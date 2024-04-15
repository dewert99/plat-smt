use bat_egg_smt::interp_smt2;
use log::info;
use rstest::rstest;
use std::fs::{remove_file, File};
use std::io::{BufWriter, Read};
use std::path::{Path, PathBuf};
use std::str::from_utf8;

fn read_path(p: &Path) -> Vec<u8> {
    let mut res = Vec::new();
    if let Ok(mut f) = File::open(p) {
        f.read_to_end(&mut res).unwrap();
    }
    res
}

fn remove_empty(file: &Path) {
    if file.metadata().unwrap().len() == 0 {
        remove_file(file).unwrap()
    }
}

fn init_logger() {
    #[cfg(feature = "env_logger")]
    let _ = env_logger::Builder::from_env(env_logger::Env::default())
        .is_test(true)
        .try_init();
}

struct WrapWrite<W>(W);

impl<W: std::io::Write> std::fmt::Write for WrapWrite<W> {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        self.0.write_all(s.as_bytes()).map_err(|_| std::fmt::Error)
    }
}

#[rstest]
fn test(#[files("tests/smt2/**/*.smt2")] mut file: PathBuf) {
    init_logger();
    info!("Starting test {:?}", file);
    let bless = std::env::var("BLESS").as_deref() == Ok("true");
    if bless {
        println!("BLESS")
    }
    let smt2_data = read_path(&file);
    if bless {
        file.set_extension("stdout");
        let stdout_file = File::create(&file).unwrap();
        file.set_extension("stderr");
        let stderr_file = File::create(&file).unwrap();
        interp_smt2(
            &*smt2_data,
            WrapWrite(BufWriter::new(stdout_file)),
            WrapWrite(BufWriter::new(stderr_file)),
        );
        remove_empty(&file);
        file.set_extension("stdout");
        remove_empty(&file);
    } else {
        file.set_extension("stdout");
        let stdout_expected = String::from_utf8(read_path(&file)).unwrap();
        file.set_extension("stderr");
        let stderr_expected = String::from_utf8(read_path(&file)).unwrap();
        let mut stdout_actual = String::new();
        let mut stderr_actual = String::new();
        interp_smt2(&*smt2_data, &mut stdout_actual, &mut stderr_actual);
        assert_eq!(stderr_actual, stderr_expected);
        assert_eq!(stdout_actual, stdout_expected);
    }
}

fn test_sequential(init_command: &str, split_command: &str, exact: bool) {
    init_logger();
    let mut out = String::new();
    let mut err = String::new();
    let mut expect_out = Vec::new();
    let mut file_buf = Vec::new();
    file_buf.extend_from_slice(init_command.as_bytes());
    let path = Path::new("tests/smt2");
    for x in path.read_dir().unwrap().filter_map(Result::ok) {
        let mut path = x.path();
        if path.extension() == Some("smt2".as_ref()) {
            info!("Adding file {:?}", path);
            File::open(&path)
                .unwrap()
                .read_to_end(&mut file_buf)
                .unwrap();
            file_buf.extend_from_slice(split_command.as_bytes());
            path.set_extension("stdout");
            File::open(&path)
                .unwrap()
                .read_to_end(&mut expect_out)
                .unwrap();
        }
    }
    interp_smt2(&*file_buf, &mut out, &mut err);
    assert_eq!(&err, "");
    if exact {
        assert_eq!(&out, from_utf8(&expect_out).unwrap());
    }
}

#[test]
fn test_sequential_pop_clear() {
    test_sequential("", "(pop)", true)
}

#[test]
fn test_sequential_reset_clear() {
    test_sequential("", "(reset)", true)
}

#[test]
fn test_sequential_push_pop() {
    test_sequential("(push)", "(pop) (push)", true)
}

#[cfg(not(debug_assertions))]
#[test]
fn test_smtlib_benchmarks() {
    use std::io::{stderr, Write};
    use std::process::{Command, Stdio};
    use walkdir::WalkDir;

    let mut out = String::new();
    let mut err = String::new();
    let mut file_buf = Vec::new();
    if let Ok(x) = std::env::var("SEED") {
        writeln!(file_buf, "(set-option :sat.random_seed {x})").unwrap();
        writeln!(file_buf, "(set-option :sat.rnd_init_act true)").unwrap();
    }
    let base_len = file_buf.len();
    let path = Path::new("benches/starexec");
    for x in WalkDir::new(path).into_iter().filter_map(Result::ok) {
        let path = x.path();
        if path.extension() == Some("smt2".as_ref()) {
            use std::io::Write;
            writeln!(stderr(), "Testing file {:?}", path).unwrap();
            let yices_child = Command::new("./yices-smt2")
                .arg("--incremental")
                .arg(path)
                .stdout(Stdio::piped())
                .spawn()
                .unwrap();
            File::open(&path)
                .unwrap()
                .read_to_end(&mut file_buf)
                .unwrap();
            interp_smt2(&*file_buf, &mut out, &mut err);
            let yices_out = yices_child.wait_with_output().unwrap();
            assert_eq!(&err, "");
            assert_eq!(&out, from_utf8(&yices_out.stdout).unwrap());
            file_buf.truncate(base_len);
            out.clear();
        }
    }
}
