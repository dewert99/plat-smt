use log::info;
use plat_smt::empty_theory::{EmptyTheory, EmptyTheoryPf};
use plat_smt::euf::{Euf, EufPf};
use plat_smt::interp_smt2;
use plat_smt::outer_solver::Logic;
use plat_smt::recorder::LoggingRecorder;
use rstest::rstest;
use std::any::type_name;
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

fn test_file<L: Logic>(mut file: PathBuf) {
    init_logger();
    info!("Starting test {:?} using {}", file, type_name::<Euf>());
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
        interp_smt2::<L>(
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
        interp_smt2::<L>(&*smt2_data, &mut stdout_actual, &mut stderr_actual);
        assert_eq!(stderr_actual, stderr_expected);
        assert_eq!(stdout_actual, stdout_expected);
    }
}

#[rstest]
fn test_euf(#[files("tests/smt2/**/*.smt2")] file: PathBuf) {
    test_file::<(Euf, EufPf, LoggingRecorder, _)>(file)
}

#[rstest]
fn test_no_euf(#[files("tests/smt2/no_euf/**/*.smt2")] file: PathBuf) {
    test_file::<(EmptyTheory, EmptyTheoryPf, LoggingRecorder, _)>(file)
}

fn test_sequential(init_command: &str, split_command: &str, exact: bool) {
    init_logger();
    let mut out = String::new();
    let mut err = String::new();
    let mut expect_out = Vec::new();
    let mut file_buf = Vec::new();
    file_buf.extend_from_slice(init_command.as_bytes());
    let path = Path::new("tests/smt2");
    let mut paths: Vec<_> = path
        .read_dir()
        .unwrap()
        .filter_map(|x| {
            let path = x.ok()?.path();
            if path.extension() == Some("smt2".as_ref()) {
                Some(path)
            } else {
                None
            }
        })
        .collect();
    paths.sort_unstable();
    for mut path in paths {
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
    interp_smt2::<(Euf, EufPf, LoggingRecorder, _)>(&*file_buf, &mut out, &mut err);
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
mod test_smtlib_benchmarks {
    use super::*;
    use std::io::{stderr, Seek, Write};
    use std::process::{Command, Stdio};
    use walkdir::WalkDir;

    #[test]
    fn test_incremental() {
        let mut out = String::new();
        let mut err = String::new();
        let mut file_buf = Vec::new();
        if let Ok(x) = std::env::var("SEED") {
            writeln!(file_buf, "(set-option :sat.random_seed {x})").unwrap();
            writeln!(file_buf, "(set-option :sat.rnd_init_act true)").unwrap();
        }
        let base_len = file_buf.len();
        let path = Path::new("benches/starexec/incremental");
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
                interp_smt2::<(Euf, EufPf, LoggingRecorder, _)>(&*file_buf, &mut out, &mut err);
                let yices_out = yices_child.wait_with_output().unwrap();
                assert_eq!(&err, "");
                assert_eq!(&out, from_utf8(&yices_out.stdout).unwrap());
                file_buf.truncate(base_len);
                out.clear();
            }
        }
    }

    #[test]
    fn test_model_unsat_core() {
        let mut out = String::new();
        let mut err = String::new();
        let mut file_buf = Vec::new();
        if let Ok(x) = std::env::var("SEED") {
            writeln!(file_buf, "(set-option :sat.random_seed {x})").unwrap();
            writeln!(file_buf, "(set-option :sat.rnd_init_act true)").unwrap();
        }
        let base_len = file_buf.len();
        let path = Path::new("benches/starexec/non-incremental/QF_UF/2018-Goel-hwbench");
        for x in WalkDir::new(path).into_iter().filter_map(Result::ok) {
            let path = x.path();
            if path.extension() == Some("smt2".as_ref()) {
                use std::io::Write;
                writeln!(stderr(), "Testing file {:?}", path).unwrap();
                let mut base_file = File::open(&path).unwrap();
                base_file.read_to_end(&mut file_buf).unwrap();
                base_file.rewind().unwrap();
                let mut scrambled_file = File::create("tmp.smt2").unwrap();
                let mut output_file = File::create("tmp.rsmt2").unwrap();
                interp_smt2::<(Euf, EufPf, LoggingRecorder, _)>(&*file_buf, &mut out, &mut err);
                assert_eq!(&err, "");
                file_buf.truncate(base_len);
                match &*out {
                    "sat\n" => {
                        let scrambler_out = Command::new("./scrambler")
                            .args(["-gen-model-val", "true"])
                            .stdin(base_file)
                            .output()
                            .unwrap();
                        assert!(scrambler_out.stderr.is_empty() && scrambler_out.status.success());
                        let scrambled = scrambler_out.stdout;
                        out.clear();
                        interp_smt2::<(Euf, EufPf, LoggingRecorder, _)>(
                            &*scrambled,
                            &mut out,
                            &mut err,
                        );
                        assert_eq!(&err, "");
                        scrambled_file.write_all(&*scrambled).unwrap();
                        drop(scrambled_file);
                        output_file.write_all(out.as_bytes()).unwrap();
                        out.clear();
                        let validator_out = Command::new("./dolmen")
                            .args(["--check-model=true", "-r", "tmp.rsmt2", "tmp.smt2"])
                            .output()
                            .unwrap();
                        if !validator_out.status.success() {
                            std::io::stderr().write(&validator_out.stderr).unwrap();
                            panic!();
                        }
                    }
                    "unsat\n" => {
                        let scrambler_out = Command::new("./scrambler")
                            .args(["-gen-unsat-core", "true"])
                            .stdin(base_file)
                            .output()
                            .unwrap();
                        assert!(scrambler_out.stderr.is_empty() && scrambler_out.status.success());
                        let scrambled = scrambler_out.stdout;
                        out.clear();
                        interp_smt2::<(Euf, EufPf, LoggingRecorder, _)>(
                            &*scrambled,
                            &mut out,
                            &mut err,
                        );
                        assert_eq!(&err, "");
                        scrambled_file.write_all(&*scrambled).unwrap();
                        drop(scrambled_file);
                        output_file.write_all(out.as_bytes()).unwrap();
                        out.clear();
                        let scrambled_file = File::open("tmp.smt2").unwrap(); // open in read mode
                        let mut cored_child = Command::new("./scrambler")
                            .args(["-seed", "0", "-core", "tmp.rsmt2"])
                            .stdin(scrambled_file)
                            .stdout(Stdio::piped())
                            .spawn()
                            .unwrap();
                        let yices_out = Command::new("./yices-smt2")
                            .stdin(cored_child.stdout.take().unwrap())
                            .output()
                            .unwrap();
                        assert_eq!(String::from_utf8_lossy(&yices_out.stdout), "unsat\n");
                        assert_eq!(String::from_utf8_lossy(&yices_out.stderr), "");
                        cored_child.wait().unwrap();
                    }
                    _ => panic!("unexpected output:\n{out}"),
                }
            }
        }
    }
}
