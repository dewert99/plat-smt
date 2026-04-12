use log::info;
use plat_smt::empty_theory::{EmptyTheory, EmptyTheoryPf};
use plat_smt::euf::{Euf, EufPf};
use plat_smt::interp_smt2;
use plat_smt::outer_solver::Logic;
use plat_smt::recorder::InterpolantRecorder;
use rstest::rstest;
use std::any::type_name;
use std::fs::{remove_file, File, ReadDir};
use std::io::{BufWriter, Read};
use std::path::{Path, PathBuf};
use std::str::from_utf8;

fn read_path_into(path: &mut PathBuf, extension: &str, dst: &mut Vec<u8>) {
    #[cfg(feature = "test_add_more_mid_search_equalities")]
    {
        path.set_extension(format!("mid_search_eq_{extension}"));
        if let Ok(mut f) = File::open(&path) {
            f.read_to_end(dst).unwrap();
            return;
        }
    }
    path.set_extension(extension);
    if let Ok(mut f) = File::open(&path) {
        f.read_to_end(dst).unwrap();
    }
}

fn read_path(path: &mut PathBuf, extension: &str) -> Vec<u8> {
    let mut res = Vec::new();
    read_path_into(path, extension, &mut res);
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
    let smt2_data = read_path(&mut file, "smt2");
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
        let stdout_expected = String::from_utf8(read_path(&mut file, "stdout")).unwrap();
        let stderr_expected = String::from_utf8(read_path(&mut file, "stderr")).unwrap();
        let mut stdout_actual = String::new();
        let mut stderr_actual = String::new();
        interp_smt2::<L>(&*smt2_data, &mut stdout_actual, &mut stderr_actual);
        assert_eq!(stderr_actual, stderr_expected);
        assert_eq!(stdout_actual, stdout_expected);
    }
}

#[rstest]
fn test_euf(#[files("tests/smt2/**/*.smt2")] file: PathBuf) {
    test_file::<(Euf, EufPf, InterpolantRecorder, _)>(file)
}

#[rstest]
fn test_no_euf(#[files("tests/smt2/no_euf/**/*.smt2")] file: PathBuf) {
    test_file::<(EmptyTheory, EmptyTheoryPf, InterpolantRecorder, _)>(file)
}

fn iter_direct(path: &str) -> ReadDir {
    Path::new(path).read_dir().unwrap()
}

fn test_sequential(init_command: &str, split_command: &str, exact: bool) {
    init_logger();
    let mut out = String::new();
    let mut err = String::new();
    let mut expect_out = Vec::new();
    let mut file_buf = Vec::new();
    file_buf.extend_from_slice(init_command.as_bytes());
    let mut paths: Vec<_> = iter_direct("tests/smt2")
        .chain(iter_direct("tests/smt2/no_euf"))
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
        read_path_into(&mut path, "smt2", &mut file_buf);
        file_buf.extend_from_slice(split_command.as_bytes());
        path.set_extension("stdout");
        read_path_into(&mut path, "stdout", &mut expect_out);
    }
    interp_smt2::<(Euf, EufPf, InterpolantRecorder, _)>(&*file_buf, &mut out, &mut err);
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
    use plat_smt::recorder::LoggingRecorder;
    use plat_smt::IncrementalParser;
    use std::env;
    use std::fmt::Display;
    use std::io::{stderr, Seek, Write};
    use std::process::{Command, Stdio};
    use walkdir::WalkDir;

    fn take_suffix(s: &mut String, suffix: &str) {
        let new_len = s.len() - suffix.len();
        assert_eq!(&s[new_len..], suffix);
        s.truncate(new_len);
    }

    fn write_fmt(s: &mut String, x: impl Display) {
        std::fmt::Write::write_fmt(s, format_args!("{x}")).unwrap()
    }

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

    const ASSUMP_NAME: &str = "smtcomp";

    #[test]
    fn test_model_unsat_core() {
        let mut incr = IncrementalParser::<(Euf, EufPf, InterpolantRecorder, _)>::default();
        let mut interp_a = String::new();
        let mut interp_b = String::new();
        let mut yices_in = String::new();
        let mut file_buf = Vec::new();
        let scramble_seed = env::var("SCRAMBLE_SEED").unwrap_or("0".to_owned());
        if let Ok(x) = env::var("SEED") {
            writeln!(file_buf, "(set-option :sat.random_seed {x})").unwrap();
            writeln!(file_buf, "(set-option :sat.rnd_init_act true)").unwrap();
        }
        let base_len = file_buf.len();
        let path = Path::new("benches/starexec/non-incremental/QF_UF/2018-Goel-hwbench");
        for x in WalkDir::new(path).into_iter().filter_map(Result::ok) {
            let path = x.path();
            if path.extension() == Some("smt2".as_ref()) {
                use std::io::Write;
                let mut base_file = File::open(&path).unwrap();
                base_file.read_to_end(&mut file_buf).unwrap();
                base_file.rewind().unwrap();
                let mut scrambled_file = File::create("tmp.smt2").unwrap();
                let mut output_file = File::create("tmp.rsmt2").unwrap();
                write!(stderr(), "Testing file {path:?}").unwrap();
                incr.clear();
                incr.interp_smt2_commands(str::from_utf8(&*file_buf).unwrap());
                assert_eq!(incr.err(), "");
                file_buf.truncate(base_len);
                write!(stderr(), ": {}", incr.out()).unwrap();
                match incr.out() {
                    "sat\n" => {
                        let scrambler_out = Command::new("./scrambler")
                            .args(["-gen-model-val", "true", "-seed", &scramble_seed])
                            .stdin(base_file)
                            .output()
                            .unwrap();
                        assert!(scrambler_out.stderr.is_empty() && scrambler_out.status.success());
                        let scrambled = scrambler_out.stdout;
                        incr.clear();
                        incr.interp_smt2_commands(str::from_utf8(&*scrambled).unwrap());
                        assert_eq!(incr.err(), "");
                        scrambled_file.write_all(&*scrambled).unwrap();
                        drop(scrambled_file);
                        output_file.write_all(incr.out().as_bytes()).unwrap();
                        let validator_out = Command::new("./dolmen")
                            .args(["--check-model=true", "-r", "tmp.rsmt2", "tmp.smt2"])
                            .output()
                            .unwrap();
                        if !validator_out.status.success() {
                            stderr().write(&validator_out.stderr).unwrap();
                            panic!();
                        }
                    }
                    "unsat\n" => {
                        let scrambler_out = Command::new("./scrambler")
                            .args(["-gen-unsat-core", "true", "-seed", &scramble_seed])
                            .stdin(base_file)
                            .output()
                            .unwrap();
                        assert!(scrambler_out.stderr.is_empty() && scrambler_out.status.success());
                        let mut scrambled = String::from_utf8(scrambler_out.stdout).unwrap();
                        take_suffix(&mut scrambled, "(exit)\n");
                        incr.clear();
                        incr.interp_smt2_commands(&scrambled);
                        assert_eq!(incr.err(), "");
                        assert_eq!(&incr.out()[..7], "unsat\n(");
                        assert_eq!(&incr.out()[incr.out().len() - 2..], ")\n");
                        let unsat_core_range = 7..incr.out().len() - 2;
                        take_suffix(&mut scrambled, "(get-unsat-core)\n");
                        take_suffix(&mut scrambled, "(check-sat)\n");
                        let start_idx = scrambled.rfind(ASSUMP_NAME).unwrap() + ASSUMP_NAME.len();
                        let end_idx = start_idx + scrambled[start_idx..].find(")").unwrap();

                        let last_assump_idx: u32 = scrambled[start_idx..end_idx].parse().unwrap();
                        interp_a.clear();
                        interp_b.clear();
                        for i in 1..=last_assump_idx {
                            if i & 4 > 0 {
                                write_fmt(&mut interp_a, format_args!("{ASSUMP_NAME}{i} "));
                            } else {
                                write_fmt(&mut interp_b, format_args!("{ASSUMP_NAME}{i} "));
                            }
                        }
                        let old_len = incr.out().len();
                        incr.interp_smt2_commands(format_args!(
                            "(get-interpolants (and {interp_a}) (and {interp_b}))"
                        ));
                        assert_eq!(incr.err(), "");
                        let interpolant = &incr.out()[old_len..];
                        let unsat_core = &incr.out()[unsat_core_range];
                        yices_in.clear();
                        let mut i = 1;
                        for line in scrambled.lines() {
                            if let Some(rest) = line.strip_prefix("(assert (! ") {
                                let exp = &rest[..rest.find(":named").unwrap()];
                                write_fmt(
                                    &mut yices_in,
                                    format_args!("(define-fun {ASSUMP_NAME}{i} () Bool {exp})\n"),
                                );
                                i += 1;
                            } else if !line.starts_with("(set-option") {
                                write_fmt(&mut yices_in, format_args!("{line}\n"));
                            }
                        }
                        write_fmt(
                            &mut yices_in,
                            format_args!("(define-fun interpolant () Bool {interpolant})\n"),
                        );
                        write_fmt(
                            &mut yices_in,
                            format_args!("(check-sat-assuming ({unsat_core}))\n"),
                        );
                        write_fmt(
                            &mut yices_in,
                            format_args!("(check-sat-assuming ({interp_a}(not interpolant)))\n"),
                        );
                        write_fmt(
                            &mut yices_in,
                            format_args!("(check-sat-assuming ({interp_b} interpolant))\n"),
                        );
                        scrambled_file.write_all(yices_in.as_bytes()).unwrap();
                        let yices_out = Command::new("./yices-smt2")
                            .args(["--incremental", "tmp.smt2"])
                            .output()
                            .unwrap();
                        assert_eq!(String::from_utf8_lossy(&yices_out.stderr), "");
                        assert_eq!(
                            String::from_utf8_lossy(&yices_out.stdout),
                            "unsat\nunsat\nunsat\n"
                        );
                    }
                    _ => panic!("unexpected output:\n{}", incr.out()),
                }
            }
        }
    }
}
