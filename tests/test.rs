use bat_egg_smt::interp_smt2;
use log::info;
use rstest::rstest;
use std::fs::{remove_file, File};
use std::io::{BufWriter, Read};
use std::path::{Path, PathBuf};

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

#[rstest]
fn test(#[files("tests/smt2/**/*.smt2")] mut file: PathBuf) {
    #[cfg(feature = "env_logger")]
    let _ = env_logger::Builder::from_env(env_logger::Env::default())
        .is_test(true)
        .try_init();
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
            &smt2_data,
            BufWriter::new(stdout_file),
            BufWriter::new(stderr_file),
        );
        remove_empty(&file);
        file.set_extension("stdout");
        remove_empty(&file);
    } else {
        file.set_extension("stdout");
        let stdout_expected = String::from_utf8(read_path(&file)).unwrap();
        file.set_extension("stderr");
        let stderr_expected = String::from_utf8(read_path(&file)).unwrap();
        let mut stdout_actual = Vec::new();
        let mut stderr_actual = Vec::new();
        interp_smt2(&smt2_data, &mut stdout_actual, &mut stderr_actual);
        assert_eq!(String::from_utf8(stdout_actual).unwrap(), stdout_expected);
        assert_eq!(String::from_utf8(stderr_actual).unwrap(), stderr_expected);
    }
}
