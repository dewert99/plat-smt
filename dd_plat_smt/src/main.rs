mod elim_nodes;
mod padded;
mod remove_unused;
mod replace_by_child;
mod use_mutator;

use crate::elim_nodes::ElimNodes;
use crate::padded::Padded;
use crate::remove_unused::remove_unused;
use crate::replace_by_child::ReplaceByChild;
use crate::use_mutator::{Mutator, use_mutator};
use std::io::{StdoutLock, Write, stdout};
use std::path::PathBuf;
use std::process::Command;
use std::time::{Duration, Instant};
use std::{env, fs};
use tempfile::NamedTempFile;

fn main() {
    let mut args = env::args();
    let _ = args.next().unwrap();
    let in_file = args.next().unwrap();
    let out_file = args.next().unwrap();
    let command = args.next().unwrap();
    let data = fs::read_to_string(&in_file).unwrap();
    let mut checker = Checker::new(data, out_file, command);
    let mut cursor = Vec::new();
    let mut stdout = stdout().lock();
    loop {
        let len = checker.data.len();
        reduce::<ElimNodes>(&mut checker, &mut cursor, &mut stdout);
        reduce::<ReplaceByChild>(&mut checker, &mut cursor, &mut stdout);
        if checker.data.len() == len {
            break;
        }
    }
}

fn reduce<M: Mutator>(checker: &mut Checker, mut cursor: &mut Vec<u32>, stdout: &mut StdoutLock) {
    let mut mutator = M::from_data(&checker.data);
    checker.check(remove_unused);
    let mut skip_first = false;
    loop {
        write!(
            stdout,
            "\rlen: {:10}, cursor: {:?} {:?}, self_time: {:?}, command_time: {:?}",
            checker.data.len(),
            Padded(&cursor, 30),
            Padded(&mutator, 15),
            Padded(checker.self_time, 15),
            Padded(checker.command_time, 15)
        )
        .unwrap();
        stdout.flush().unwrap();
        skip_first = !checker
            .check(|data, out| use_mutator(data, out, &mut cursor, skip_first, &mut mutator));
        if cursor.is_empty() {
            break;
        }
    }
}

struct Checker {
    data: String,
    buf: String,
    tmp_file: NamedTempFile,
    out_file: PathBuf,
    command: String,
    golden_out: Vec<u8>,
    last_timestamp: Instant,
    self_time: Duration,
    command_time: Duration,
}

impl Checker {
    fn new(data: String, out_file: String, command: String) -> Checker {
        let tmp_file = NamedTempFile::new().unwrap();
        fs::write(tmp_file.path(), &data).unwrap();
        let golden_out = Command::new(&command)
            .arg(tmp_file.path())
            .output()
            .unwrap()
            .stdout;
        println!("Golden output:\n{}", String::from_utf8_lossy(&golden_out));
        Checker {
            data,
            buf: String::new(),
            tmp_file,
            out_file: out_file.into(),
            command,
            golden_out,
            last_timestamp: Instant::now(),
            self_time: Duration::ZERO,
            command_time: Duration::ZERO,
        }
    }

    fn take_time_window(&mut self) -> Duration {
        let now = Instant::now();
        let res = now.duration_since(self.last_timestamp);
        self.last_timestamp = now;
        res
    }

    fn check(&mut self, mutator: impl FnOnce(&str, &mut String)) -> bool {
        self.buf.clear();
        mutator(&self.data, &mut self.buf);
        fs::write(self.tmp_file.path(), &self.buf).unwrap();
        let self_time = self.take_time_window();
        self.self_time += self_time;
        let out = Command::new(&self.command)
            .arg(self.tmp_file.path())
            .output()
            .unwrap()
            .stdout;
        let command_time = self.take_time_window();
        self.command_time += command_time;
        if out == self.golden_out {
            fs::write(&self.out_file, &self.buf).unwrap();
            self.data.clone_from(&self.buf);
            true
        } else {
            false
        }
    }
}
