use codspeed_criterion_compat::{black_box, criterion_group, criterion_main, Criterion};
use plat_smt::empty_theory::{EmptyTheory, EmptyTheoryPf};
use plat_smt::euf::{Euf, EufPf};
use plat_smt::interp_smt2;
use plat_smt::lra::{LinearArithPf, Lra};
use plat_smt::outer_solver::Logic;
use plat_smt::recorder::LoggingRecorder;
use std::fs::File;
use std::io::{read_to_string, Read};
use std::path::Path;

fn criterion_benchmark_gen<L: Logic>(c: &mut Criterion, sample: &str) {
    let path = Path::new(sample);
    let sample = read_to_string(File::open(path).unwrap()).unwrap();
    for path in sample.lines() {
        let mut data = Vec::new();
        let mut out = String::new();
        let mut err = String::new();
        File::open(path).unwrap().read_to_end(&mut data).unwrap();
        c.bench_function(path, |b| {
            b.iter(|| interp_smt2::<L>(&*data, &mut out, &mut err))
        });
        black_box((out, err));
    }
}

// TODO rename to criterion_benchmark_euf if Codspeed supports migrating benchmarks
pub fn criterion_benchmark(c: &mut Criterion) {
    criterion_benchmark_gen::<(Euf, EufPf, LoggingRecorder, _)>(c, "benches/sample_euf.txt")
}

pub fn criterion_benchmark_lra(c: &mut Criterion) {
    criterion_benchmark_gen::<(
        (EmptyTheory, Lra),
        (LinearArithPf, EmptyTheoryPf),
        LoggingRecorder,
        _,
    )>(c, "benches/sample_lra.txt")
}

criterion_group!(benches, criterion_benchmark, criterion_benchmark_lra);
criterion_main!(benches);
