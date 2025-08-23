use codspeed_criterion_compat::{black_box, criterion_group, criterion_main, Criterion};
use plat_smt::euf::{Euf, EufPf};
use plat_smt::interp_smt2;
use plat_smt::recorder::LoggingRecorder;
use std::fs::File;
use std::io::{read_to_string, Read};
use std::path::Path;

pub fn criterion_benchmark(c: &mut Criterion) {
    // Random sample of 5% of incremental QF_UF benchmark
    let path = Path::new("benches/random_sample.txt");
    let sample = read_to_string(File::open(path).unwrap()).unwrap();
    for path in sample.lines() {
        let mut data = Vec::new();
        let mut out = String::new();
        let mut err = String::new();
        File::open(path).unwrap().read_to_end(&mut data).unwrap();
        c.bench_function(path, |b| {
            b.iter(|| interp_smt2::<(Euf, EufPf, LoggingRecorder, _)>(&*data, &mut out, &mut err))
        });
        black_box((out, err));
    }
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
