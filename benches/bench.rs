use bat_egg_smt::interp_smt2;
use codspeed_criterion_compat::{black_box, criterion_group, criterion_main, Criterion};
use std::fs::File;
use std::io::Read;
use std::path::Path;
pub fn criterion_benchmark(c: &mut Criterion) {
    use walkdir::WalkDir;

    let path = Path::new("benches/starexec");
    for x in WalkDir::new(path).into_iter().filter_map(Result::ok) {
        let path = x.path();
        if path.extension() == Some("smt2".as_ref()) {
            let mut data = Vec::new();
            let mut out = Vec::new();
            let mut err = Vec::new();
            File::open(path).unwrap().read_to_end(&mut data).unwrap();
            c.bench_function(path.as_os_str().to_str().unwrap(), |b| {
                b.iter(|| interp_smt2(&data, &mut out, &mut err))
            });
            black_box((out, err));
        }
    }
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
