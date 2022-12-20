use criterion::{criterion_group, criterion_main, Criterion};

mod normalize;

pub fn flamegraph(b: &mut Criterion) {
    normalize::normal_forms_bench(b, "flamegraph", normalize::BENCH)
}

criterion_group! {
    name = normalize;
    config = Criterion::default().with_profiler(pprof::criterion::PProfProfiler::new(100, pprof::criterion::Output::Flamegraph(None)));
    targets = flamegraph
}

criterion_main!(normalize);
