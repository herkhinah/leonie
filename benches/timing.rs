use criterion::{criterion_group, criterion_main, Criterion};

mod normalize;

pub fn timing(b: &mut Criterion) {
    normalize::normal_forms_bench(b, "timing", normalize::BENCH)
}

criterion_group!(normalize, timing);
criterion_main!(normalize);
