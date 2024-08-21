use ark_ff::UniformRand;
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use rand::{distributions::Uniform, Rng};
use s3id::{s3id::*, Scalar};

fn bench_s3id(
    c: &mut Criterion,
    num_issuers: usize,
    n: usize,
    t: usize,
    tprime: usize,
    big_l: usize,
) {
    let mut c = c.benchmark_group(format!(
        "(N, n, t, t', L) = {:?}",
        (num_issuers, n, t, tprime, big_l)
    ));

    let mut rng = rand::thread_rng();

    let attribute = Scalar::rand(&mut rng);
    let attributes: Vec<_> = (0..big_l).map(|_| Scalar::rand(&mut rng)).collect();
    let attributes_subset: Vec<_> = (0..big_l)
        .filter_map(|idx| {
            if idx % 2 == 0 {
                Some(attributes[idx])
            } else {
                None
            }
        })
        .collect();

    let msg = b"some message";

    let (pp, issuers) = setup(num_issuers, t, n, tprime, big_l).expect("setup failed");
    c.bench_function("dedup", |b| {
        b.iter(|| {
            black_box(dedup(&pp, &attribute, &issuers)).unwrap();
        })
    });

    let (pp_u, prv_u) = dedup(&pp, &attribute, &issuers).expect("dedup failed");
    if n > 50 {
        c.sample_size(50);
    }
    c.bench_function("microcred", |b| {
        b.iter(|| {
            black_box(microcred(&attributes, &pp_u, &prv_u, &issuers, &pp)).unwrap();
        })
    });
    if n > 50 {
        c.sample_size(100);
    }

    let signatures = microcred(&attributes, &pp_u, &prv_u, &issuers, &pp).expect("microred failed");
    c.bench_function("appcred", |b| {
        b.iter(|| {
            black_box(appcred(
                &attributes,
                &signatures,
                &prv_u,
                msg,
                &attributes_subset,
                &pp,
            ))
            .unwrap();
        });
    });

    let (cred, pi) = appcred(
        &attributes,
        &signatures,
        &prv_u,
        msg,
        &attributes_subset,
        &pp,
    )
    .expect("appcred failed");
    c.bench_function("verifycred", |b| {
        b.iter(|| {
            black_box(verifycred(&cred, &pi, msg, &pp)).unwrap();
        });
    });
}

fn bench_s3id_attibute_sizes(
    c: &mut Criterion,
    num_issuers: usize,
    n: usize,
    t: usize,
    tprime: usize,
    small_l: usize,
    big_l: usize,
) {
    let mut c = c.benchmark_group(format!(
        "(N, n, t, t', l, L) = {:?}",
        (num_issuers, n, t, tprime, small_l, big_l)
    ));

    let mut rng = rand::thread_rng();

    let mut indices = vec![];
    let distribution = Uniform::new(0, big_l - 1);
    while indices.len() < small_l {
        let sample = rng.sample(distribution);
        if !indices.iter().any(|v| *v == sample) {
            indices.push(sample);
        }
    }

    let attribute = Scalar::rand(&mut rng);
    let attributes: Vec<_> = (0..big_l).map(|_| Scalar::rand(&mut rng)).collect();
    let attributes_subset: Vec<_> = indices.into_iter().map(|idx| attributes[idx]).collect();

    let msg = b"some message";

    let (pp, issuers) = setup(num_issuers, t, n, tprime, big_l).expect("setup failed");
    let (pp_u, prv_u) = dedup(&pp, &attribute, &issuers).expect("dedup failed");
    if n > 50 {
        c.sample_size(50);
    }
    c.bench_function("microcred", |b| {
        b.iter(|| {
            black_box(microcred(&attributes, &pp_u, &prv_u, &issuers, &pp)).unwrap();
        })
    });
    if n > 50 {
        c.sample_size(100);
    }

    let signatures = microcred(&attributes, &pp_u, &prv_u, &issuers, &pp).expect("microred failed");
    c.bench_function("appcred", |b| {
        b.iter(|| {
            black_box(appcred(
                &attributes,
                &signatures,
                &prv_u,
                msg,
                &attributes_subset,
                &pp,
            ))
            .unwrap();
        });
    });

    let (cred, pi) = appcred(
        &attributes,
        &signatures,
        &prv_u,
        msg,
        &attributes_subset,
        &pp,
    )
    .expect("appcred failed");
    c.bench_function("verifycred", |b| {
        b.iter(|| {
            black_box(verifycred(&cred, &pi, msg, &pp)).unwrap();
        });
    });
}

const NUM_ISSUERS: [usize; 3] = [4, 16, 64];
const NS: [usize; 3] = [30, 40, 128];
const BIG_LS: [usize; 3] = [16, 32, 64];
const BIG_L: usize = BIG_LS[0];

fn bench_params(c: &mut Criterion) {
    for num_issuers in NUM_ISSUERS {
        for n in NS {
            let t = num_issuers / 2 + 1;
            let tprime = n / 2 + 1;
            bench_s3id(c, num_issuers, n, t, tprime, BIG_L);
        }
    }
}

fn bench_attribute_sizes(c: &mut Criterion) {
    const ISSUERS: usize = NUM_ISSUERS[0];
    const N: usize = NS[0];
    const T: usize = ISSUERS / 2 + 1;
    const TPRIME: usize = N / 2 + 1;
    for big_l in BIG_LS {
        for div in [2, 4, 8] {
            let small_l = big_l / div;
            bench_s3id_attibute_sizes(c, ISSUERS, N, T, TPRIME, small_l, big_l);
        }
    }
}

criterion_group!(benches, bench_params, bench_attribute_sizes);
criterion_main!(benches);
