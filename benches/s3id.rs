use bls12_381::Scalar;
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use group::ff::Field;
use s3id::s3id::*;

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

    let attribute = Scalar::random(&mut rng);
    let attributes: Vec<_> = (0..big_l).map(|_| Scalar::random(&mut rng)).collect();
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
            #[allow(unused_must_use)]
            {
                black_box(dedup(&pp, &attribute, &issuers));
            }
        })
    });

    let (pp_u, prv_u) = dedup(&pp, &attribute, &issuers).expect("dedup failed");
    if n > 50 {
        c.sample_size(50);
    }
    c.bench_function("microcred", |b| {
        b.iter(|| {
            #[allow(unused_must_use)]
            {
                black_box(microcred(&attributes, &pp_u, &prv_u, &issuers, &pp));
            }
        })
    });
    if n > 50 {
        c.sample_size(100);
    }

    let signatures = microcred(&attributes, &pp_u, &prv_u, &issuers, &pp).expect("microred failed");
    c.bench_function("appcred", |b| {
        b.iter(|| {
            #[allow(unused_must_use)]
            {
                black_box(appcred(
                    &attributes,
                    &signatures,
                    &prv_u,
                    msg,
                    &attributes_subset,
                    &pp,
                ));
            }
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
            #[allow(unused_must_use)]
            {
                black_box(verifycred(&cred, &pi, msg, &pp));
            }
        });
    });
}

const NUM_ISSUERS: [usize; 3] = [4, 16, 64];
const N: [usize; 3] = [30, 40, 128];
const BIG_L: usize = 16;

fn bench_params(c: &mut Criterion) {
    for num_issuers in NUM_ISSUERS {
        for n in N {
            let t = num_issuers / 2 + 1;
            let tprime = n / 2 + 1;
            bench_s3id(c, num_issuers, n, t, tprime, BIG_L)
        }
    }
}

criterion_group!(benches, bench_params);
criterion_main!(benches);
