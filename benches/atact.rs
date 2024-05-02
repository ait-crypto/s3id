use bls12_381::Scalar;
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use group::ff::Field;
use s3id::atact::*;

fn bench_atact(
    c: &mut Criterion,
    num_attributes: usize,
    num_issuers: usize,
    n: usize,
    t: usize,
    tprime: usize,
) {
    let mut c = c.benchmark_group(format!("(N, n, t, t') = {:?}", (num_issuers, n, t, tprime)));

    let mut rng = rand::thread_rng();
    let attributes: Vec<_> = (0..num_attributes)
        .map(|_| Scalar::random(&mut rng))
        .collect();
    let a = attributes[0];

    let (pp, issuers) = setup(num_issuers, n, t, tprime, &attributes).expect("setup failed");

    c.bench_function("register", |b| {
        b.iter(|| {
            #[allow(unused_must_use)]
            {
                black_box(register(&a, &pp));
            }
        })
    });

    let (strg, cm) = register(&a, &pp).expect("register failed");
    if n > 50 {
        c.sample_size(50);
    }
    c.bench_function("token_request", |b| {
        b.iter(|| {
            #[allow(unused_must_use)]
            {
                black_box(token_request(&strg, &cm, &pp));
            }
        })
    });
    if n > 50 {
        c.sample_size(100);
    }

    let (blind_request, rand) = token_request(&strg, &cm, &pp).expect("token request failed");
    c.bench_function("tissue", |b| {
        b.iter(|| {
            #[allow(unused_must_use)]
            {
                black_box(tissue(&blind_request, &issuers[0], &pp));
            }
        });
    });

    let blind_tokens = issuers
        .iter()
        .map(|issuer| tissue(&blind_request, issuer, &pp).expect("tissue failed"))
        .collect();
    c.bench_function("aggregate/unblind", |b| {
        b.iter(|| {
            black_box(aggregate_unblind(&blind_tokens, &rand, &pp));
        });
    });

    let token = aggregate_unblind(&blind_tokens, &rand, &pp);
    c.bench_function("proof", |b| {
        b.iter(|| {
            black_box(prove(&token, &rand, &pp));
        });
    });

    let token_proof = prove(&token, &rand, &pp);
    c.bench_function("verify", |b| {
        b.iter(|| {
            #[allow(unused_must_use)]
            {
                black_box(verify(&token, &token_proof, &blind_request, &pp));
            }
        });
    });
}

const NUM_ISSUERS: [usize; 3] = [4, 16, 64];
const N: [usize; 3] = [30, 40, 128];
const NUM_ATTRIBUTES: usize = 10;

fn bench_params(c: &mut Criterion) {
    for num_issuers in NUM_ISSUERS {
        for n in N {
            let t = num_issuers / 2 + 1;
            let tprime = n / 2 + 1;
            bench_atact(c, NUM_ATTRIBUTES, num_issuers, n, t, tprime)
        }
    }
}

criterion_group!(benches, bench_params);
criterion_main!(benches);
