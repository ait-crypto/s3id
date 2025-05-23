use ark_ff::UniformRand;
use criterion::{Criterion, black_box, criterion_group, criterion_main};
use s3id::{Scalar, atact::*};

fn bench_atact(c: &mut Criterion, num_issuers: usize, n: usize, t: usize, tprime: usize) {
    let mut c = c.benchmark_group(format!("(N, n, t, t') = {:?}", (num_issuers, n, t, tprime)));

    let mut rng = rand::thread_rng();
    let a = Scalar::rand(&mut rng);

    let (pp, issuers) = setup(num_issuers, n, t, tprime, 1).expect("setup failed");

    c.bench_function("register", |b| {
        b.iter(|| {
            black_box(register(&a, &pp)).unwrap();
        })
    });

    let (strg, cm) = register(&a, &pp).expect("register failed");
    if n > 50 {
        c.sample_size(50);
    }
    c.bench_function("token_request", |b| {
        b.iter(|| {
            black_box(token_request(&strg, &cm, &pp)).unwrap();
        })
    });
    if n > 50 {
        c.sample_size(100);
    }

    let (blind_request, rand) = token_request(&strg, &cm, &pp).expect("token request failed");
    c.bench_function("tissue", |b| {
        b.iter(|| {
            black_box(tissue(&blind_request, &issuers[0], &pp)).unwrap();
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
            black_box(verify(&token, &token_proof, &blind_request, &pp)).unwrap();
        });
    });
}

const NUM_ISSUERS: [usize; 3] = [4, 16, 64];
const N: [usize; 3] = [30, 40, 128];

fn bench_params(c: &mut Criterion) {
    for num_issuers in NUM_ISSUERS {
        for n in N {
            let t = num_issuers / 2 + 1;
            let tprime = n / 2 + 1;
            bench_atact(c, num_issuers, n, t, tprime);
        }
    }
}

criterion_group!(benches, bench_params);
criterion_main!(benches);
