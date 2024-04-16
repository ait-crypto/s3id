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
    let mut rng = rand::thread_rng();
    let attributes: Vec<_> = (0..num_attributes)
        .map(|_| Scalar::random(&mut rng))
        .collect();
    let a = attributes[0];

    let (pp, issuers) = setup(num_issuers, n, t, tprime, &attributes);

    c.bench_function(
        &format!("token_request {:?}", (num_issuers, n, t, tprime)),
        |b| {
            b.iter(|| {
                let (blind_request, rand) = token_request(a, &pp).expect("token request failed");
                black_box(blind_request);
                black_box(rand);
            })
        },
    );

    let (blind_request, rand) = token_request(a, &pp).expect("token request failed");
    c.bench_function(&format!("tissue {:?}", (num_issuers, n, t, tprime)), |b| {
        b.iter(|| {
            let blind_token = tissue(&blind_request, &issuers[0], &pp).expect("tissue failed");
            black_box(blind_token);
        });
    });

    let mut blind_tokens = vec![];
    for issuer in &issuers {
        let blind_token = tissue(&blind_request, issuer, &pp).expect("tissue failed");
        blind_tokens.push(blind_token);
    }

    c.bench_function(
        &format!("aggregate/unblind {:?}", (num_issuers, n, t, tprime)),
        |b| {
            b.iter(|| {
                let token = aggregate_unblind(&blind_tokens, &rand, &pp);
                black_box(token);
            });
        },
    );

    let token = aggregate_unblind(&blind_tokens, &rand, &pp);
    c.bench_function(&format!("proof {:?}", (num_issuers, n, t, tprime)), |b| {
        b.iter(|| {
            let token_proof = prove(&token, &rand, &pp);
            black_box(token_proof);
        });
    });

    let token_proof = prove(&token, &rand, &pp);
    c.bench_function(&format!("verify {:?}", (num_issuers, n, t, tprime)), |b| {
        b.iter(|| {
            #[allow(unused_must_use)]
            {
                black_box(verify(&token, &token_proof, &blind_request, &pp));
            }
        });
    });
}

fn bench_params_1(c: &mut Criterion) {
    const NUM_ISSUERS: usize = 50;
    const N: usize = 40;
    const T: usize = NUM_ISSUERS / 2 + 1;
    const TPRIME: usize = N / 2 + 1;
    const NUM_ATTRIBUTES: usize = 10;

    bench_atact(c, NUM_ATTRIBUTES, NUM_ISSUERS, N, T, TPRIME);
}

fn bench_params_2(c: &mut Criterion) {
    const NUM_ISSUERS: usize = 50;
    const N: usize = 128;
    const T: usize = NUM_ISSUERS / 2 + 1;
    const TPRIME: usize = N / 2 + 1;
    const NUM_ATTRIBUTES: usize = 10;

    bench_atact(c, NUM_ATTRIBUTES, NUM_ISSUERS, N, T, TPRIME);
}

criterion_group!(benches, bench_params_1, bench_params_2);
criterion_main!(benches);
