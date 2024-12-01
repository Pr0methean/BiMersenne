mod buffer;

use num_bigint::BigUint;
use num_prime::nt_funcs::{factorize128};
use num_prime::{BitTest, ExactRoots, Primality};
use std::borrow::Cow;
use std::fmt::{Debug, Display, Formatter};
use std::fs::File;
use std::io::Write;
use std::ops::{Shl, Sub};
use std::sync::{OnceLock};
use std::time;
use std::time::Duration;
use mod_exp::mod_exp;
use Primality::{No, Yes};
use tokio::task::JoinSet;
use crate::buffer::ConcurrentPrimeBuffer;

pub const MERSENNE_EXPONENTS: [u32; 52] = [
    2, 3, 5, 7, 13, 17, 19, 31, 61, 89, 107, 127, 521, 607, 1279, 2203, 2281, 3217, 4253, 4423,
    9689, 9941, 11213, 19937, 21701, 23209, 44497, 86243, 110503, 132049, 216091, 756839, 859433,
    1257787, 1398269, 2976221, 3021377, 6972593, 13466917, 20996011, 24036583, 25964951, 30402457,
    32582657, 37156667, 42643801, 43112609, 57885161, 74207281, 77232917, 82589933, 136279841,
];
pub const MAX_TRIAL_DIVISIONS: u64 = 1 << 34;
pub const NUM_TRIAL_ROOTS: u64 = 1 << 8;

static BUFFER: OnceLock<ConcurrentPrimeBuffer> = OnceLock::new();

async fn is_prime_with_trials(p: u64, q: u64) -> PrimalityResult {
    let mut join_set = JoinSet::new();
    join_set.spawn(async move {
        let mut divisions_done = 0;
        let report_progress_every = match p + q {
            0..10_000_000 => 1 << 24,
            10_000_000..100_000_000 => 1 << 22,
            _ => 1 << 20,
        };
        let buffer = get_buffer();
        let mut last_prime = 0;
        let mut factors = Vec::with_capacity(3);
        let start_trials = time::Instant::now();
        for prime in buffer.primes(u64::MAX) {
            if prime != p && prime != q {
                let prime = prime as u128;
                let mut modulus = prime;
                let mut remainder;
                let mut factor_found = false;
                loop {
                    remainder = mod_exp(2u128, (p + q) as u128, modulus)
                        + (prime - mod_exp(2u128, p as u128, modulus))
                        + (prime - mod_exp(2u128, q as u128, modulus))
                        - 1;
                    remainder %= prime;
                    if remainder == 0 {
                        factors.push(prime);
                        eprintln!("Trial division found {} as a factor of a {}-bit number in {}",
                                  prime, p + q, ReadableDuration(start_trials.elapsed()));
                        modulus *= prime;
                        factor_found = true;
                    } else {
                        break;
                    }
                }
                if factor_found && prime > 7 {
                    return Some(PrimalityResult {
                        result: No,
                        source: format!("Trial divisions by {:?}", factors).into(),
                    });
                }
            }
            last_prime = prime;
            divisions_done += 1;
            if divisions_done % report_progress_every == 0 {
                eprintln!("{} trial divisions done for a {}-bit number in {}",
                          divisions_done, p + q, ReadableDuration(start_trials.elapsed()));
            }
            if divisions_done >= MAX_TRIAL_DIVISIONS {
                break;
            }
        }
        if factors.is_empty() {
            let min_root_bits = (last_prime + 2).bits() as u64;
            let start_roots = time::Instant::now();
            let num = product_m2_as_biguint(p, q);
            let mut remaining_roots = NUM_TRIAL_ROOTS;
            for prime in buffer.primes(buffer.get_nth(NUM_TRIAL_ROOTS)) {
                if (prime.bits() as u64 - 1) * (min_root_bits - 1) > p + q {
                    // Higher roots would've been found by trial divisions already
                    eprintln!("Ruling out {} and higher roots for a {}-bit number because divisions would have found them ({} trial roots skipped)",
                              prime, p + q, remaining_roots);
                    break;
                }
                remaining_roots -= 1;
                if prime == 2 && p + q < 100_000_000 {
                    // Previous runs have ruled out numbers in this range being perfect squares
                    continue;
                }
                if num.is_nth_power(prime as u32) {
                    eprintln!("Trial root found {} root of a {}-bit number in {}",
                              prime, p + q, ReadableDuration(start_trials.elapsed()));
                    return Some(PrimalityResult {
                        result: No,
                        source: format!("Trial nth root: {} and factors: {:?}", prime, factors).into(),
                    });
                } else if p + q > 100_000 || remaining_roots == 0 {
                    eprintln!("{}-bit number has no {} root (trying roots for {})",
                              p + q, prime, ReadableDuration(start_roots.elapsed()));
                }
            }
            eprintln!("Trial roots failed for a {}-bit number in {} ns; calling is_prime",
                      p + q, start_roots.elapsed().as_nanos());
            return None;
        }
        Some(PrimalityResult {
            result: No,
            source: format!("Trial divisions by {:?}", factors).into(),
        })
    });
    join_set.spawn(async move {
        let buffer = get_buffer();
        tokio::task::yield_now().await;
        let start_is_prime = time::Instant::now();
        let product_m2 = product_m2_as_biguint(p, q);
        let result = buffer.is_prime(&product_m2);
        let elapsed = start_is_prime.elapsed();
        drop(product_m2);
        eprintln!(
            "is_prime for a {}-bit number took {} and returned {:?}",
            p + q,
            ReadableDuration(elapsed),
            result
        );
        Some(PrimalityResult {
            result,
            source: "is_prime".into(),
        })
    });
    while let Some(result) = join_set.join_next().await {
        if let Some(result) = result.unwrap() {
            return result;
        }
    }
    panic!("Both trial divisions and is_prime failed for a {}-bit number", p + q);
}

fn product_m2_as_biguint(p: u64, q: u64) -> BigUint {
    let mut product_limbs = vec![u32::MAX; (p + q) as usize / 32];
    if (p + q) % 32 != 0 {
        product_limbs.push((1 << ((p + q) % 32)) - 1);
    }
    let mut product_m2: BigUint = BigUint::new(product_limbs);
    debug_assert!(product_m2 == one().shl(p + q).sub(one()));
    if p == q {
        product_m2.set_bit(p + 1, false);
    } else {
        product_m2.set_bit(p, false);
        product_m2.set_bit(q, false);
    }
    debug_assert!(product_m2 == one().shl(p + q).sub(one().shl(p)).sub(one().shl(q)).sub(one()));
    product_m2
}

fn get_buffer() -> &'static ConcurrentPrimeBuffer {
    BUFFER.get_or_init(|| {
        let buffer = ConcurrentPrimeBuffer::new();
        buffer
    })
}

struct PrimalityResult {
    result: Primality,
    source: Cow<'static, str>,
}

impl Display for PrimalityResult {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(format!("{:?}, {}", self.result, self.source).as_str())
    }
}

#[tokio::main(flavor = "multi_thread")]
async fn main() {
    tokio::spawn(async {
        get_buffer().get_nth(MAX_TRIAL_DIVISIONS);
    }); // Start building buffer ahead of time
    let mut output_tasks = Vec::new();
    let mut is_prime_calls = 0;
    let mut factorize128_calls = 0;
    for p_i in (0..MERSENNE_EXPONENTS.len()).rev() {
        let p = MERSENNE_EXPONENTS[p_i];
        for q_i in (p_i..MERSENNE_EXPONENTS.len()).rev() {
            let q = MERSENNE_EXPONENTS[q_i];
            let num_filename = std::path::PathBuf::from(format!("result_{}_{}.txt", p, q));
            if num_filename.exists() {
                continue;
            }
            if p + q <= 128 {
                factorize128_calls += 1;
                let m_p = (1u64 << p) - 1;
                let m_q = (1u128 << q) - 1;
                let product = m_p as u128 * m_q;
                output_tasks.push(tokio::spawn(async move {
                    let factors = factorize128(product - 2);
                    let result = PrimalityResult {
                        result: if factors.values().sum::<usize>() == 1 {
                            Yes
                        } else {
                            No
                        },
                        source: format!("factorize128 gives factors: {:?}", factors).into(),
                    };
                    File::create(num_filename).unwrap().write_all(result.to_string().as_bytes()).unwrap()
                }));
            } else {
                is_prime_calls += 1;
                output_tasks.push(tokio::spawn(async move {
                    let result = is_prime_with_trials(p as u64, q as u64).await;
                    File::create(num_filename).unwrap().write_all(result.to_string().as_bytes()).unwrap()
                }));
            }
        }
    }
    eprintln!("All computation tasks launched: {} using factorize128, {} using is_prime or trial divisions",
              factorize128_calls, is_prime_calls);
    for task in output_tasks.into_iter() {
        task.await.unwrap();
    }
}

fn one() -> BigUint {
    BigUint::from(1u8)
}

struct ReadableDuration(Duration);

impl Display for ReadableDuration {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut seconds = self.0.as_secs();
        if seconds == 0 {
            return self.0.fmt(f);
        }
        let days = seconds / (60 * 60 * 24);
        seconds %= 60 * 60 * 24;
        let hours = seconds / (60 * 60);
        seconds %= 60 * 60;
        let minutes = seconds / 60;
        seconds %= 60;
        let nanos = self.0.as_nanos() % 1_000_000_000;
        if days == 0 {
            if hours == 0 {
                if minutes == 0 {
                    return f.write_str(format!("{}.{:09}s", seconds, nanos).as_str());
                }
                return f.write_str(format!("{}m{:02}.{:09}s", minutes, seconds, nanos).as_str());
            }
            return f.write_str(format!("{}h{:02}m{:02}.{:09}s", hours, minutes, seconds, nanos).as_str());
        }
        f.write_str(format!("{}d{:02}h{:02}m{:02}.{:09}s", days, hours, minutes, seconds, nanos).as_str())
    }
}