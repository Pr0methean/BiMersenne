mod buffer;

use num_bigint::BigUint;
use num_prime::nt_funcs::{factorize128};
use num_prime::{BitTest, ExactRoots, Primality};
use std::borrow::Cow;
use std::fmt::{Debug, Display, Formatter};
use std::iter;
use std::ops::{Shl, Sub};
use std::time::{Duration, Instant};
use log::info;
use mod_exp::mod_exp;
use num_prime::detail::SMALL_PRIMES;
use Primality::{No, Probable, Yes};
use crate::buffer::{PrimeBuffer};

pub const MERSENNE_EXPONENTS: [u32; 52] = [
    2, 3, 5, 7, 13, 17, 19, 31, 61, 89, 107, 127, 521, 607, 1279, 2203, 2281, 3217, 4253, 4423,
    9689, 9941, 11213, 19937, 21701, 23209, 44497, 86243, 110503, 132049, 216091, 756839, 859433,
    1257787, 1398269, 2976221, 3021377, 6972593, 13466917, 20996011, 24036583, 25964951, 30402457,
    32582657, 37156667, 42643801, 43112609, 57885161, 74207281, 77232917, 82589933, 136279841,
];
pub const MAX_TRIAL_DIVISIONS: usize = 1 << 31;
pub const NUM_TRIAL_ROOTS: u64 = 1 << 8;
pub const SKIPPED_PRIMES_COUNT: usize = 2; // (2^p-1)*(2^q-1) - 2 can't divide 2 or 3

// 5, 7, 11 and 13 are factored separately because they follow simple patterns
// (e.g. no factor of 11 unless p and q end in 9 and 3)
// 17, 31 and 41 don't seem to occur as factors at all (FIXME: prove this)
// 19, 23, 29, 37, 43, 47 are a bit too common even though there's no obvious pattern
pub const SPECIALLY_HANDLED_PRIMES_COUNT: usize = 13;
pub const SPECIALLY_HANDLED_PRIMES: [u64; SPECIALLY_HANDLED_PRIMES_COUNT] = [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47];

#[inline]
fn is_prime_with_trials(p: u64, q: u64, buffer: &mut PrimeBuffer) -> PrimalityResult {
    let mut trial_factors = Vec::new();
    for small_factor in SPECIALLY_HANDLED_PRIMES {
        let power = trial_division(p, q, small_factor);
        trial_factors.extend(iter::repeat(small_factor).take(power as usize));
    }
    let small_factors_product: BigUint = trial_factors.iter().copied().map(BigUint::from).product();
    let cofactor = product_m2_as_biguint(p, q) / &small_factors_product;
    if p + q <= small_factors_product.bits() + 128 {
        if let Ok(cofactor) = u128::try_from(&cofactor) {
            let large_factors = factorize128(cofactor);
            return PrimalityResult {
                result: No,
                source: format!("factors are {:?} (trial factoring) and {:?} (factorize128)",
                                trial_factors, large_factors).into()
            };
        }
    }
    info!("Starting larger trial divisions for a {}-bit number", p + q);
    let mut divisions_done = 0;
    let report_progress_every = match p + q {
        0..10_000_000 => 1 << 24,
        10_000_000..100_000_000 => 1 << 23,
        _ => 1 << 22,
    };
    let mut last_prime = SPECIALLY_HANDLED_PRIMES[SPECIALLY_HANDLED_PRIMES_COUNT - 1];
    let start_trials = Instant::now();
    let mut prime_iter = buffer.primes().skip(SPECIALLY_HANDLED_PRIMES_COUNT + 2);
    loop {
        let prime = prime_iter.next().unwrap();
        let power = trial_division(p, q, prime);
        if power > 0 {
            info!("Trial division found factor of {}^{} for a {}-bit number in {}",
                prime, power, p+q, ReadableDuration(start_trials.elapsed()));
            trial_factors.extend(iter::repeat(prime).take(power as usize));
            return PrimalityResult {
                result: No,
                source: format!("Trial division found factors {:?}", trial_factors).into()
            };
        }
        last_prime = prime;
        divisions_done += 1;
        if divisions_done % report_progress_every == 0 {
            info!("{} trial divisions done for a {}-bit number in {}",
                      divisions_done, p + q, ReadableDuration(start_trials.elapsed()));
        }
        if divisions_done >= MAX_TRIAL_DIVISIONS {
            break;
        }
    }
    info!("Starting trial roots for a {}-bit number", p + q);
    let min_root_bits = (last_prime + 2).bits() as u64;
    let start_roots = Instant::now();
    let mut remaining_roots = NUM_TRIAL_ROOTS;
    let max_power_bits = (p + q + 1) / min_root_bits;
    for prime in SMALL_PRIMES.iter().copied().take(NUM_TRIAL_ROOTS as usize) {
        if prime.bits() as u64 > max_power_bits {
            // Higher roots would've been found by trial divisions already
            info!("Ruling out {} and higher roots for a {}-bit number because divisions would have found them ({} trial roots skipped)",
                      prime, p + q, remaining_roots);
            break;
        }
        remaining_roots -= 1;
        if cofactor.is_nth_power(prime as u32) {
            info!("Trial root found {} root of a {}-bit number in {}",
                      prime, p + q, ReadableDuration(start_trials.elapsed()));
            return PrimalityResult {
                result: No,
                source: format!("Trial nth root: {} and factors: {:?}", prime, trial_factors).into(),
            };
        } else {
            info!("{}-bit number has no {} root (trying roots for {})",
                      p + q, prime, ReadableDuration(start_roots.elapsed()));
        }
    }
    info!("Trial roots failed for a {}-bit number in {} ns",
              p + q, ReadableDuration(start_roots.elapsed()));
    PrimalityResult {
        result: Probable(0.5),
        source: format!("Trial divisions by {:?}", trial_factors).into(),
    }
}

#[inline]
fn trial_division(p: u64, q: u64, prime: u64) -> u64 {
    if prime == p || prime == q {
        return 0;
    }
    let mut power = 0;
    let prime = prime as u128;
    let mut modulus = prime;
    while modulus < 1<<64 {
        let mut remainder = mod_exp(2u128, (p + q) as u128, modulus)
            + (modulus - mod_exp(2u128, p as u128, modulus))
            + (modulus - mod_exp(2u128, q as u128, modulus))
            - 1;
        remainder %= modulus;
        if remainder == 0 {
            modulus *= prime;
            power += 1;
        } else {
            return power;
        }
    }
    let prime = BigUint::from(prime);
    let two = BigUint::from(2u8);
    let p_plus_q = BigUint::from(p + q);
    let p = BigUint::from(p);
    let q = BigUint::from(q);
    let mut modulus = BigUint::from(modulus);
    loop {
        let remainder = (two.modpow(&p_plus_q, &modulus)
            + (&modulus - two.modpow(&p, &modulus))
            + (&modulus - two.modpow(&q, &modulus))
            - 1u32) % &modulus;
        if remainder == BigUint::ZERO {
            modulus *= &prime;
            power += 1;
        } else {
            return power;
        }
    }
}

#[inline]
fn one() -> BigUint {
    BigUint::from(1u8)
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

struct PrimalityResult {
    result: Primality,
    source: Cow<'static, str>,
}

impl Display for PrimalityResult {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(format!("{:?}, {}", self.result, self.source).as_str())
    }
}

fn main() {
    simple_logger::init().unwrap();
    let mut buffer = PrimeBuffer::new();
    for p_i in (0..(MERSENNE_EXPONENTS.len() - 5)).rev() {
        let p = MERSENNE_EXPONENTS[p_i];
        for q_i in (p_i..MERSENNE_EXPONENTS.len()).rev() {
            let q = MERSENNE_EXPONENTS[q_i];
            if p + q <= 128 {
                let m_p = (1u64 << p) - 1;
                let m_q = (1u128 << q) - 1;
                let productm2 = m_p as u128 * m_q - 2;
                let start_factorize128 = Instant::now();
                let factors = factorize128(productm2);
                info!("factorize128 finished for {} in {}", productm2, ReadableDuration(start_factorize128.elapsed()));
                let result = PrimalityResult {
                    result: if factors.values().sum::<usize>() == 1 {
                        Yes
                    } else {
                        No
                    },
                    source: format!("factorize128 gives factors: {:?}", factors).into(),
                };
                println!("{},{}: {}", p, q, result);
            } else {
                let result = is_prime_with_trials(p as u64, q as u64, &mut buffer);
                println!("{},{}: {}", p, q, result);
            }
        }
    }
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