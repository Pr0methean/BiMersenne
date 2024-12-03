use std::hint;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Instant;
use bitvec::bitvec;
use bitvec::order::Msb0;
use concurrent_list::{Iter, Reader, Writer};
use log::info;
use num_bigint::BigUint;
use num_integer::Roots;
use num_prime::detail::SMALL_PRIMES;
use num_prime::{Primality, PrimalityUtils};
use parking_lot::{Mutex};
use rand::rngs::ThreadRng;
use rand::RngCore;
use crate::ReadableDuration;

const SPRP_TRIALS: u64 = 8;
const RANDOM_SPRP_TRIALS: u64 = 4;
pub const EXPANSION_UNIT: u64 = 1 << 30;

pub struct ConcurrentPrimeBuffer {
    reader: Reader<u64>,
    writer: Mutex<Writer<u64>>,
    bound: AtomicU64,
    len: AtomicU64
}

pub struct ConcurrentPrimeBufferIter<'a> {
    iter: Iter<'a, u64>,
    buffer: &'a ConcurrentPrimeBuffer
}

impl Iterator for ConcurrentPrimeBufferIter<'_> {
    type Item = u64;

    fn next(&mut self) -> Option<Self::Item> {
        let mut next_read = self.iter.next();
        while next_read.is_none() {
            if !self.buffer.reserve_concurrent(self.buffer.bound.load(Ordering::Acquire) + EXPANSION_UNIT) {
                hint::spin_loop();
            }
            next_read = self.iter.next();
        }
        next_read.map(|x| *x)
    }
}

impl ConcurrentPrimeBuffer {
    pub fn new() -> Self {
        let (mut writer, reader) = concurrent_list::new();
        SMALL_PRIMES.iter().for_each(|prime| writer.push(*prime as u64));
        ConcurrentPrimeBuffer {
            reader,
            writer: Mutex::new(writer),
            len: AtomicU64::new(SMALL_PRIMES.len() as u64),
            bound: AtomicU64::new(*SMALL_PRIMES.last().unwrap() as u64)
        }
    }
    pub fn primes(&self) -> ConcurrentPrimeBufferIter {
        ConcurrentPrimeBufferIter {
            iter: self.reader.iter(),
            buffer: self
        }
    }

    pub fn bound(&self) -> u64 {
        self.bound.load(Ordering::Acquire)
    }

    pub fn len(&self) -> u64 {
        self.len.load(Ordering::Acquire)
    }

    pub(crate) fn reserve_concurrent(&self, limit: u64) -> bool {
        let Some(mut writer) = self.writer.try_lock() else {
            return false;
        };
        let sieve_limit = (limit | 1) + 2; // make sure sieving limit is odd and larger than limit
        let current = self.bound();
        if sieve_limit < current {
            return true;
        }
        info!("Expanding prime limit from {} to {}", current, sieve_limit);
        let sieve_start = Instant::now();
        // create sieve and filter with existing primes
        let mut sieve = bitvec![usize, Msb0; 0; ((sieve_limit - current) / 2) as usize];
        for p in self.reader.iter().skip(1) {
            let p = *p;
            // skip pre-filtered 2
            let start = if p * p < current {
                p * ((current / p) | 1) // start from an odd factor
            } else {
                p * p
            };
            for multi in (start..sieve_limit).step_by(2 * (p as usize)) {
                if multi >= current {
                    sieve.set(((multi - current) / 2) as usize, true);
                }
            }
        }

        // sieve with new primes
        for p in (current..Roots::sqrt(&sieve_limit) + 1).step_by(2) {
            for multi in (p * p..sieve_limit).step_by(2 * (p as usize)) {
                if multi >= current {
                    sieve.set(((multi - current) / 2) as usize, true);
                }
            }
        }

        // collect the sieve
        let mut size_increase = 0;
        let mut new_bound = 0;
        sieve.iter_zeros().map(|x| (x as u64) * 2 + current).for_each(|x| {
            writer.push(x);
            size_increase += 1;
            new_bound = x;
        });
        self.len.fetch_add(size_increase, Ordering::AcqRel);
        self.bound.store(new_bound, Ordering::Release);
        info!("Expanding prime limit from {} to {} took {}", current, sieve_limit, ReadableDuration(sieve_start.elapsed()));
        true
    }

    #[inline]
    pub fn is_prime(
        &self,
        target: &BigUint,
    ) -> Primality
    {
        let mut probability = 1.;

        // miller-rabin test
        let mr_start = Instant::now();
        let mut witness_list: Vec<u64> = Vec::with_capacity((SPRP_TRIALS + RANDOM_SPRP_TRIALS) as usize);
        witness_list.extend(self.primes().take(SPRP_TRIALS as usize));
        probability *= 1. - 0.25f32.powi(SPRP_TRIALS as i32);
        for _ in 0..RANDOM_SPRP_TRIALS {
            // we have ensured target is larger than 2^64
            let mut w: u64 = ThreadRng::default().next_u64();
            while witness_list.iter().any(|x| x == &w) {
                w = ThreadRng::default().next_u64();
            }
            witness_list.push(w);
        }
        probability *= 1. - 0.25f32.powi(RANDOM_SPRP_TRIALS as i32);
        if !witness_list
            .into_iter()
            .all(|x| {
                let mr_start = Instant::now();
                let result = target.is_sprp(BigUint::from(x));
                info!("Miller-Rabin test for a {}-bit number with witness {} took {} and returned {}",
                          target.bits(), x, ReadableDuration(mr_start.elapsed()), result);
                result
            })
        {
            info!("Miller-Rabin test found a {}-bit number composite after {}", target.bits(),
                      ReadableDuration(mr_start.elapsed()));
            return Primality::No;
        }
        info!("Miller-Rabin test failed to prove a {}-bit number composite after {}", target.bits(),
                  ReadableDuration(mr_start.elapsed()));
        // lucas probable prime test
        probability *= 1. - 4f32 / 15f32;
        let lucas_start = Instant::now();
        if !target.is_slprp(None, None) {
            info!("Strong Lucas test found a {}-bit number composite after {}", target.bits(),
                      ReadableDuration(lucas_start.elapsed()));
            return Primality::No;
        }
        info!("Strong Lucas test failed to prove a {}-bit number composite after {}", target.bits(),
                  ReadableDuration(lucas_start.elapsed()));
        probability *= 1. - 4f32 / 15f32;
        let lucas_start = Instant::now();
        if !target.is_eslprp(None) {
            info!("Extra-strong Lucas test found a {}-bit number composite after {}", target.bits(),
                      ReadableDuration(lucas_start.elapsed()));
            return Primality::No;
        }
        info!("Extra-strong Lucas test failed to prove a {}-bit number composite after {}", target.bits(),
                  ReadableDuration(lucas_start.elapsed()));
        Primality::Probable(probability)
    }
}
