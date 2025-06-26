use bitvec::bitvec;
use bitvec::order::Msb0;
use log::info;
use num_integer::Roots;
use num_prime::detail::SMALL_PRIMES;
use crate::MAX_TRIAL_DIVISIONS;

pub const EXPANSION_UNIT: u64 = 1 << 28;

pub struct PrimeBuffer(Vec<u64>);

pub struct PrimeBufferIter<'a> {
    index: usize,
    buffer: &'a mut PrimeBuffer
}

impl Iterator for PrimeBufferIter<'_> {
    type Item = u64;

    fn next(&mut self) -> Option<Self::Item> {
        let mut next_read = self.buffer.0.get(self.index);
        while next_read.is_none() {
            self.buffer.grow(EXPANSION_UNIT, MAX_TRIAL_DIVISIONS);
            next_read = self.buffer.0.get(self.index);
        }
        self.index += 1;
        next_read.copied()
    }
}

impl PrimeBuffer {
    pub fn new() -> Self {
        PrimeBuffer(SMALL_PRIMES.iter().map(|x| *x as u64).collect())
    }
    pub fn primes(&mut self) -> PrimeBufferIter<'_> {
        PrimeBufferIter {
            index: 0,
            buffer: self
        }
    }

    pub fn bound(&self) -> u64 {
        *self.0.last().unwrap()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub(crate) fn grow(&mut self, desired_growth: u64, len_limit: usize) {
        if len_limit < self.len() {
            info!("No need to grow the prime buffer");
            return;
        }
        let current = self.bound();
        let mut sieve_limit = ((current + desired_growth) | 1) + 2; // make sure sieving limit is odd and larger than limit
        sieve_limit = (current + desired_growth).min(sieve_limit);
        self.0.reserve(len_limit - self.len());
        info!("Expanding prime limit from {} to {}", current, sieve_limit);
        // create sieve and filter with existing primes
        let mut sieve = bitvec![usize, Msb0; 0; ((sieve_limit - current) / 2) as usize];
        for p in self.0.iter().copied().skip(1) {
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
            self.0.push(x);
            size_increase += 1;
            new_bound = x;
        });
        info!("Done expanding prime limit from {} to {}", current, sieve_limit);
        #[cfg(debug_assertions)]
        if sieve_limit >= 563743 {
            debug_assert!(self.0.contains(&563743));
        }
    }
}