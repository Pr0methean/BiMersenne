use bitvec::bitvec;
use bitvec::order::Msb0;
use num_integer::Roots;
use parking_lot::RwLock;
use num_prime::buffer::PrimeBuffer;
use num_prime::detail::SMALL_PRIMES;

pub struct ConcurrentPrimeBuffer(RwLock<Vec<u64>>);

pub struct ConcurrentPrimeBufferIter<'a> {
    buffer: &'a ConcurrentPrimeBuffer,
    index: usize,
}

impl Iterator for ConcurrentPrimeBufferIter<'_> {
    type Item = u64;

    fn next(&mut self) -> Option<Self::Item> {
        let result = self.buffer.0.read().get(self.index).copied();
        self.index += 1;
        result
    }
}

impl ConcurrentPrimeBuffer {
    pub fn new() -> Self {
        ConcurrentPrimeBuffer(RwLock::new(Vec::from(SMALL_PRIMES.map(u64::from))))
    }

    pub fn primes(&self, limit: u64) -> std::iter::Take<<Self as PrimeBuffer>::PrimeIter> {
        self.reserve(limit);
        let position = match self.0.read().binary_search(&limit) {
            Ok(p) => p + 1,
            Err(p) => p,
        }; // into_ok_or_err()
        self.iter().take(position)
    }
}

impl PrimeBuffer for ConcurrentPrimeBuffer {
    type PrimeIter = ConcurrentPrimeBufferIter<'_>;

    fn iter(&self) -> Self::PrimeIter {
        ConcurrentPrimeBufferIter {
            buffer: self,
            index: 0,
        }
    }
    fn reserve(&self, limit: u64) {
        let sieve_limit = (limit | 1) + 2; // make sure sieving limit is odd and larger than limit
        let current = self.bound();
        if sieve_limit < current {
            return;
        }
        let mut list = self.0.write();
        let current = self.bound();
        // create sieve and filter with existing primes
        let mut sieve = bitvec![usize, Msb0; 0; ((sieve_limit - current) / 2) as usize];
        for p in self.iter().skip(1) {
            // skip pre-filtered 2
            let start = if p * p < current {
                p * ((current / p) | 1) // start from an odd factor
            } else {
                p * p
            };
            for multi in (start..sieve_limit).step_by(2 * (*p as usize)) {
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
        list.extend(sieve.iter_zeros().map(|x| (x as u64) * 2 + current));
    }

    fn bound(&self) -> u64 {
        let list = self.0.read();
        *list.last().unwrap()
    }

    fn contains(&self, num: u64) -> bool {
        self.0.read().binary_search(&num).is_ok()
    }

    fn clear(&mut self) {
        self.0.write().truncate(SMALL_PRIMES.len());
    }
}