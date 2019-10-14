#![feature(test)]
extern crate test;

macro_rules! create_radix2_bench {
    ( $t:ident ) => {
        #[bench]
        fn bench_into_radix2(b: &mut Bencher) {
            let target = core::$t::MAX >> 1;
            b.iter(|| target.into_binary_digits());
        }

        #[bench]
        fn bench_reverse_radix2(b: &mut Bencher) {
            let target = core::$t::MAX >> 1;
            b.iter(|| target.reverse_binary_digits());
        }

        #[bench]
        fn bench_permutation_radix2(b: &mut Bencher) {
            let target = core::$t::MAX >> 1;
            let reverse = target.reverse_binary_digits();
            b.iter(|| target.is_binary_permutation(reverse));
        }
    }
}

macro_rules! create_radix10_bench {
    ( $t:ident ) => {
        #[bench]
        fn bench_into_radix10(b: &mut Bencher) {
            let target = core::$t::MAX >> 1;
            b.iter(|| target.into_decimal_digits());
        }

        #[bench]
        fn bench_reverse_radix10(b: &mut Bencher) {
            let target = core::$t::MAX >> 1;
            b.iter(|| target.reverse_decimal_digits());
        }

        #[bench]
        fn bench_permutation_radix10(b: &mut Bencher) {
            let target = core::$t::MAX / 10;
            let reverse = target.reverse_binary_digits();
            b.iter(|| target.is_decimal_permutation(reverse));
        }
    }
}

macro_rules! create_radix16_bench {
    ( $t:ident ) => {
        #[bench]
        fn bench_into_radix16(b: &mut Bencher) {
            let target = core::$t::MAX >> 1;
            b.iter(|| target.into_digits(16));
        }

        #[bench]
        fn bench_reverse_radix16(b: &mut Bencher) {
            let target = core::$t::MAX >> 1;
            b.iter(|| target.reverse_digits(16));
        }

        #[bench]
        fn bench_permutation_radix16(b: &mut Bencher) {
            let target = core::$t::MAX >> 4;
            let reverse = target.reverse_binary_digits();
            b.iter(|| target.is_permutation(reverse, 16));
        }
    }
}

macro_rules! create_benches {
    ( $($t:ident)* ) => {
        $(
            mod $t {
                use radixal::IntoDigits;
                use test::Bencher;

                create_radix2_bench!($t);
                create_radix10_bench!($t);
                create_radix16_bench!($t);
            }
        )*
    }
}

create_benches!(u8 u16 u32 u64 u128 usize);
