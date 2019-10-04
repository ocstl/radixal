#![feature(test)]
extern crate test;

macro_rules! create_radix2_bench {
    ( $t:ident ) => {
        #[bench]
        fn bench_radix2(b: &mut Bencher) {
            let target = core::$t::MAX / 2;
            b.iter(|| target.into_binary_digits());
        }
    }
}

macro_rules! create_radix10_bench {
    ( $t:ident ) => {
        #[bench]
        fn bench_radix10(b: &mut Bencher) {
            let target = core::$t::MAX / 2;
            b.iter(|| target.into_decimal_digits());
        }
    }
}

macro_rules! create_radix16_bench {
    ( $t:ident ) => {
        #[bench]
        fn bench_radix16(b: &mut Bencher) {
            let target = core::$t::MAX / 2;
            b.iter(|| target.into_digits(16));
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
