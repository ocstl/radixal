# radixal

Digits iteration for unsigned integer types.

The `IntoDigits` trait offers a number of methods to facilitate dealing with 
unsigned integers as digits.

For less simple uses, the `DigitsIterator` implements a number of methods to 
manipulate the number in place, offering more control than the `IntoDigits` 
trait. 

## Features

This crate can be used without the standard library.

The `DigitsIterator` struct as well as the `IntoDigits` trait are only 
implemented for primitive unsigned types: `u8`, `u16`, `u32`, `u64`, `u128`,
`usize` as well as their corresponding `Wrapping` types.

Internal numerical operations use wrapping semantics when required, both for 
the sake of simplicity and performance. It is expected that checked 
operations will be used in a future version, while tying wrapping operations 
to an optional feature for performance sensitive uses.