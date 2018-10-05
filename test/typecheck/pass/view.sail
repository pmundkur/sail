$option -view_patterns

default Order dec

$include <prelude.sail>

val print = "print_endline" : string -> unit

val "parse_bits" : string -> {'n, 'n >= 0. option(bits('n))}

// hex_bits_forwards is partial, so it should return an option. We
// should have some kind of syntax for this in the mapping patterns types
// maybe?

val hex_bits_forwards : forall 'n, 'n >= 0. string -> option(bits('n))

// We can't actually make hex_bits_forwards directly as an external
// function, so we use the "parse_bits" extern. It takes a string and
// returns a option(bits('n)) or any length. We check that this is equal
// to the desired length of the type variable 'n, otherwise return
// None(). The reason for this is that external functions can't know
// about Sail type variables.

function hex_bits_forwards(str) = {
  match parse_bits(str) {
    Some(xs) => if length(xs) == 'n then Some(xs) else None(),
    None() => None()
  }
}

// hex_bits_backwards is total.

val hex_bits_backwards = "string_of_bits" : forall 'n, 'n >= 0. bits('n) -> string

// Regular function overloading then gives us the hex_bits mapping
// primitive.

overload hex_bits = {hex_bits_backwards, hex_bits_forwards}

function main() : unit -> unit = {
  match "0x123" {
    // Currently we need this type annotation which is a bit
    // awkward. I want to fix this.
    hex_bits(Some(0x123) : option(bits(12))) => print("ok"),
    _ => print("fail") };
  match 0x1 @ 0x23 {
    hex_bits(str) => print(str)
  }
}
