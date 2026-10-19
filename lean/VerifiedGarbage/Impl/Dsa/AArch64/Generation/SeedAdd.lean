module

public import VerifiedGarbage.Impl.Bignum.AArch64.Core

/-! # Wrapped addition of a public offset to a DSA seed

The seed and output pointers are x1 and x2; x0 carries the offset.
Bytes are visited from least to most significant, discarding final overflow.
The parameter generator uses fixed 20- and 32-byte seeds.
-/

@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64

def seedAddByte (i : Nat) : List Instr :=
  [.ldrb .x3 .x1 i, .add .x .x0 .x0 .x3,
   .strb .x0 .x2 i, .lsr .x .x0 .x0 8]

def seedAdd : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (.block (seedAddByte n)) (seedAdd n)

end VG.Impl.Dsa.AArch64.Generation
