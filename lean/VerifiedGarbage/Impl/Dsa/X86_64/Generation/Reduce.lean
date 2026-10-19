module

public import VerifiedGarbage.Impl.Rsa.X86_64.Keys

/-! # Final arithmetic for a DSA p candidate -/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Bignum.X86_64

/-- Subtract a division remainder into a distinct destination. -/
def subtractRemainder (dst x rem : Nat) : Prog isa :=
  .seq (.block (ws ++ [.mov32 .rbp (.imm 0)] ++ base x .r8 ++ base rem .r10 ++ base dst .rsi))
    (wordLoop 0 subBody)

/-- The preceding subtraction is even, so adding one needs no carry. -/
def incrementEven (dst : Nat) : List Instr :=
  ws ++ base dst .rbx ++ [.mov .rax (.mem (at0 .rbx)), .alu .add .rax (.imm 1),
    .store (at0 .rbx) .rax]

/-- Double an array in place; used for 2q and the saved generator exponent. -/
def doubleArray (dst : Nat) : Prog isa :=
  .seq (.block (ws ++ [.mov32 .rbp (.imm 0)] ++ base dst .rbx)) (wordLoop 0 shlBody)

/-- Input: X in array 0 and 2q in array 2. Output: p in array 5, quotient
in array 0, remainder in array 1. Array 4 preserves X during division. -/
def reduceCandidate : Prog isa := seqs [copyA 4 0, divmod 0 1 2 3,
  subtractRemainder 5 4 1, .block (incrementEven 5)]

end VG.Impl.Dsa.X86_64.Generation
