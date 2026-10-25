module

public import VerifiedGarbage.Impl.Words.RISCV64

/-!
# 64-bit words in RISC-V code

Instruction sequences that the RISC-V implementations of hash functions on
big-endian 64-bit words (SHA-512, …) share, beside the little-endian ones of
`Impl/Words64/RISCV64.lean`; their lemmas are in
`Proof/Framework/RISCV64/ByteLoad64.lean`.

* A big-endian word of an argument buffer, whose alignment the contracts do
  not state, is loaded a byte at a time, from its most significant byte
  down, shifting what is loaded so far left by 8 before each `or` of the
  next byte, with one temporary register.
* A 64-bit constant is its high word, shifted up, plus its low word, each
  loaded by `li32`: as `addiw` sign-extends the low word, the high word is
  incremented first when the low word's top bit is set. That is two
  instructions fewer than `movImm64`, which clears the sign extension with
  two shifts: it builds SHA-512's 80 round constants in every block.
-/

@[expose] public section

namespace VG.Impl.Words.RISCV64

open VG.RISCV64

/-- `d :=` the big-endian 64-bit word at `off(n)`, a byte at a time; `tmp` is
clobbered. `d`, `tmp` and `n` are different. -/
def loadBE64 (d tmp n : Reg) (off : Nat) : List Instr :=
  [.load .b d n off,
   .shift .sll .d d d 8, .load .b tmp n (off + 1), .logic .or d d tmp,
   .shift .sll .d d d 8, .load .b tmp n (off + 2), .logic .or d d tmp,
   .shift .sll .d d d 8, .load .b tmp n (off + 3), .logic .or d d tmp,
   .shift .sll .d d d 8, .load .b tmp n (off + 4), .logic .or d d tmp,
   .shift .sll .d d d 8, .load .b tmp n (off + 5), .logic .or d d tmp,
   .shift .sll .d d d 8, .load .b tmp n (off + 6), .logic .or d d tmp,
   .shift .sll .d d d 8, .load .b tmp n (off + 7), .logic .or d d tmp]

/-- The high word `li64` loads before shifting it up: `v`'s high word, plus
the top bit of its low word, which `addiw` sign-extends. -/
def hiAdj (v : BitVec 64) : BitVec 32 :=
  (v >>> 32).setWidth 32 + ((v >>> 31).setWidth 32 &&& 1)

/-- `d := v`, with `tmp` clobbered: the adjusted high word (`li32`), shifted
up, plus the sign-extended low word (`li32`). `d` and `tmp` are different. -/
def li64 (d tmp : Reg) (v : BitVec 64) : List Instr :=
  li32 d (hiAdj v) ++ [.shift .sll .d d d 32] ++ li32 tmp (v.setWidth 32) ++ [.add d d tmp]

end VG.Impl.Words.RISCV64
