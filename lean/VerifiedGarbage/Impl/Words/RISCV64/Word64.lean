module

public import VerifiedGarbage.Impl.Words.RISCV64

/-!
# 64-bit words in RISC-V code

Instruction sequences that the RISC-V implementations of hash functions on
64-bit words (SHA-512, …) share; their lemmas are in
`Proof/Framework/RISCV64/ByteLoad64.lean`. As for 32-bit words
(`Impl/Words/RISCV64.lean`), words of argument buffers are loaded and stored
a byte at a time, since the contracts state no alignment for them:

* a word is loaded from its most significant byte down, shifting what is
  loaded so far left by 8 before each `or` of the next byte, in either byte
  order, with one temporary register;
* it is stored by shifting each byte down, least significant first;
* a 64-bit constant is its high word, shifted up, plus its low word, each
  loaded by `li32`: as `addiw` sign-extends the low word, the high word is
  incremented first when the low word's top bit is set.
-/

@[expose] public section

namespace VG.Impl.Words.RISCV64

open VG.RISCV64

/-- `d :=` the 64-bit word whose bytes, most significant first, are at
`off(n) + o 0`, …, `off(n) + o 7`; `tmp` is clobbered. `d`, `tmp` and `n` are
different. -/
def loadBytes64 (d tmp n : Reg) (off : Nat) (o : Nat → Nat) : List Instr :=
  [.load .b d n (off + o 0),
   .shift .sll .d d d 8, .load .b tmp n (off + o 1), .logic .or d d tmp,
   .shift .sll .d d d 8, .load .b tmp n (off + o 2), .logic .or d d tmp,
   .shift .sll .d d d 8, .load .b tmp n (off + o 3), .logic .or d d tmp,
   .shift .sll .d d d 8, .load .b tmp n (off + o 4), .logic .or d d tmp,
   .shift .sll .d d d 8, .load .b tmp n (off + o 5), .logic .or d d tmp,
   .shift .sll .d d d 8, .load .b tmp n (off + o 6), .logic .or d d tmp,
   .shift .sll .d d d 8, .load .b tmp n (off + o 7), .logic .or d d tmp]

/-- `d :=` the big-endian 64-bit word at `off(n)`, a byte at a time. -/
def loadBE64 (d tmp n : Reg) (off : Nat) : List Instr := loadBytes64 d tmp n off id

/-- `d :=` the little-endian 64-bit word at `off(n)`, a byte at a time. -/
def loadLE64b (d tmp n : Reg) (off : Nat) : List Instr := loadBytes64 d tmp n off (7 - ·)

/-- Store the low `w` bytes of `v` at `off(n)`, little-endian (least
significant first), a byte at a time; `tmp` is clobbered. `tmp` is neither
`v` nor `n`. -/
def storeLE (w : Nat) (v tmp n : Reg) (off : Nat) : List Instr :=
  (List.range w).flatMap fun j => [.shift .srl .d tmp v (8 * j), .store .b tmp n (off + j)]

/-- The high word `li64` loads before shifting it up: `v`'s high word, plus
the top bit of its low word, which `addiw` sign-extends. -/
def hiAdj (v : BitVec 64) : BitVec 32 :=
  (v >>> 32).setWidth 32 + ((v >>> 31).setWidth 32 &&& 1)

/-- `d := v`, with `tmp` clobbered: the adjusted high word (`li32`), shifted
up, plus the sign-extended low word (`li32`). `d` and `tmp` are different. -/
def li64 (d tmp : Reg) (v : BitVec 64) : List Instr :=
  li32 d (hiAdj v) ++ [.shift .sll .d d d 32] ++ li32 tmp (v.setWidth 32) ++ [.add d d tmp]

end VG.Impl.Words.RISCV64
