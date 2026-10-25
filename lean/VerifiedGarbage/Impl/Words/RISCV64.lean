module

public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# 32-bit words in RISC-V code

Instruction sequences that the RISC-V implementations of word-oriented hash
functions (SHA-256, SHA-1, MD5, SM3, …) share; their lemmas are in
`Proof/Framework/RISCV64/ByteLoad.lean`.

The model faults on a misaligned access, and the contracts state no
alignment for argument buffers, so words of argument buffers are loaded and
stored a byte at a time (`lbu`, `sb`): a word is assembled from its bytes
with shifts and `or`s, in either byte order, and stored by shifting each byte
down. A 32-bit constant is `lui` of its upper 20 bits (rounded) and `addiw`
of the rest, as the assembler's `li` expands it.
-/

@[expose] public section

namespace VG.Impl.Words.RISCV64

open VG.RISCV64

/-- `d :=` the big-endian 32-bit word at `off(n)` (zero-extended), a byte at
a time; `tmp` is clobbered. `d`, `tmp` and `n` are different. -/
def loadBE32 (d tmp n : Reg) (off : Nat) : List Instr :=
  [.load .b d n off, .shift .sll .d d d 24,
   .load .b tmp n (off + 1), .shift .sll .d tmp tmp 16, .logic .or d d tmp,
   .load .b tmp n (off + 2), .shift .sll .d tmp tmp 8, .logic .or d d tmp,
   .load .b tmp n (off + 3), .logic .or d d tmp]

/-- `d :=` the little-endian 32-bit word at `off(n)` (zero-extended), a byte
at a time; `tmp` is clobbered. `d`, `tmp` and `n` are different. -/
def loadLE32 (d tmp n : Reg) (off : Nat) : List Instr :=
  [.load .b d n off,
   .load .b tmp n (off + 1), .shift .sll .d tmp tmp 8, .logic .or d d tmp,
   .load .b tmp n (off + 2), .shift .sll .d tmp tmp 16, .logic .or d d tmp,
   .load .b tmp n (off + 3), .shift .sll .d tmp tmp 24, .logic .or d d tmp]

/-- Store the low word of `v` at `off(n)`, little-endian, a byte at a time;
`tmp` is clobbered. `tmp` is neither `v` nor `n`. -/
def storeLE32 (v tmp n : Reg) (off : Nat) : List Instr :=
  [.store .b v n off,
   .shift .srl .d tmp v 8, .store .b tmp n (off + 1),
   .shift .srl .d tmp v 16, .store .b tmp n (off + 2),
   .shift .srl .d tmp v 24, .store .b tmp n (off + 3)]

/-- Store the low `w` bytes of `v` at `off(n)`, big-endian (most significant
first), a byte at a time; `tmp` is clobbered. `tmp` is neither `v` nor `n`. -/
def storeBE (w : Nat) (v tmp n : Reg) (off : Nat) : List Instr :=
  (List.range w).flatMap fun j => [.shift .srl .d tmp v (8 * (w - 1 - j)), .store .b tmp n (off + j)]

/-- The upper 20 bits of `w` for `lui`, rounded so that the low 12 bits are a
signed immediate (`lo12`). -/
def hi20 (w : BitVec 32) : BitVec 20 := BitVec.ofNat 20 ((w.toNat + 2048) / 4096)

/-- The low 12 bits of `w`, as the signed immediate of `addiw` that `hi20`
leaves: in `[-2048, 2048)`. -/
def lo12 (w : BitVec 32) : Int :=
  if w.toNat % 4096 < 2048 then w.toNat % 4096 else (w.toNat % 4096 : Int) - 4096

/-- `d :=` a register whose low word is `w` (`lui`, then `addiw`). -/
def li32 (d : Reg) (w : BitVec 32) : List Instr := [.lui d (hi20 w), .addiw d d (lo12 w)]

end VG.Impl.Words.RISCV64
