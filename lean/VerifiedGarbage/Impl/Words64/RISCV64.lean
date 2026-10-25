module

public import VerifiedGarbage.Impl.Words.RISCV64

/-!
# 64-bit words in RISC-V code

Instruction sequences for 64-bit words that the RISC-V implementations of
lane-oriented functions (Keccak, …) share; their lemmas are in
`Proof/Framework/RISCV64/Words64.lean`.

As for 32-bit words (`Impl/Words/RISCV64.lean`), argument buffers, whose
alignment the contracts do not state, are accessed a byte at a time: a
little-endian doubleword is two little-endian words (`loadLE32`,
`storeLE32`), the high one shifted up by 32. A 64-bit constant is its high
word (`li32`) shifted up by 32, or-ed with its low word (`li32`), whose sign
extension two shifts clear.
-/

@[expose] public section

namespace VG.Impl.Words64.RISCV64

open VG.RISCV64
open VG.Impl.Words.RISCV64

/-- `d :=` the little-endian doubleword at `off(n)`, a byte at a time;
`tmp` and `tmp2` are clobbered. `d`, `tmp`, `tmp2` and `n` are different. -/
def loadLE64 (d tmp tmp2 n : Reg) (off : Nat) : List Instr :=
  loadLE32 d tmp n off ++ loadLE32 tmp2 tmp n (off + 4) ++
    [.shift .sll .d tmp2 tmp2 32, .logic .or d d tmp2]

/-- Store `v` at `off(n)`, little-endian, a byte at a time; `tmp` and `tmp2`
are clobbered. `tmp` and `tmp2` are different, and neither is `v` nor `n`. -/
def storeLE64 (v tmp tmp2 n : Reg) (off : Nat) : List Instr :=
  storeLE32 v tmp n off ++ [.shift .srl .d tmp v 32] ++ storeLE32 tmp tmp2 n (off + 4)

/-- `d :=` the 64-bit constant `v`; `tmp` is clobbered. `d` and `tmp` are
different. -/
def movImm64 (d tmp : Reg) (v : BitVec 64) : List Instr :=
  li32 d (v.extractLsb' 32 32) ++ [.shift .sll .d d d 32] ++ li32 tmp (v.extractLsb' 0 32) ++
    [.shift .sll .d tmp tmp 32, .shift .srl .d tmp tmp 32, .logic .or d d tmp]

end VG.Impl.Words64.RISCV64
