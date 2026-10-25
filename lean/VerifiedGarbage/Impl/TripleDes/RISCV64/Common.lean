module

public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# Fixed bit permutations on RISC-V

As on PPC64LE (`Impl/TripleDes/PPC64LE/Common.lean`), one bit at a time:
each output bit is shifted down to bit 0, masked with `andi`, shifted up to
its place and XORed into the result. RV64I has no rotation, but a single
bit at the bottom of a word is placed by a left shift.
-/

@[expose] public section

namespace VG.Impl.TripleDes.RISCV64

open VG.RISCV64

/-- `mv d, n` (`addi d, n, 0`). -/
def movR (d n : Reg) : Instr := .addi d n 0

/-- `d := n >>> k`, as a move when `k = 0`. -/
def shrFrom (d n : Reg) (k : Nat) : List Instr := if k = 0 then [movR d n] else [.shift .srl .d d n k]

/-- The bit at the bottom of `r` to bit `n`. -/
def placeBit (r : Reg) (n : Nat) : List Instr := if n = 0 then [] else [.shift .sll .d r r n]

/-- Keep exactly the low `n` bits with two fixed shifts. -/
def mask (r : Reg) (n : Nat) : List Instr := [.shift .sll .d r r (64 - n), .shift .srl .d r r (64 - n)]

/-- A fixed bit permutation of the low `n` bits of `src` into the low `m`
bits of `dst`, one bit at a time through `tmp`. -/
def permuteCode {m : Nat} (positions : Vector Nat m) (n : Nat) (dst src tmp : Reg) :
    List Instr :=
  [.logicImm .and dst src 0] ++ (List.range m).flatMap fun j =>
    shrFrom tmp src (n - positions.getD j 1) ++
      ([.logicImm .and tmp tmp 1] : List Instr) ++ placeBit tmp (m - 1 - j) ++
      ([.logic .xor dst dst tmp] : List Instr)

end VG.Impl.TripleDes.RISCV64
