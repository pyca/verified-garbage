module

public import VerifiedGarbage.TCB.PPC64LE.Isa

@[expose] public section

namespace VG.Impl.TripleDes.PPC64LE

open VG.PPC64LE

/-- `mr d, n` (`or d, n, n`). -/
def rr (d n : Reg) : Instr := .logic .or d n n

def imm (r : Reg) (n : Nat) : Instr := .li r n

def shr (r : Reg) (n : Nat) : List Instr := if n = 0 then [] else [.lsr .d r r n]

/-- `d := n >>> k`, as a move when `k = 0`. -/
def shrFrom (d n : Reg) (k : Nat) : List Instr := if k = 0 then [rr d n] else [.lsr .d d n k]

def placeBit (r : Reg) (n : Nat) : List Instr := if n = 0 then [] else [.rotr .d r r (64 - n)]

/-- Keep exactly the low `n` bits with two fixed shifts. -/
def mask (r : Reg) (n : Nat) : List Instr := [.lsl r r (64 - n), .lsr .d r r (64 - n)]

/-- A fixed bit permutation of the low `n` bits of `src` into the low `m`
bits of `dst`, one bit at a time through `tmp`, masked by the 1 in `bit`. -/
def permuteCode {m : Nat} (positions : Vector Nat m) (n : Nat) (dst src tmp bit : Reg) :
    List Instr :=
  [imm dst 0, imm bit 1] ++ (List.range m).flatMap fun j =>
    shrFrom tmp src (n - positions.getD j 1) ++
      ([.logic .and tmp tmp bit] : List Instr) ++ placeBit tmp (m - 1 - j) ++
      ([.logic .xor dst dst tmp] : List Instr)

end VG.Impl.TripleDes.PPC64LE
