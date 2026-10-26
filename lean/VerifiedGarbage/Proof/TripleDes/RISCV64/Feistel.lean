module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.FeistelLit
public import VerifiedGarbage.Proof.Framework.RISCV64.Linear
public import VerifiedGarbage.Proof.TripleDes.SboxTables
import VerifiedGarbage.Proof.Framework.Lit

/-!
# The round function on RISC-V

`feistel` is checked in three parts by evaluation. Its first part
(`feistelIn`) and its last (`feistelOut`) are linear (the lane domain,
`Framework/RISCV64/Linear.lean`): the first forms each lane's six input bits,
bits of R and of the round key, in `m 0`–`m 5`; the last XORs each output bit
into L at its destination under P. The middle part (`feistelTree`) is checked
over the position-table domain (`Framework/Bitslice/PosTable.lean`), on all
64 inputs of every lane at once: each lane's result is its table
(`laneTables`). The words of constants are external words of the frame.
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Bitslice VG.Impl.TripleDes.RISCV64
open VG.Proof.TripleDes (inputTable)

/-- The frame's first 70 words, read only: slots 15–69 hold the constants. -/
def feiCfg : Cfg := { base := sb, slots := 0, ext := sb, exts := 15 + 55 }

/-- External word `15 + c` is the constant `c`. -/
def constKs : List (Nat × BitVec 64) := (List.range 55).map fun c => (15 + c, roundConsts.getD c 0)

/-- R (input word 0) and the round key (input word 1). -/
def inRegs : List (Reg × Nat) := [(.a2, 0), (.t4, 1)]

/-- Lane `p`'s input bit `k`: bits of R and of the round key, by E. -/
def maskBits (k p : Nat) : List Nat :=
  let n := 6 * (7 - p / 8) + 5 - k
  [32 - Spec.TripleDes.expansion.getD n 1, 64 + (47 - n)]

def maskOuts : List (Reg × (Nat → List Nat)) := (List.range 6).map fun k => (m k, maskBits k)

theorem feistelIn_check :
    check (lanes 64 7) feiCfg (kExt constKs) (instrs feistelIn.lit) (linEnv inRegs)
      (linPost 7 maskOuts) = true := by
  lit_decide

/-- The lanes' tables (input word 0) and L (input word 1). -/
def outRegs : List (Reg × Nat) := [(.t0, 0), (.a1, 1)]

/-- The low lane of the output that P moves to bit `q < 32` of L. -/
def pSrc (q : Nat) : Nat :=
  let t := 32 - Spec.TripleDes.p.getD (31 - q) 1
  8 * (t / 4) + outLane (t / 4) (t % 4)

def outBits (q : Nat) : List Nat := [64 + q] ++ (if q < 32 then [pSrc q, pSrc q + 4] else [])

theorem feistelOut_check :
    check (lanes 64 7) feiCfg (kExt constKs) (instrs feistelOut.lit) (linEnv outRegs)
      (linPost 7 [(.a1, outBits)]) = true := by
  lit_decide

/-- The input bits, the same table at every position. -/
def treeEnv : Env Nat :=
  { reg := fun r => ((List.range 6).find? (fun k => m k == r)).map
      fun k => .v (everywhere 64 64 (inputTable k)),
    slot := fun _ => none }

def treeExt (j : Nat) : Option Nat :=
  if 15 ≤ j then some (spreadConst 64 64 (roundConsts.getD (j - 15) 0).toNat) else none

def treePost (e : Env Nat) : Bool := word (e.reg .t0) == some laneTables

theorem feistelTree_check :
    check (posTables 64 64) feiCfg treeExt (instrs feistelTree.lit) treeEnv treePost = true := by
  lit_decide

end VG.Proof.TripleDes.RISCV64
