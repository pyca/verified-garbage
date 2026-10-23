module

import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Recode
public import VerifiedGarbage.Impl.Ed448.PublicTable
public import VerifiedGarbage.Impl.Ed448.AArch64.VerifyWindow

/-! Eight projective odd multiples of the public key and sixty-four affine
odd multiples of the fixed base. No inversions enter the runtime table. -/

@[expose] public section

namespace VG.Impl.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (slot ld st)
open VG.Impl.X448.AArch64.Base (constSlot)

/-- Normalize the decoded negative X coordinate once. All odd-table X limbs then
have the multiplication output bound, including entry zero. -/
def normalizeKey : Prog isa :=
  .seq (.block (constSlot (slot 20) 1))
    (X448.AArch64.Fast.opsK [.mul (slot 6) (slot 6) (slot 20)])

/-- Save R, store -A as odd entry zero, and initialize field constants. -/
def tableInit : List Instr :=
  Curve448.AArch64.copy RX (slot 8) ++ Curve448.AArch64.copy RY (slot 9) ++
  constSlot (slot 19) 0 ++ constSlot (slot 20) 1 ++
  Curve448.AArch64.copy (slot 3) (slot 6) ++ Curve448.AArch64.copy (slot 4) (slot 7) ++
  constSlot (slot 5) 1 ++ [.movz .x .x19 0 0] ++ tabStore

/-- Keep 2(-A) in slots 6–8, restore -A from entry zero, and start at entry one. -/
def tableStepSetup : List Instr :=
  Point56.copy3 6 3 ++
  (List.range 24).flatMap (fun i =>
    [ld .x4 (TAB+8*i), st .x4 (slot (3+i/8)+8*(i%8))]) ++ [.movz .x .x19 1 0]

def tableBody : Prog isa :=
  .seq Point56.addCall (.block (tabStore ++
    [.addImm .x .x19 .x19 1, .subImm .x .x9 .x19 8]))

def oddTable : Prog isa :=
  .seq (.block tableInit) <| .seq Point56.doubleCall <|
  .seq (.block tableStepSetup) (.loop tableBody (.nonzero .x .x9))

/-- Magnitude divided by two selects the odd multiple with that index. -/
def selectKey : List Instr :=
  [.lsr .x .x11 .x11 1, .lsl .x .x8 .x11 7, .lsl .x .x9 .x11 6,
   .add .x .x8 .x8 .x9, .add .x .x8 .x8 .x3] ++
  (List.range 24).flatMap fun i =>
    [.ldr .x .x4 .x8 (TAB+8*i), st .x4 (slot (6+i/8)+8*(i%8))]

def baseSym : String := "VG_ED448_VERIFY_ODD_BASE"

def baseWord (i : Nat) : BitVec 64 :=
  let e := PublicTable.entry (i/16)
  BitVec.ofNat 64 (((if i%16<8 then e.1 else e.2).val >>> (56*(i%8))) % 2^56)

def baseWords : List (BitVec 64) := (List.range 1024).map baseWord

def baseConsts : List (String × List (BitVec 64)) := [(baseSym,baseWords)]

/-- The public magnitude indexes an immutable affine table. -/
def selectBase : List Instr :=
  [.lsr .x .x11 .x11 1, .adrSym .x8 baseSym, .lsl .x .x9 .x11 7, .add .x .x8 .x8 .x9] ++
  (List.range 16).flatMap fun i =>
    [.ldr .x .x4 .x8 (8*i), st .x4 (slot (6+i/8)+8*(i%8))]

end VG.Impl.Ed448.AArch64.Sparse
