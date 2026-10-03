import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Rc2.PiLit
import VerifiedGarbage.Impl.Rc2.Arm.Block
import VerifiedGarbage.Impl.Rc2.Arm.ExpandKey

namespace VG.Impl.Rc2.Arm

open VG.Arm

/-- `piStep`, reading PITABLE from its packed table (`Rc2.piTable_getD`). -/
def piStepLit (i : Nat) : List Instr :=
  selectMask i ++
    ([imm .r10 (BitVec.ofNat 8 (VG.Rc2.piNat i)).toNat,
      .dp .and .r11 .r11 (.reg .r10), .dp .orr .r3 .r3 (.reg .r11)] : List Instr)

/-- `piLookup`, reading PITABLE from its packed table. -/
def piLookupLit : List Instr :=
  mask .r12 8 ++ [imm .r3 0] ++ (List.range 256).flatMap piStepLit ++ [rr .r12 .r3]

materialize_value piLookupLit

/-- The literal of `piLookup`, evaluated through the packed PITABLE. -/
noncomputable abbrev piLookup.lit : List Instr := piLookupLit.lit

theorem piLookup.lit_eq : piLookup = piLookup.lit := by
  have : piStep = piStepLit := by
    funext i; simp only [piStep, piStepLit, VG.Rc2.piTable_getD]
  refine Eq.trans ?_ piLookupLit.lit_eq
  simp only [piLookup, piLookupLit, this]

materialize_value keyLookup

materialize_code encryptBlock
materialize_code decryptBlock

materialize_code expandKey

end VG.Impl.Rc2.Arm
