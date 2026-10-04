import VerifiedGarbage.Impl.Rc2.X86.ExpandKey
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Rc2.PiLit

namespace VG.Impl.Rc2.X86

open VG.X86

/-- `piStep`, reading PITABLE from its packed table (`Rc2.piTable_getD`). -/
def piStepLit (i : Nat) : List Instr :=
  selectMask i ++
    ([.alu .and .edx (.imm ((BitVec.ofNat 8 (VG.Rc2.piNat i)).setWidth 32)),
      .alu .or .ebx (.reg .edx)] : List Instr)

/-- `piLookup`, reading PITABLE from its packed table. -/
def piLookupLit : List Instr :=
  ([.alu .and .eax (.imm 255), imm .ebx 0] : List Instr) ++
    (List.range 256).flatMap piStepLit ++ ([rr .eax .ebx] : List Instr)

materialize_value piLookupLit

/-- The literal of `piLookup`, evaluated through the packed PITABLE. -/
noncomputable abbrev piLookup.lit : List Instr := piLookupLit.lit

theorem piLookup.lit_eq : piLookup = piLookup.lit := by
  have : piStep = piStepLit := by
    funext i; simp only [piStep, piStepLit, VG.Rc2.piTable_getD]
  refine Eq.trans ?_ piLookupLit.lit_eq
  simp only [piLookup, piLookupLit, this]

materialize_code expandKey

end VG.Impl.Rc2.X86
