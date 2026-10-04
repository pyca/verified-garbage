import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Rc2.PiLit
import VerifiedGarbage.Impl.Rc2.X86_64.Block
import VerifiedGarbage.Impl.Rc2.X86_64.ExpandKey

/-! # Literal RC2 programs for kernel-evaluated checks -/

namespace VG.Impl.Rc2.X86_64.Sse2

open VG.X86_64 VG.Impl.Rc2.X86_64

/-- `piValues`, reading PITABLE from its packed table (`Rc2.piTable_getD`). -/
def piValuesLit (n : Nat) : BitVec 128 :=
  ofWords fun j => (BitVec.ofNat 8 (VG.Rc2.piNat (8 * n + j))).setWidth 16

/-- `piStep`, reading PITABLE from its packed table. -/
def piStepLit (n : Nat) : List Instr := loadConst .xmm4 (piValuesLit n) ++ select

/-- `piLookup`, reading PITABLE from its packed table. -/
def piLookupLit : List Instr :=
  start .r8 255 ++ (List.range 32).flatMap piStepLit ++ finish .r8

materialize_value piLookupLit

/-- The literal of `piLookup`, evaluated through the packed PITABLE. -/
noncomputable abbrev piLookup.lit : List Instr := piLookupLit.lit

theorem piLookup.lit_eq : piLookup = piLookup.lit := by
  have : piStep = piStepLit := by
    funext n; simp only [piStep, piStepLit, piValues, piValuesLit, VG.Rc2.piTable_getD]
  refine Eq.trans ?_ piLookupLit.lit_eq
  simp only [piLookup, piLookupLit, this]

end VG.Impl.Rc2.X86_64.Sse2

namespace VG

materialize_code Impl.Rc2.X86_64.encryptBlock
materialize_code Impl.Rc2.X86_64.decryptBlock
materialize_code Impl.Rc2.X86_64.expandKey

end VG
