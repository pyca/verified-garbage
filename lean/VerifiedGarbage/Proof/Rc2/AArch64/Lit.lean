import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Rc2.PiLit
import VerifiedGarbage.Impl.Rc2.AArch64.Block
import VerifiedGarbage.Impl.Rc2.AArch64.ExpandKey

/-! # Literal RC2 programs for kernel-evaluated checks -/

namespace VG.Impl.Rc2.AArch64

open VG.AArch64 VG.Impl.Tbl.AArch64

/-- `piLookup`, reading PITABLE from its packed table (`Rc2.piTable_getD`). -/
def piLookupLit : List Instr :=
  loadTable (fun k => BitVec.ofNat 8 (VG.Rc2.piNat k)) ++ [.vop (.dup .b16 .v0 .x8)] ++
    quarters true ++ select true ++ [.umov .w .x8 .v0 0] ++ mask .x8 8

materialize_value piLookupLit

/-- The literal of `piLookup`, evaluated through the packed PITABLE. -/
noncomputable abbrev piLookup.lit : List Instr := piLookupLit.lit

theorem piLookup.lit_eq : piLookup = piLookup.lit := by
  have : (fun k => Spec.Rc2.piTable.getD k 0) = fun k => BitVec.ofNat 8 (VG.Rc2.piNat k) := by
    funext k; exact VG.Rc2.piTable_getD k
  refine Eq.trans ?_ piLookupLit.lit_eq
  simp only [piLookup, piLookupLit, this]

end VG.Impl.Rc2.AArch64

namespace VG

materialize_flat_code Impl.Rc2.AArch64.encryptBlock
materialize_flat_code Impl.Rc2.AArch64.decryptBlock
materialize_flat_code Impl.Rc2.AArch64.expandKey

end VG
