module
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAddTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeStore
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeInvariant

import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Production
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Timing
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTree
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTableTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoadTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeFetch
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeStep
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeArithmetic
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd

/-! The public tree carries exact paired field values and fixed loop counters. -/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

abbrev RegCT (rs : List Reg) (c : Prog isa) :=
  ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs rs)) c

 theorem tableStore_preserves (K : WinCfg) {r : Reg} (hr : r≠.x4) :
    ∀ i∈instrs (.block (Jacobian.tableStore K) : Prog isa), clobbers i r = false := by
  intro i hi
  change i∈(List.range 12).flatMap (fun j => [ld .x4 (K.R.x+8*j),.str .x .x4 .x20 (8*j)]) at hi
  obtain ⟨j,_,hi⟩ := List.mem_flatMap.mp hi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl
  · exact clobbers_eq_false (by simpa [dsts, dstOf, ld] using hr)
  · exact clobbers_eq_false (by simp [dsts, dstOf])

 theorem relCT_keepControls {P Q : State → State → Prop} {c : Prog isa} {a b : BitVec 64}
    (h : RelCT isa P c Q) (hc : ∀ r∈[Reg.x19,Reg.x20], ∀ i∈instrs c, clobbers i r = false) :
    RelCT isa (fun s t => P s t ∧ s.gpr .x19=a ∧ t.gpr .x19=a ∧ s.gpr .x20=b ∧ t.gpr .x20=b) c
      (fun s t => Q s t ∧ s.gpr .x19=a ∧ t.gpr .x19=a ∧ s.gpr .x20=b ∧ t.gpr .x20=b) := by
  intro s t ts tt s' t' ⟨hp,s19,t19,s20,t20⟩ es et
  obtain ⟨he,hq⟩ := h _ _ _ _ _ _ hp es et
  exact ⟨he,hq,(Exec.gpr (hc _ (by simp)) es).trans s19,(Exec.gpr (hc _ (by simp)) et).trans t19,
    (Exec.gpr (hc _ (by simp)) es).trans s20,(Exec.gpr (hc _ (by simp)) et).trans t20⟩

end VG.Proof.Weierstrass.AArch64
