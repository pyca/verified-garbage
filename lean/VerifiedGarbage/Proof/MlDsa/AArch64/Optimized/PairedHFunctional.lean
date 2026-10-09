import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedHintFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowEntryState
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedHintAccess
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedHAllFields
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedHReturnSemantic

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.Paired

structure HResult (s t : State) : Prop where
  keep : Keep entryRegs s t
  fields : HintIs t.mem (s.gpr .x2) 2 ((List.range 2).map fun j =>
    pairedHintPoly s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x3) (Round.arg32 s .x5) j)
  ret : t.gpr .x0=BitVec.ofNat 64
    (hintOnes ((List.range 2).map fun j => pairedHintPoly s.mem (s.gpr .x0) (s.gpr .x1)
      (s.gpr .x2) (s.gpr .x3) (Round.arg32 s .x5) j)+
      if normRq ((List.range 2).map fun j => pairedProduct s.mem (s.gpr .x0) (s.gpr .x1) j)<Round.arg32 s .x5
      then 4294967296 else 0)

theorem pairedHint_functional {s : State} (h : HintSpecPre s) :
    WP isa (selected .h) s (HResult s) := by
  refine WP.mono (pairedHint_machine h) fun t ⟨a,u,ha,hf,hp,hl,ht,hmem,hret⟩ => ?_
  have hg : Round.IsG (Round.arg32 s .x5) := by
    simpa [or_comm,gamma2s,Round.IsG,VG.Impl.MlDsa.AArch64.Round.g32,
      VG.Impl.MlDsa.AArch64.Round.g88,Round.arg32] using h.gamma
  have hgb : 1≤Round.arg32 s .x5 := by rcases hg with hv|hv <;> rw [hv] <;> decide
  have hframe := hintEntry_frame h hf
  have hdata : dataAt u=⟨firstPassMem a.mem (s.gpr .x4) (s.gpr .x0) (s.gpr .x1) 8,0,0⟩ := by
    unfold dataAt
    rw [hp.mem,ha.work,ha.common,ha.secret,hl.flags,hl.count rfl]
  have hgamma : ∀e<4,vword (constantsAt u).gamma e=BitVec.ofNat 32 (Round.arg32 s .x5) := by
    intro e he
    change vword (u.v .v11) e=_
    rw [hl.gamma rfl e he,ha.gamma]
    simp only [Round.arg32,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  have hlower : ∀e<4,vword (constantsAt u).lower e=BitVec.ofNat 32 (Round.arg32 s .x5-1) := by
    intro e he
    change vword (u.v .v9) e=_
    rw [hl.lower e he,ha.bound,h.bound]
    exact bound_sub_one _ hgb
  have hwidth : ∀e<4,vword (constantsAt u).width e=BitVec.ofNat 32 (2*Round.arg32 s .x5-1) := by
    intro e he
    change vword (u.v .v10) e=_
    rw [hl.width e he,ha.bound,h.bound]
    exact bound_width _ hgb
  have hc := h.commonWork.sub_right (Region.sub_prefix (by decide : 2048≤2176))
  have hs := h.secretWork.sub_right (Region.sub_prefix (by decide : 2048≤2176))
  have ho := h.dataWork.symm.sub_left (Region.sub_prefix (by decide : 2048≤2176))
  have hx := h.auxWork.symm.sub_left (Region.sub_prefix (by decide : 2048≤2176))
  have hfields := hPass_all_fields hg (constantsAt u) hgamma hc hs ho hx h.auxData hframe.products hframe.decomposed 0 0
  have hvalue := hPass_return hg (constantsAt u) hgamma hlower hwidth hc hs ho hx h.auxData hframe.products hframe.decomposed
  dsimp only at hfields hvalue
  have hhints : ((List.range 2).map fun j => pairedHintPoly a.mem (s.gpr .x0) (s.gpr .x1)
      (s.gpr .x2) (s.gpr .x3) (Round.arg32 s .x5) j)=
      ((List.range 2).map fun j => pairedHintPoly s.mem (s.gpr .x0) (s.gpr .x1)
      (s.gpr .x2) (s.gpr .x3) (Round.arg32 s .x5) j) := by
    apply List.map_congr_left
    intro j hj
    exact hframe.hints j (List.mem_range.mp hj)
  have hproducts : ((List.range 2).map fun j => pairedProduct a.mem (s.gpr .x0) (s.gpr .x1) j)=
      ((List.range 2).map fun j => pairedProduct s.mem (s.gpr .x0) (s.gpr .x1) j) := by
    apply List.map_congr_left
    intro j hj
    exact hframe.product j (List.mem_range.mp hj)
  rw [hdata] at hmem hret
  refine ⟨ht,?_,?_⟩
  · rw [hmem,←hhints]
    exact hfields
  · rw [hret]
    change Response.hintFinishValue _ _=_
    rw [hvalue,hhints,hproducts]

end VG.Proof.MlDsa.AArch64.Optimized.Paired
