import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedZEntryFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedZAccess
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedZAllFields
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedZReturnSemantic

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.Paired

structure ZResult (s t : State) : Prop where
  keep : Keep entryRegs s t
  fields : ∀j<2,CenteredReduced t.mem (pairPolyPtr (s.gpr .x2) j) ∧
    signedPolyAt t.mem (pairPolyPtr (s.gpr .x2) j)=add (polyAt s.mem (pairPolyPtr (s.gpr .x2) j))
      (pairedProduct s.mem (s.gpr .x0) (s.gpr .x1) j)
  ret : t.gpr .x0=if normRq ((List.range 2).map fun j => add (polyAt s.mem (pairPolyPtr (s.gpr .x2) j))
    (pairedProduct s.mem (s.gpr .x0) (s.gpr .x1) j))<Round.arg32 s .x6 then 1 else 0

theorem pairedZ_functional {s : State} (h : ZSpecPre s) :
    WP isa (selected .z) s (ZResult s) := by
  refine WP.mono (pairedZ_machine h) fun t ⟨a,u,ha,hf,hp,hl,ht,hmem,hret⟩ => ?_
  have hframe := zEntry_frame h hf
  have hdata : dataAt u=⟨firstPassMem a.mem (s.gpr .x4) (s.gpr .x0) (s.gpr .x1) 8,0,u.v .v14⟩ := by
    unfold dataAt
    rw [hp.mem,ha.work,ha.common,ha.secret,hl.flags]
  have hlower : ∀e<4,vword (constantsAt u).lower e=BitVec.ofNat 32 (Round.arg32 s .x6-1) := by
    intro e he
    change vword (u.v .v9) e=_
    rw [hl.lower e he,ha.bound]
    exact bound_sub_one _ h.boundLow
  have hwidth : ∀e<4,vword (constantsAt u).width e=BitVec.ofNat 32 (2*Round.arg32 s .x6-1) := by
    intro e he
    change vword (u.v .v10) e=_
    rw [hl.width e he,ha.bound]
    exact bound_width _ h.boundLow
  have hc := h.commonWork.sub_right (Region.sub_prefix (by decide : 2048≤2176))
  have hs := h.secretWork.sub_right (Region.sub_prefix (by decide : 2048≤2176))
  have ho := h.dataWork.symm.sub_left (Region.sub_prefix (by decide : 2048≤2176))
  have hfields := zPass_all_fields (aux:=s.gpr .x3) (constantsAt u) hc hs ho hframe.products hframe.data 0 (u.v .v14)
  have hvalue := zPass_return (aux:=s.gpr .x3) (constantsAt u) hlower hwidth h.boundLow h.boundHigh
    hc hs ho hframe.products hframe.data (u.v .v14)
  dsimp only at hfields hvalue
  rw [hdata] at hmem hret
  refine ⟨ht,?_,?_⟩
  · intro j hj
    rw [hmem]
    have hv := hfields j hj
    rw [hframe.sum j hj] at hv
    exact hv
  · rw [hret]
    change Response.finishValue _=_
    rw [hvalue]
    have he : ((List.range 2).map fun j => add (polyAt a.mem (pairPolyPtr (s.gpr .x2) j))
        (pairedProduct a.mem (s.gpr .x0) (s.gpr .x1) j))=
        ((List.range 2).map fun j => add (polyAt s.mem (pairPolyPtr (s.gpr .x2) j))
        (pairedProduct s.mem (s.gpr .x0) (s.gpr .x1) j)) := by
      apply List.map_congr_left
      intro j hj
      exact hframe.sum j (List.mem_range.mp hj)
    rw [he]

end VG.Proof.MlDsa.AArch64.Optimized.Paired
