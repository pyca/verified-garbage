import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowEntryFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowEntryState
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowAllFields

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.Paired

structure LowResult (s t : State) : Prop where
  keep : Keep entryRegs s t
  fields : ∀j<2,∀i<n,
    (coeffAt t.mem (pairPolyPtr (s.gpr .x2) j) i).toNat=
      (highBits (Round.arg32 s .x5) (pairedDifference s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) j)[i]!).toNat ∧
    (coeffAt t.mem (pairPolyPtr (s.gpr .x3) j) i).toInt=
      lowBits (Round.arg32 s .x5) (pairedDifference s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) j)[i]!
  ret : t.gpr .x0=if normRq ((List.range 2).map fun j => pairedLowPoly (Round.arg32 s .x5)
    (pairedDifference s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) j))<Round.arg32 s .x6 then 1 else 0

theorem pairedLow_functional {s : State} (h : LowSpecPre s) :
    WP isa (selected .r0) s (LowResult s) := by
  refine WP.mono (pairedLow_machine h) fun t ⟨a,b,u,ha,hf,hk,hm,hp,hl,ht,hmem,hret⟩ => ?_
  have hg : Round.IsG (Round.arg32 s .x5) := by
    simpa [or_comm,gamma2s,Round.IsG,VG.Impl.MlDsa.AArch64.Round.g32,
      VG.Impl.MlDsa.AArch64.Round.g88,Round.arg32] using h.gamma
  have hframe := lowEntry_frame h hf
  obtain ⟨hscale,hlower,hwidth⟩ := preparedLow_constants ha hk hl h.boundLow
  have hdata := preparedLow_data ha hk hm hp hl
  have hc := h.commonWork.sub_right (Region.sub_prefix (by decide : 2048≤2176))
  have hs := h.secretWork.sub_right (Region.sub_prefix (by decide : 2048≤2176))
  have ho := h.dataWork.symm.sub_left (Region.sub_prefix (by decide : 2048≤2176))
  have hx := h.auxWork.symm.sub_left (Region.sub_prefix (by decide : 2048≤2176))
  have hfields := lowPass_all_fields hg (lowConstantsAt u) hscale hc hs ho hx h.dataAux
    hframe.products hframe.data 0 (u.v .v14)
  have hvalue := lowPass_return_complete hg (lowConstantsAt u) hscale hlower hwidth h.boundLow h.boundHigh
    hc hs ho hx h.dataAux hframe.products hframe.data (u.v .v14)
  dsimp only at hfields hvalue
  rw [hdata] at hmem hret
  refine ⟨ht,?_,?_⟩
  · intro j hj i hi
    rw [hmem]
    have hv := hfields j hj i hi
    rw [hframe.difference j hj] at hv
    exact hv
  · change t.gpr .x0=_
    rw [hret]
    change Response.finishValue _=_
    rw [hvalue]
    have he : ((List.range 2).map fun j => pairedLowPoly (Round.arg32 s .x5)
        (pairedDifference a.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) j))=
        ((List.range 2).map fun j => pairedLowPoly (Round.arg32 s .x5)
        (pairedDifference s.mem (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) j)) := by
      apply List.map_congr_left
      intro j hj
      rw [hframe.difference j (List.mem_range.mp hj)]
    rw [he]

end VG.Proof.MlDsa.AArch64.Optimized.Paired
