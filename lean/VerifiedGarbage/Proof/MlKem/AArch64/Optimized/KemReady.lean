module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemDecode
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Ready
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.DotSpec
import VerifiedGarbage.Proof.MlKem.AArch64.KemEnc

/-! # Establish the fused arithmetic preconditions from KEM buffer facts -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
variable {P : KemLay} {L : Layout}

theorem fused_ready {s₀ s : State} (hp : Pre P L s₀) (hk : KB P L s₀ s)
    {off : Nat} (ho : PO P off) {terms : List (Nat × Nat)} {F G : (Nat × Nat) → Poly}
    (hn : terms.length≤4)
    (hf : ∀ fg∈terms, PO P fg.1) (hg : ∀ fg∈terms, PO P fg.2)
    (hF : ∀ fg∈terms, PolyIs s.mem (sA L s₀ fg.1) (F fg))
    (hG : ∀ fg∈terms, PolyIs s.mem (sA L s₀ fg.2) (G fg))
    (df : ∀ fg∈terms, off+1024≤fg.1 ∨ fg.1+1024≤off)
    (dg : ∀ fg∈terms, off+1024≤fg.2 ∨ fg.2+1024≤off)
    (ht : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (hc : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (ha : (polyRegion (sA L s₀ off)).Disjoint ⟨s.syms "VG_MLKEM_GAMMA",512⟩) :
    Dot.Ready s (s.gpr .x28+BitVec.ofNat 64 off) (s.syms "VG_MLKEM_GAMMA") terms F G := by
  refine ⟨hn,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,hc,ht⟩
  · intro fg hh; have := (hf fg hh).le; kom
  · intro fg hh; have := (hg fg hh).le; kom
  · intro fg hh; rw [e28 hk]; exact hF fg hh
  · intro fg hh; rw [e28 hk]; exact hG fg hh
  · intro fg hh; rw [e28 hk,e28 hk]; exact papart hp ho (hf fg hh) (df fg hh)
  · intro fg hh; rw [e28 hk,e28 hk]; exact papart hp ho (hg fg hh) (dg fg hh)
  · intro fg hh; rw [e28 hk]; exact cov_sr hp hk (hf fg hh).le
  · intro fg hh; rw [e28 hk]; exact cov_sr hp hk (hg fg hh).le
  · rw [e28 hk]; exact cov_s hp hk ho.le
  · rwa [e28 hk]

def decodedTerms (P : KemLay) : List (Nat × Nat) :=
  (List.range P.k).map fun j => (aOff P 0 j,yOff P j)

def decodedF (T : Nat → Poly) (fg : Nat × Nat) : Poly := T ((fg.1-AH)/1024)
def decodedG (P : KemLay) (Y : Nat → Poly) (fg : Nat × Nat) : Poly := Y ((fg.2-YH P)/1024)

theorem decoded_sum (T Y : Nat → Poly) :
    Dot.polySum (decodedTerms P) (decodedF T) (decodedG P Y)=KPke.dotK T Y P.k := by
  apply Optimized.polySum_dotK
  · intro j hj; simp [decodedF,aOff]
  · intro j hj; simp [decodedG,yOff]


theorem decoded_ready {s₀ s : State} (hp : Pre P L s₀)
    {mD : Mem} {T Y : Nat → Poly} {v : BitVec 64}
    (h : DecodeInv P L s₀ mD T Y v P.k s)
    (ht : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (hc : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (ha : (polyRegion (sA L s₀ (TP P))).Disjoint ⟨s.syms "VG_MLKEM_GAMMA",512⟩) :
    Dot.Ready s (s.gpr .x28+BitVec.ofNat 64 (TP P)) (s.syms "VG_MLKEM_GAMMA")
      (decodedTerms P) (decodedF T) (decodedG P Y) := by
  have hw := hp.wf
  have h0 : 0<P.k := hw.facts.1
  have term : ∀ fg∈decodedTerms P, ∃ j<P.k, fg=(aOff P 0 j,yOff P j) := by
    intro fg hh
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hh
    exact ⟨j,List.mem_range.mp hj,rfl⟩
  refine fused_ready hp h.kb (po_TP hw) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ht hc ha
  · simpa only [decodedTerms,List.length_map,List.length_range] using hw.facts.2.1
  · intro fg hh; obtain ⟨j,hj,rfl⟩ := term fg hh; exact po_a hw h0 hj
  · intro fg hh; obtain ⟨j,hj,rfl⟩ := term fg hh; exact po_y hw hj
  · intro fg hh; obtain ⟨j,hj,rfl⟩ := term fg hh
    simpa only [decodedF,aOff,Nat.mul_zero,Nat.zero_add,Nat.add_sub_cancel_left,
      Nat.mul_div_cancel_left _ (by decide : 0<1024)] using h.decoded j hj
  · intro fg hh; obtain ⟨j,hj,rfl⟩ := term fg hh
    simpa only [decodedG,yOff,Nat.add_sub_cancel_left,
      Nat.mul_div_cancel_left _ (by decide : 0<1024)] using h.y j hj
  · intro fg hh; obtain ⟨j,hj,rfl⟩ := term fg hh
    have := ij_lt h0 hj
    exact .inr (by lom)
  · intro fg hh; obtain ⟨j,hj,rfl⟩ := term fg hh
    exact .inr (by lom)

end VG.Proof.MlKem.AArch64.Kem
