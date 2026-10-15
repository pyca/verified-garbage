module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemNoise
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Fused transposed-matrix products from the encryption invariant -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
variable {P : KemLay} {L : Layout}

def uF (L : Layout) (s₀ s : State) (fg : Nat × Nat) : Poly := polyAt s.mem (sA L s₀ fg.1)
def uG (L : Layout) (s₀ s : State) (fg : Nat × Nat) : Poly := polyAt s.mem (sA L s₀ fg.2)

theorem u_sum {s₀ s : State} {kC co : Nat} {mE mB : Mem} {v : BitVec 64}
    {rv mv : List Byte} {i : Nat} (hi : i<P.k)
    (h : EInv P L s₀ kC co mE mB v rv mv P.k i s) :
    Dot.polySum (uTerms P i) (uF L s₀ s) (uG L s₀ s)=
      KPke.dotK (fun j => aM P L s₀ mB j i) (encY rv) P.k := by
  apply Optimized.polySum_dotK
  · intro j hj; exact (h.a j hj i hi).2
  · intro j hj; exact (h.y j hj).2

theorem u_ready {s₀ s : State} (hp : Pre P L s₀)
    {kC co : Nat} {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte} {i : Nat} (hi : i<P.k)
    (h : EInv P L s₀ kC co mE mB v rv mv P.k i s)
    (ht : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (hc : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (ha : (polyRegion (sA L s₀ (TP P))).Disjoint ⟨s.syms "VG_MLKEM_GAMMA",512⟩) :
    Dot.Ready s (s.gpr .x28+BitVec.ofNat 64 (TP P)) (s.syms "VG_MLKEM_GAMMA")
      (uTerms P i) (uF L s₀ s) (uG L s₀ s) := by
  have hw := hp.wf
  have term : ∀fg∈uTerms P i, ∃j<P.k, fg=(aOff P j i,yOff P j) := by
    intro fg hh
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hh
    exact ⟨j,List.mem_range.mp hj,rfl⟩
  refine fused_ready hp h.kb (po_TP hw) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ht hc ha
  · simpa only [uTerms,List.length_map,List.length_range] using hw.facts.2.1
  · intro fg hh; obtain ⟨j,hj,rfl⟩ := term fg hh; exact po_a hw hj hi
  · intro fg hh; obtain ⟨j,hj,rfl⟩ := term fg hh; exact po_y hw hj
  · intro fg hh; obtain ⟨j,hj,rfl⟩ := term fg hh; exact ⟨(h.a j hj i hi).1,rfl⟩
  · intro fg hh; obtain ⟨j,hj,rfl⟩ := term fg hh; exact ⟨(h.y j hj).1,rfl⟩
  · intro fg hh; obtain ⟨j,hj,rfl⟩ := term fg hh
    have := ij_lt hj hi
    exact .inr (by lom)
  · intro fg hh; obtain ⟨j,hj,rfl⟩ := term fg hh
    exact .inr (by lom)

end VG.Proof.MlKem.AArch64.Kem
