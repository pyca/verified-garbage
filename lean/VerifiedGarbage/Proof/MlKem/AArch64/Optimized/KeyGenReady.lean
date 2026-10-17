module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenRow
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Ready

/-! # The fused row's arithmetic preconditions follow from the keygen invariant -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
variable {P : KemLay}

def rowF (s₀ s : State) (fg : Nat × Nat) : Poly := polyAt s.mem (kA s₀ 3+BitVec.ofNat 64 fg.1)
def rowG (s₀ s : State) (fg : Nat × Nat) : Poly := polyAt s.mem (kA s₀ 3+BitVec.ofNat 64 fg.2)

theorem row_sum {s₀ s : State} {mB : Mem} {v : BitVec 64} {i : Nat}
    (hi : i < P.k) (h : TL P s₀ mB v i s) :
    Dot.polySum (rowTerms P i) (rowF s₀ s) (rowG s₀ s) =
      KPke.dotK (aM P s₀ mB i) (KPke.kgS P.params (dB s₀)) P.k := by
  apply Optimized.polySum_dotK
  · intro j hj
    exact (h.c.ahat (P.k*i+j) (ij_lt hi hj)).2
  · intro j hj
    exact (h.sp j hj).2

theorem row_ready {s₀ s : State} (hp : Pre P s₀) {mB : Mem} {v : BitVec 64} {i : Nat}
    (hi : i < P.k) (h : TL P s₀ mB v i s)
    (ht : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (hc : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (ha : (polyRegion (s.gpr .x28+BitVec.ofNat 64 (TP P))).Disjoint ⟨s.syms "VG_MLKEM_GAMMA",512⟩) :
    Dot.Ready s (s.gpr .x28+BitVec.ofNat 64 (TP P)) (s.syms "VG_MLKEM_GAMMA")
      (rowTerms P i) (rowF s₀ s) (rowG s₀ s) := by
  have hw := hp.wf
  have term : ∀ fg ∈ rowTerms P i, ∃ j<P.k, fg=(aOff P i j,sOff P j) := by
    intro fg hf
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hf
    exact ⟨j,List.mem_range.mp hj,rfl⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,ha,hc,ht⟩
  · simp only [rowTerms,List.length_map,List.length_range]; exact hw.facts.2.1
  · intro fg hf; obtain ⟨j,hj,rfl⟩ := term fg hf; have hij := ij_lt hi hj; change aOff P i j < 65536; lom
  · intro fg hf; obtain ⟨j,hj,rfl⟩ := term fg hf; have hij := ij_lt hi hj; change sOff P j < 65536; lom
  · intro fg hf; obtain ⟨j,hj,rfl⟩ := term fg hf
    have hij := ij_lt hi hj
    rw [h.c.kb.x28]
    exact ⟨(h.c.ahat (P.k*i+j) (ij_lt hi hj)).1,rfl⟩
  · intro fg hf; obtain ⟨j,hj,rfl⟩ := term fg hf
    have hij := ij_lt hi hj
    rw [h.c.kb.x28]
    exact ⟨(h.sp j hj).1,rfl⟩
  · intro fg hf; obtain ⟨j,hj,rfl⟩ := term fg hf
    have hij := ij_lt hi hj
    rw [h.c.kb.x28]
    exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by lom)
  · intro fg hf; obtain ⟨j,hj,rfl⟩ := term fg hf
    have hij := ij_lt hi hj
    rw [h.c.kb.x28]
    exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by lom)
  · intro fg hf; obtain ⟨j,hj,rfl⟩ := term fg hf
    have hij := ij_lt hi hj
    rw [h.c.kb.x28]
    exact cov_r hp h.c.kb (b := 3) (by decide) (by kl)
  · intro fg hf; obtain ⟨j,hj,rfl⟩ := term fg hf
    have hij := ij_lt hi hj
    rw [h.c.kb.x28]
    exact cov_r hp h.c.kb (b := 3) (by decide) (by kl)
  · rw [h.c.kb.x28]
    exact cov_w hp h.c.kb (b := 3) (by decide) (by kl)

end VG.Proof.MlKem.AArch64.KeyGen
