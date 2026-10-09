import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedDot
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.RestRow

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Impl.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.KeyGen (dotK)

private theorem poly_addr (s : State) (b j : Nat) :
    pa s (VG.Impl.MlDsa.AArch64.Call.sc (oP (b+j))) =
      pa s (VG.Impl.MlDsa.AArch64.Call.sc (oP b))+BitVec.ofNat 64 (1024*j) := by
  simp only [pa,oP,Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc]

/-- The fused inverse consumes the lazy secret transforms directly. Its
canonical row is the same field sum as the scalar reference key generator. -/
theorem dotRow_value {p : Params} (hF : PFacts p) {S' : Nat} {σ s : State}
    (hp : kgPre p S' σ) {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {i : Nat}
    (hi : i<p.k) (h : PositiveKR p σ A S R (p.ℓ+p.k) p.ℓ i s)
    (roots : Sign.StaticRoots S' s) :
    WP isa (Impl.MlDsa.AArch64.KeyGen.Optimized.dotRow p i) s fun t =>
      PositiveKR p σ A S R (p.ℓ+p.k) p.ℓ i t ∧ Sign.StaticRoots S' t ∧
      PolyIs t.mem (pa t (tP p)) (nttInv (dotK p A S i p.ℓ)) := by
  have hA j (hj : j<p.ℓ) : PolyIs s.mem
      (pa s (aP (p.ℓ*i))+BitVec.ofNat 64 (1024*j)) (A (p.ℓ*i+j)) := by
    have hv := h.aS _ (idx_lt hi hj)
    change PolyIs s.mem (pa s (VG.Impl.MlDsa.AArch64.Call.sc (oP (p.ℓ*i+j)))) _ at hv
    rw [poly_addr] at hv
    exact hv
  have hB j (hj : j<p.ℓ) : PosPolyIs s.mem
      (pa s (sP p 0)+BitVec.ofNat 64 (1024*j)) (ntt (toRq (S j))) := by
    have hv := h.s1 j hj
    simp only [ite_eq_left hj] at hv
    change PosPolyIs s.mem (pa s (VG.Impl.MlDsa.AArch64.Call.sc (oP (p.k*p.ℓ+j)))) _ at hv
    rw [poly_addr] at hv
    simpa only [sP,Nat.add_zero] using hv
  refine WP.mono (optimizedDot_ok hF (optimizedDotChk_ok hF i hi) hp h.kc roots
    (fun j hj => (PosPolyIs.of_canonical (hA j hj)).bound)
    (fun j hj => (hB j hj).bound)) fun t ⟨_,rt,h24,hP,hv⟩ => ?_
  have hc : KRChk p (p.ℓ+p.k) p.ℓ i (dotWrites p i) := by
    have hk := hF.k; have hl := hF.l; have hs := hF.scr
    exact KRChk.append (ws₁ := [_])
      (KRChk.x28 hF (Nat.le_refl _) (Nat.le_of_lt hi) (by simp only [SV, oP]; omega) (.inr (Nat.le_refl _))
        (by rw [hs]; simp only [oP]; omega))
      (KRChk.x28 hF (Nat.le_refl _) (Nat.le_of_lt hi) (by simp only [SV, oSS]; omega)
        (.inl (by simp only [oSS, oP]; omega)) (by rw [hs]; simp only [oSS]; omega))
  refine ⟨h.keep hF hp hP h24 hc,rt,?_⟩
  have he : dotNTT
      (fun j => polyAt s.mem (pa s (aP (p.ℓ*i))+BitVec.ofNat 64 (1024*j)))
      (fun j => polyAt s.mem (pa s (sP p 0)+BitVec.ofNat 64 (1024*j))) p.ℓ = dotK p A S i p.ℓ := by
    unfold dotNTT dotK
    apply congrArg (List.foldl add zero)
    apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    dsimp only
    rw [(hA j hj).2,(hB j hj).value]
  simpa only [he] using hv

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
