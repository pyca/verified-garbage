import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.RestBase
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.LazyInv
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedEntry

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call (Ptr)
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt PolyIs bitPack simpleBitPack)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.KeyGen (t1K t0K Small)
open VG.Proof.MlDsa.AArch64.Optimized (PosPolyIs)

/-- Key-generation progress with positive redundant transform values. The
untransformed secrets and every encoded key byte retain their old meanings. -/
structure PositiveKR (p : Params) (σ : State) (A : Nat → Poly) (S : Nat → IPoly) (R : BitVec 64) (np nj nr : Nat)
    (s : State) : Prop where
  kc : KC p σ s
  x24 : s.gpr .x24 = R
  good : Good p σ (p.k * p.ℓ) (p.ℓ + p.k) A S R
  small : ∀ r < p.ℓ + p.k, Small p.η (S r)
  aS : ∀ e < p.k * p.ℓ, PolyIs s.mem (pa s (aP e)) (A e)
  s2 : ∀ i < p.k, PolyIs s.mem (pa s (sP p (p.ℓ + i))) (toRq (S (p.ℓ + i)))
  s1 : ∀ j < p.ℓ, if j < nj then PosPolyIs s.mem (pa s (sP p j)) (ntt (toRq (S j)))
    else PolyIs s.mem (pa s (sP p j)) (toRq (S j))
  pk0 : bytesAt s.mem (pa s (.x26, 0)) 32 = rhoOf p σ
  sk0 : bytesAt s.mem (pa s (.x27, 0)) 32 = rhoOf p σ
  sk1 : bytesAt s.mem (pa s (.x27, 32)) 32 = kOf p σ
  packs : ∀ r < np, bytesAt s.mem (pa s (.x27, 128 + lenS p * r)) (lenS p) = bitPack (S r) p.η p.η
  rows : ∀ i < nr, bytesAt s.mem (pa s (.x26, 32 + 320 * i)) 320 = simpleBitPack (t1K p A S i) 1023 ∧
    bytesAt s.mem (pa s (.x27, oT0 p + 416 * i)) 416 = bitPack (t0K p A S i) 4095 4096

theorem PositiveKR.keep {p : Params} (hF : PFacts p) {S' : Nat} {σ : State} (hp : kgPre p S' σ) {A : Nat → Poly}
    {S : Nat → IPoly} {R : BitVec 64} {np nj nr : Nat} {s s' : State} (h : PositiveKR p σ A S R np nj nr s)
    {ws : List (Ptr × Nat)} (hP : PPostB S' s s' ws) (h24 : s'.gpr .x24 = s.gpr .x24) (hc : KRChk p np nj nr ws) :
    PositiveKR p σ A S R np nj nr s' := by
  have L := h.kc.lay hF hp
  exact ⟨h.kc.step hF hp hP hc.kc, h24.trans h.x24, h.good, h.small,
    fun e he => L.keepPoly hP (hc.aS e he) (h.aS e he), fun i hi => L.keepPoly hP (hc.s2 i hi) (h.s2 i hi),
    fun j hj => by
      have hv := h.s1 j hj
      by_cases hjn : j < nj
      · simp only [ite_eq_left hjn] at hv ⊢
        exact Sign.keepPosPoly L hP (hc.s1 j hj) hv
      · simp only [ite_eq_right hjn] at hv ⊢
        exact L.keepPoly hP (hc.s1 j hj) hv, by rw [L.keepBytes hP hc.pk0]; exact h.pk0,
    by rw [L.keepBytes hP hc.sk0]; exact h.sk0, by rw [L.keepBytes hP hc.sk1]; exact h.sk1,
    fun r hr => by rw [L.keepBytes hP (hc.packs r hr)]; exact h.packs r hr,
    fun i hi => ⟨by rw [L.keepBytes hP (hc.rows i hi).1]; exact (h.rows i hi).1,
      by rw [L.keepBytes hP (hc.rows i hi).2]; exact (h.rows i hi).2⟩⟩


theorem PositiveKR.of_canonical {p : Params} {σ s : State} {A : Nat → Poly}
    {S : Nat → IPoly} {R : BitVec 64} {np nj nr : Nat}
    (h : KR p σ A S R np nj nr s) : PositiveKR p σ A S R np nj nr s := by
  refine ⟨h.kc,h.x24,h.good,h.small,h.aS,h.s2,?_,h.pk0,h.sk0,h.sk1,h.packs,h.rows⟩
  intro j hj
  have hv := h.s1 j hj
  split <;> rename_i hc
  · rw [ite_eq_left hc] at hv
    exact PosPolyIs.of_canonical hv
  · simpa only [ite_eq_right hc] using hv

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
