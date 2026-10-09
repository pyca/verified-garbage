import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.OptimizedRest
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedFinish
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedPackSecret
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedNtt

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (seqR)
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

/-- The complete optimized arithmetic suffix. Depth premises are syntactic
bounds on the supplied primitive implementations, discharged at registration. -/
theorem rest_ok {P : Prims} {S' : Nat} (hP : PrimsOk P S') {p : Params}
    (hF : PFacts p) {σ s : State} (hp : kgPre p S' σ)
    (h : KSamp p σ (p.k*p.ℓ) (p.ℓ+p.k) s) (roots : Sign.StaticRoots S' s)
    (hdpack : ∀j<p.ℓ+p.k,16*(Impl.MlDsa.AArch64.KeyGen.Optimized.packSecret P p j).aarch64Depth≤S')
    (hdrow : ∀i<p.k,16*(Impl.MlDsa.AArch64.KeyGen.Optimized.row P p i).aarch64Depth≤S') :
    WP isa (Impl.MlDsa.AArch64.KeyGen.Optimized.restWith keccak.callee P p) s (KFin p σ) := by
  unfold Impl.MlDsa.AArch64.KeyGen.Optimized.restWith
  apply WP.seq
  refine WP.mono (roots.phase (show 16*(Code.block copies).aarch64Depth≤S' from by
    change 0≤S'; omega) hP.s64 (copies_ok hF hp h)) fun a ⟨⟨A,T,R,ha⟩,ra⟩ => ?_
  apply WP.seq
  refine WP.mono (seqR_ok (I := fun j t => KR p σ A T R j 0 0 t ∧ Sign.StaticRoots S' t)
    (p.ℓ+p.k) 0 (fun j _ hj t ⟨ht,rt⟩ =>
      rt.phase (hdpack j (by omega)) hP.s64 (packSecret_ok hP hF hp (by omega) ht)) a ⟨ha,ra⟩)
    fun b ⟨hb,rb⟩ => ?_
  simp only [Nat.zero_add] at hb
  apply WP.seq
  refine WP.mono (seqR_ok (I := fun j t => PositiveKR p σ A T R (p.ℓ+p.k) j 0 t ∧ Sign.StaticRoots S' t)
    p.ℓ 0 (fun j _ hj t ⟨ht,rt⟩ => nttSecret_ok hF hp (by omega) ht rt)
    b ⟨PositiveKR.of_canonical hb,rb⟩) fun c ⟨hc,rc⟩ => ?_
  simp only [Nat.zero_add] at hc
  apply WP.seq
  refine WP.mono (seqR_ok (I := fun i t => PositiveKR p σ A T R (p.ℓ+p.k) p.ℓ i t ∧ Sign.StaticRoots S' t)
    p.k 0 (fun i _ hi t ⟨ht,rt⟩ => row_ok hP hF hp (by omega) ht rt (hdrow i (by omega)))
    c ⟨hc,rc⟩) fun d ⟨hd,_⟩ => ?_
  simp only [Nat.zero_add] at hd
  exact (trHash_piece hF hP.s16 hP.s64).ok σ d hp ⟨A,T,R,hd⟩

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
