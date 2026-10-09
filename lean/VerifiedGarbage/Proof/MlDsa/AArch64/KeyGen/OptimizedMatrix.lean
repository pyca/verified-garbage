import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.OptimizedMatrix
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedMatrixFour
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedMatrixTwo

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.KeyGen.Optimized
open VG.Impl.MlDsa.AArch64.Call
open VG.Spec.MlDsa (Params)

theorem matrixGroup_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p)
    {σ : State} (hp : kgPre p S σ) {g : Nat} (hg : 4*g+4≤p.k*p.ℓ) {s : State}
    (hs : KSamp p σ (4*g) 0 s) (hr : MatrixPrefixes p σ 4 s) :
    WP isa (matrixGroup P p g) s fun t => KSamp p σ (4*g+4) 0 t ∧ MatrixPrefixes p σ 4 t := by
  unfold matrixGroup
  apply WP.seq
  exact WP.mono (matrixNonces_ok hF hp hg (Nat.le_refl _) hs hr)
    fun _ ht => matrixFour_ok hP hF hp hg ht.1 ht.2

theorem matrixTwoPhase_ok {S : Nat} (hS : S<2^64) {cd : Prog isa}
    (C : CalleeOk S cd (Spec.MlDsa.rejNTT2Contract AArch64.abi S))
    {p : Params} (hF : PFacts p) {σ : State} (hp : kgPre p S σ)
    {e : Nat} (he : e+2≤p.k*p.ℓ) {s : State} (hs : KSamp p σ e 0 s) (hr : MatrixPrefixes p σ 4 s) :
    WP isa (matrixTwo cd p e) s fun t => KSamp p σ (e+2) 0 t ∧ MatrixPrefixes p σ 4 t := by
  unfold matrixTwo
  apply WP.seq
  exact WP.mono (matrixNonces_ok hF hp he (by decide) hs hr)
    fun _ ht => matrixTwo_ok hS C hF hp he ht.1 ht.2

theorem matrixWith_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {cd : Prog isa}
    (C : CalleeOk S cd (Spec.MlDsa.rejNTT2Contract AArch64.abi S))
    {p : Params} (hF : PFacts p) (hm : p.k*p.ℓ%4=0 ∨ p.k*p.ℓ%4=2)
    {σ : State} (hp : kgPre p S σ) {s : State} (hs : K1 p σ s) (h24 : s.gpr .x24=1) :
    WP isa (matrixWith cd P p) s (KSamp p σ (p.k*p.ℓ) 0) := by
  unfold matrixWith
  apply WP.seq
  refine WP.mono (matrixPrefixes_ok hF hp (KSamp.zero hs h24)) fun u hu => ?_
  apply WP.seq
  have loop := seqR_ok (I := fun j t => KSamp p σ (4*j) 0 t ∧ MatrixPrefixes p σ 4 t)
    (p.k*p.ℓ/4) 0
    (fun j _ hj t ht => by simpa only [Nat.mul_add,Nat.mul_one] using
      (matrixGroup_ok hP hF hp (by omega) ht.1 ht.2)) u hu
  refine WP.mono loop fun t ht => ?_
  simp only [Nat.zero_add] at ht
  rcases hm with hm | hm
  · rw [VG.Proof.MlDsa.KeyGen.ifn (by omega),hm]
    exact WP.block_nil (by simpa only [show 4*(p.k*p.ℓ/4)=p.k*p.ℓ by omega] using ht.1)
  · rw [VG.Proof.MlDsa.KeyGen.ifp hm]
    refine WP.mono (matrixTwoPhase_ok hP.s64 C hF hp (by omega) ht.1 ht.2) fun _ hv => ?_
    simpa only [show 4*(p.k*p.ℓ/4)+2=p.k*p.ℓ by omega] using hv.1

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
