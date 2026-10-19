module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopInit
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoopStep
import VerifiedGarbage.Proof.Framework.Omega

/-! # The complete DSA witness loop implements RSA's blinded primality loop -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.MillerRabin.AArch64

theorem millerRabin_ok (M : Mont) (K : Kernel) {P : PrimeParams} {used : Nat} {s : State}
    (h : PrimeState P used s) (hu : used ≤ P.rand.length) :
    WP isa (Impl.Dsa.AArch64.Generation.millerRabin M.mm K.run P.len P.drawBytes) s
      (PrimeLoopEnd P s (primeRest P 1 0 used)) := by
  unfold Impl.Dsa.AArch64.Generation.millerRabin
  refine WP.seq (WP.mono (primeLoopInit_ok h hu) fun u hI => ?_)
  exact WP.loop
    (fun n t => ∃ i uni used', n = P.rand.length - used' ∧
      PrimeLoopState P s (primeRest P 1 0 used) i uni used' t)
    (fun n t ⟨i, uni, used', hn, hstate⟩ =>
      WP.mono (primeIteration_ok M K hstate) fun t' ht => ht.imp (fun ht => ht)
        fun ⟨he, uni', hnext⟩ =>
          ⟨he, P.rand.length - (used' + P.drawBytes),
            by have := hnext.usedBound; have := P.drawMin; omega,
            i + 1, uni', used' + P.drawBytes, rfl, hnext⟩)
    (P.rand.length - used) u ⟨1, 0, used, rfl, hI⟩

end VG.Proof.Dsa.AArch64.Generation
