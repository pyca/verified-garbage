module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ExponentCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ExponentCT
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega

/-! Compose Montgomery constants and exponent preparation timing proofs. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.Ffdh.AArch64.ParameterCandidate

theorem primeConstants_exponent (M : Mont) {p : PrimeParams} {s : State} (h : PrimeR2Ready p s) :
    WP isa (seqs (Impl.Dsa.AArch64.Generation.primeConstants M.mm)) s (ExponentBefore p) := by
  obtain ⟨hw, hi, hn, hone, hr2⟩ := h
  refine WP.mono (primeConstants_ok M hw hn p.odd (by have := p.n3; omega) hi hone hr2)
    fun t ⟨ht, _, _, _, _, hf, _⟩ => ?_
  obtain ⟨_, _, hN⟩ := mp_fix hf hw.scr.nowrap hw.hZ
  exact ⟨ht, hN.trans hn⟩

theorem primeSetup_ct (M : Mont) : RelCT isa (Two PrimeSetupBefore)
    (Impl.Dsa.AArch64.Generation.primeSetup M.mm) (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.primeSetup
  refine RelCT.seq (two_post (primeR2_ct M) (fun _ _ h => primeR2_ready M h)) ?_
  exact RelCT.seqs_append (by simp [Impl.Dsa.AArch64.Generation.primeConstants]) (by simp [expSetup, lowWord])
    (RelCT.seq (two_post (primeConstants_ct M) (fun _ _ h => primeConstants_exponent M h)) primeExponent_ct)

end VG.Proof.Dsa.AArch64.Generation
