import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothTiming

namespace VG.Proof.Ecdsa.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
theorem booth_sign_a64 (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hcomb : CombCorrect p256 Impl.P256.Booth.comb) (s : State)
    (hs : signAArch64.pre s) :
    ∃ t s', Exec isa Impl.P256.Booth.sign s t s' ∧ abiPreserved s s' ∧ signAArch64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := signWith_ok (p256_ok hI) hL Impl.P256.Booth.comb hcomb (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of he (by lit_decide) (by lit_decide) (by lit_decide) hsv, hpost⟩

theorem booth_sign_verified_of_comb (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hcomb : CombCorrect p256 Impl.P256.Booth.comb) :
    Verified AArch64.target Impl.P256.Booth.sign
      (Spec.Ecdsa.P256.inst.signContract (AArch64.abi.withConsts p256.combConsts)) :=
  Verified.of_correct (booth_sign_a64 hL hI hcomb) booth_sign_ct implies

end VG.Proof.Ecdsa.AArch64

namespace VG.Proof.EcKey.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Ecdsa.AArch64
theorem booth_pk_a64 (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hcomb : CombCorrect p256 Impl.P256.Booth.comb)
    (s : State)
    (hs : pkAArch64.pre s) :
    ∃ t s', Exec isa Impl.P256.Booth.publicKey s t s' ∧ abiPreserved s s' ∧ pkAArch64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := publicKeyWith_ok (p256_ok hI) hL Impl.P256.Booth.comb hcomb (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of he (by lit_decide) (by lit_decide) (by lit_decide) hsv, post_of hpost⟩

theorem booth_pk_verified_of_comb (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hcomb : CombCorrect p256 Impl.P256.Booth.comb) :
    Verified AArch64.target Impl.P256.Booth.publicKey
      (Spec.EcKey.P256.inst.publicKeyContract (AArch64.abi.withConsts p256.combConsts)) :=
  Verified.of_correct (booth_pk_a64 hL hI hcomb) booth_pk_ct implies

end VG.Proof.EcKey.AArch64
