module
public import VerifiedGarbage.Proof.EcKey.AArch64.Contract
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Contract
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Main

import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothTiming
import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
import VerifiedGarbage.Proof.Ecdsa.AArch64.Verified
import VerifiedGarbage.Proof.EcKey.AArch64.Verified
import VerifiedGarbage.Proof.Ecdsa.AArch64.BoothLit
public import VerifiedGarbage.Impl.P256.Booth
public import VerifiedGarbage.Proof.Ecdsa.Contract
import VerifiedGarbage.Proof.EcKey.AArch64.Lit
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
theorem booth_sign_a64 (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hcomb : CombCorrect p256 Impl.P256.Booth.comb) (s : State)
    (hs : signAArch64.pre s) :
    ∃ t s', Exec isa Impl.P256.Booth.sign s t s' ∧ abiPreserved s s' ∧ signAArch64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := signWith_ok (p256_ok hI) hL Impl.P256.Booth.comb hcomb (pre_of hs)
  -- Named `sign`, so that `lit_decide` reads its literal.
  have he : Exec isa Impl.P256.Booth.sign s t s' := he
  exact ⟨t, s', he, abiPreserved_of he (by lit_decide) (by lit_decide) (by lit_decide) hsv, hpost⟩

theorem booth_sign_verified_of_comb (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hcomb : CombCorrect p256 Impl.P256.Booth.comb) :
    Verified AArch64.target Impl.P256.Booth.sign
      (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P256.inst (AArch64.abi.withConsts p256.combConsts)) :=
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
  -- Named `publicKey`, so that `lit_decide` reads its literal.
  have he : Exec isa Impl.P256.Booth.publicKey s t s' := he
  exact ⟨t, s', he, abiPreserved_of he (by lit_decide) (by lit_decide) (by lit_decide) hsv, post_of hpost⟩

theorem booth_pk_verified_of_comb (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hcomb : CombCorrect p256 Impl.P256.Booth.comb) :
    Verified AArch64.target Impl.P256.Booth.publicKey
      (Spec.EcKey.P256.inst.publicKeyContract (AArch64.abi.withConsts p256.combConsts)) :=
  Verified.of_correct (booth_pk_a64 hL hI hcomb) booth_pk_ct implies

end VG.Proof.EcKey.AArch64
