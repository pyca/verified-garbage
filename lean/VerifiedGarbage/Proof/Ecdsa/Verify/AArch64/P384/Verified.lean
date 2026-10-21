module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.GContract
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJStep
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Proof.Weierstrass.CombW
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
public import VerifiedGarbage.Impl.Ecdsa.Verify.P384.AArch64
import VerifiedGarbage.Proof.Ecdsa.AArch64.P384.Verified
import VerifiedGarbage.Proof.P384.EcdhDouble.Verified
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.Lit
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointMain
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointTiming

/-!
# ECDSA verification over P-384 on AArch64: `Verified`

P-384 is a curve the proof supports (`p384_ok`, given the inversions' soundness `InvSounds`, and
`Law` for its group law, which the registration file supplies: `Proof.P384.law` and
`invSound_of_toM`), so the joint loop (`Joint.verify_ok`) gives the contract's postcondition, its
doublings the register-allocated ones of ECDH (`P384.EcdhDouble.dblsOk`, `ctRD`), its generator's
multiples those of `VG_P384_GTAB` (`Proof.P384.gtabOk9`); `x19`–`x25` are restored, and no
instruction writes the other callee-saved registers, `sp` or a SIMD register (`abiPreserved_of`).
Constant time relative to the contract's public inputs (`Joint.verify_public_ct`): the loop
branches on the digits of `u = e s⁻¹` and `v = r s⁻¹`, from the digest and the signature, and on
the coordinates of the key, and reads the entries of those digits; around them, by taint tracking,
the only branches are on loop counters and every other address is an argument plus a constant or
a counter.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64.P384

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.P384

/-- The allocated doubling does what the loop's must. -/
theorem dbl_spec (hI : Weierstrass.AArch64.InvSounds) (base : Addr) :
    Weierstrass.AArch64.DblSpec P384Joint.K p384.C base 8192 P384Joint.double P384Joint.K.R
      P384Joint.K.D (Weierstrass.AArch64.dblVR P384Joint.K) :=
  (P384.EcdhDouble.dblsOk P384.EcdhDouble.p384_C_p (Ecdh.AArch64.winLayQ (p384_ok hI))
    (Ecdh.AArch64.winAQ (p384_ok hI)) (Weierstrass.unitMod_pow_two (p384_ok hI).p_odd _) base _ rfl).1

theorem verify_callsKeep : CallsKeep verifyP384 := by lit_decide

theorem verify_untouched : KeepsUntouched verifyP384 := by lit_decide

theorem verify_keepsV : verifyP384.allInstrs keepsV = true := by lit_decide

theorem verify_a64 (hL : Weierstrass.Law Spec.P384.curve) (hO : Weierstrass.PrimeOrder Spec.P384.curve)
    (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P384.curve 9 1 Impl.P384.p384G9 Impl.P384.p384G9Start)
    (s : State) (hs : verifyGAArch64.pre s) :
    ∃ t s', Exec isa verifyP384 s t s' ∧ abiPreserved s s' ∧ verifyGAArch64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := Joint.verify_ok (p384_ok hI) hL hO (by decide) hT (dbl_spec hI)
    (vpreG_of hs)
  exact ⟨t, s', he, abiPreserved_of he verify_callsKeep verify_untouched verify_keepsV hsv, hpost⟩

theorem verify_ct (hL : Weierstrass.Law Spec.P384.curve) (hO : Weierstrass.PrimeOrder Spec.P384.curve)
    (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P384.curve 9 1 Impl.P384.p384G9 Impl.P384.p384G9Start) :
    ConstantTime isa
      (Spec.Ecdsa.P384.inst.verifyContract (AArch64.abi.withConsts P384Joint.p384v.combConsts)).pre
      (Spec.Ecdsa.P384.inst.verifyContract (AArch64.abi.withConsts P384Joint.p384v.combConsts)).pub
      verifyP384 := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  exact Joint.verify_public_ct (p384_ok hI) hL hO (by decide) hT (dbl_spec hI) _ _ _ _ _ _
    (vpreG_of (impliesG.pre _ pre₁)) (vpreG_of (impliesG.pre _ pre₂)) (jacPublicG_of_spec pub) e₁ e₂

theorem verify_verified (hL : Weierstrass.Law Spec.P384.curve) (hO : Weierstrass.PrimeOrder Spec.P384.curve)
    (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P384.curve 9 1 Impl.P384.p384G9 Impl.P384.p384G9Start) :
    Verified AArch64.target verifyP384
      (Spec.Ecdsa.P384.inst.verifyContract (AArch64.abi.withConsts P384Joint.p384v.combConsts)) := by
  refine ⟨fun s hs => ?_, verify_ct hL hO hI hT, impliesG.sat⟩
  obtain ⟨t, s', he, ha, hp⟩ := verify_a64 hL hO hI hT s (impliesG.pre _ hs)
  exact ⟨t, s', he, ha, impliesG.post s s' hs hp⟩

end VG.Proof.Ecdsa.Verify.AArch64.P384
