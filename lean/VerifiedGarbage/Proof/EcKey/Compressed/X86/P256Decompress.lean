module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86.DecompressVerified
public import VerifiedGarbage.Proof.Ecdsa.X86.Verified
public import VerifiedGarbage.Spec.EcKey.P256
import VerifiedGarbage.Proof.Weierstrass.Sqrt
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.X86
meta import VerifiedGarbage.Impl.EcKey.Compressed.X86.Decompress
meta import VerifiedGarbage.Impl.Ecdsa.P256.X86
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86.Contract
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86.CT

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86.P256Decompress

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86
open VG.Proof.Weierstrass.X86

abbrev code : Prog isa := Impl.EcKey.Compressed.X86.decompress p256

materialize_shared baseline := code

theorem sp : SpOk code 28 := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

theorem ct : ConstantTime isa (decompressContract Spec.P256.curve Impl.EcKey.Compressed.rootThreeModFour).pre
    (decompressContract Spec.P256.curve Impl.EcKey.Compressed.rootThreeModFour).pub code := by
  apply VG.Taint.constantTime (A := taint) (codecT (2 * Spec.P256.curve.len + 1))
  · exact fun _ _ hs ht hp => codec_agree hs ht hp
  · run_tac VG.taintDecideAt (Lean.mkNatLit 256) "taint_decide" none

theorem sat : ∃ s, (Spec.EcKey.P256.inst.decompressPublicKeyContract abi 28).pre s := by
  have a0 : arg (satState 33 65) 0 = 0x1000 := by decide
  have a1 : arg (satState 33 65) 1 = 0x2000 := by decide
  have a2 : arg (satState 33 65) 2 = 0x8000 := by decide
  have ea : argAddr (satState 33 65) 0 = 0x20004 := by decide
  have esp : (satState 33 65).gpr .esp = 0x20000 := rfl
  have hlen : Spec.P256.curve.len = 32 := rfl
  sig_implies_sat [Spec.EcKey.P256.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
    Spec.EcKey.Instance.decompressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argSlots, argVal, argBytes, stackBelow, satState] [a0, a1, a2, ea, esp] using (satState 33 65)

theorem verified (hL : Proof.Weierstrass.Law Spec.P256.curve) (hI : VG.Proof.Weierstrass.X86.Inv.InvSounds) :
    Verified target code (Spec.EcKey.P256.inst.decompressPublicKeyContract abi 28) :=
  decompress_verified (p256_ok hI) Spec.EcKey.P256.inst rfl Impl.EcKey.Compressed.rootThreeModFour (candidateThree_correct (p256_ok hI) (by decide +kernel)) (Proof.Weierstrass.rootFacts_three_mod_four hL (by decide +kernel)) sp ct sat

end VG.Proof.EcKey.Compressed.X86.P256Decompress
