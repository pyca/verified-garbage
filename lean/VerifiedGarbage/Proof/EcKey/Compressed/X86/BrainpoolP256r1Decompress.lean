module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86.DecompressVerified
public import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP256r1.Verified
public import VerifiedGarbage.Spec.EcKey.BrainpoolP256r1
import VerifiedGarbage.Proof.Weierstrass.Sqrt
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.X86
meta import VerifiedGarbage.Impl.EcKey.Compressed.X86.Decompress
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.X86
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86.Contract
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86.CT

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86.BrainpoolP256r1Decompress

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86
open VG.Proof.Weierstrass.X86
open VG.Proof.Ecdsa.X86.BrainpoolP256r1

abbrev code : Prog isa := Impl.EcKey.Compressed.X86.decompress brainpoolp256r1

materialize_shared baseline := code

theorem sp : SpOk code 28 := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

theorem ct : ConstantTime isa (decompressContract Spec.BrainpoolP256r1.curve Impl.EcKey.Compressed.rootThreeModFour).pre
    (decompressContract Spec.BrainpoolP256r1.curve Impl.EcKey.Compressed.rootThreeModFour).pub code := by
  apply VG.Taint.constantTime (A := taint) (codecT (2 * Spec.BrainpoolP256r1.curve.len + 1))
  · exact fun _ _ hs ht hp => codec_agree hs ht hp
  · taint_decide

theorem sat : ∃ s, (Spec.EcKey.BrainpoolP256r1.inst.decompressPublicKeyContract abi 28).pre s := by
  have a0 : arg (satState 33 65) 0 = 0x1000 := by decide
  have a1 : arg (satState 33 65) 1 = 0x2000 := by decide
  have a2 : arg (satState 33 65) 2 = 0x8000 := by decide
  have ea : argAddr (satState 33 65) 0 = 0x20004 := by decide
  have esp : (satState 33 65).gpr .esp = 0x20000 := rfl
  have hlen : Spec.BrainpoolP256r1.curve.len = 32 := rfl
  sig_implies_sat [Spec.EcKey.BrainpoolP256r1.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
    Spec.EcKey.Instance.decompressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argSlots, argVal, argBytes, stackBelow, satState] [a0, a1, a2, ea, esp] using (satState 33 65)

theorem verified (hL : Proof.Weierstrass.Law Spec.BrainpoolP256r1.curve) (hI : VG.Proof.Weierstrass.X86.Inv.InvSounds) :
    Verified target code (Spec.EcKey.BrainpoolP256r1.inst.decompressPublicKeyContract abi 28) :=
  decompress_verified (brainpoolp256r1_ok hI) Spec.EcKey.BrainpoolP256r1.inst rfl Impl.EcKey.Compressed.rootThreeModFour (candidateThree_correct (brainpoolp256r1_ok hI) (by decide +kernel)) (Proof.Weierstrass.rootFacts_three_mod_four hL (by decide +kernel)) sp ct sat

end VG.Proof.EcKey.Compressed.X86.BrainpoolP256r1Decompress
