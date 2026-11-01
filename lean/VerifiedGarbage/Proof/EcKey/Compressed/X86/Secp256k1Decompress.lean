module

import VerifiedGarbage.Proof.EcKey.Compressed.X86.DecompressVerified
import VerifiedGarbage.Proof.Ecdsa.X86.Secp256k1.Verified
public import VerifiedGarbage.Spec.EcKey.Secp256k1
import VerifiedGarbage.Proof.Weierstrass.Sqrt
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.LitAlias
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.EcKey.Compressed.X86.MulTaint
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.Secp256k1
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.LitAlias
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86.MulTaint
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.Secp256k1
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.X86
meta import VerifiedGarbage.Impl.EcKey.Compressed.X86.Decompress
meta import VerifiedGarbage.Impl.Ecdsa.Secp256k1.X86
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86.Contract
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86.CT
public import VerifiedGarbage.Impl.EcKey.Compressed.X86.Decompress
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.X86
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.DecompressContract
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.DecompressMiddle
public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
public import VerifiedGarbage.Proof.Weierstrass.X86.InvInterface
import VerifiedGarbage.Proof.EcKey.Compressed.X86.CT

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86.Secp256k1Decompress

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86
open VG.Proof.Weierstrass.X86
open VG.Proof.Ecdsa.X86.Secp256k1

abbrev code : Prog isa := Impl.EcKey.Compressed.X86.decompress secp256k1

materialize_aliases fns := code
materialize_shared baseline := code

theorem sp : SpOk code 28 := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

taint_summary mulCodecSum : taint (codecMulT (2 * Spec.Secp256k1.curve.len + 1))
  (Impl.Weierstrass.X86.Mont.mulFn Impl.Weierstrass.Mont.secp256k1p.k Impl.Weierstrass.Mont.secp256k1p.m)

theorem ct : ConstantTime isa (decompressContract Spec.Secp256k1.curve Impl.EcKey.Compressed.rootThreeModFour).pre
    (decompressContract Spec.Secp256k1.curve Impl.EcKey.Compressed.rootThreeModFour).pub code := by
  obtain ⟨_, hc⟩ : ∃ h, (taint.check (codecT (2 * Spec.Secp256k1.curve.len + 1)) code h).isSome = true := by
    native_taint_decide_sum [mulCodecSum]
  exact VG.Taint.constantTime (A := taint) (codecT (2 * Spec.Secp256k1.curve.len + 1))
    (fun _ _ hs ht hp => codec_agree hs ht hp) hc

theorem sat : ∃ s, (Spec.EcKey.Secp256k1.inst.decompressPublicKeyContract abi 28).pre s := by
  have a0 : arg (satState 33 65) 0 = 0x1000 := by decide
  have a1 : arg (satState 33 65) 1 = 0x2000 := by decide
  have a2 : arg (satState 33 65) 2 = 0x8000 := by decide
  have ea : argAddr (satState 33 65) 0 = 0x20004 := by decide
  have esp : (satState 33 65).gpr .esp = 0x20000 := rfl
  have hlen : Spec.Secp256k1.curve.len = 32 := rfl
  sig_implies_sat [Spec.EcKey.Secp256k1.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
    Spec.EcKey.Instance.decompressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argSlots, argVal, argBytes, stackBelow, satState] [a0, a1, a2, ea, esp] using (satState 33 65)

theorem verified (hL : Proof.Weierstrass.Law Spec.Secp256k1.curve) (hI : VG.Proof.Weierstrass.X86.Inv.InvSounds) :
    Verified target code (Spec.EcKey.Secp256k1.inst.decompressPublicKeyContract abi 28) :=
  decompress_verified (secp256k1_ok hI) Spec.EcKey.Secp256k1.inst rfl Impl.EcKey.Compressed.rootThreeModFour (candidateThree_correct (secp256k1_ok hI) (by decide +kernel)) (Proof.Weierstrass.rootFacts_three_mod_four hL (by decide +kernel)) sp ct sat

end VG.Proof.EcKey.Compressed.X86.Secp256k1Decompress
