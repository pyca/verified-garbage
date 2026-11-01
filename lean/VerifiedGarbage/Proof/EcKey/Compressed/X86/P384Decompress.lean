module

import VerifiedGarbage.Proof.EcKey.Compressed.X86.DecompressVerified
import VerifiedGarbage.Proof.Ecdsa.X86.P384.Verified
public import VerifiedGarbage.Spec.EcKey.P384
import VerifiedGarbage.Proof.Weierstrass.Sqrt
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.LitAlias
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.EcKey.Compressed.X86.MulTaint
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P384
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.LitAlias
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86.MulTaint
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P384
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.X86
meta import VerifiedGarbage.Impl.EcKey.Compressed.X86.Decompress
meta import VerifiedGarbage.Impl.Ecdsa.P384.X86
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86.Contract
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86.CT
public import VerifiedGarbage.Impl.EcKey.Compressed.X86.Decompress
public import VerifiedGarbage.Impl.Ecdsa.P384.X86
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.DecompressContract
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.DecompressMiddle
public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
import VerifiedGarbage.Proof.EcKey.Compressed.X86.CT

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86.P384Decompress

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86
open VG.Proof.Weierstrass.X86
open VG.Proof.Ecdsa.X86.P384

abbrev code : Prog isa := Impl.EcKey.Compressed.X86.decompress p384

materialize_aliases fns := code
materialize_shared baseline := code

theorem sp : SpOk code 28 := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

taint_summary mulCodecSum : taint (codecMulT (2 * Spec.P384.curve.len + 1))
  (Impl.Weierstrass.X86.Mont.mulFn Impl.Weierstrass.Mont.p384p.k Impl.Weierstrass.Mont.p384p.m)

theorem ct : ConstantTime isa (decompressContract Spec.P384.curve Impl.EcKey.Compressed.rootThreeModFour).pre
    (decompressContract Spec.P384.curve Impl.EcKey.Compressed.rootThreeModFour).pub code := by
  obtain ⟨_, hc⟩ : ∃ h, (taint.check (codecT (2 * Spec.P384.curve.len + 1)) code h).isSome = true := by
    native_taint_decide_sum [mulCodecSum]
  exact VG.Taint.constantTime (A := taint) (codecT (2 * Spec.P384.curve.len + 1))
    (fun _ _ hs ht hp => codec_agree hs ht hp) hc

theorem sat : ∃ s, (Spec.EcKey.P384.inst.decompressPublicKeyContract abi 28).pre s := by
  have a0 : arg (satState 49 97) 0 = 0x1000 := by decide
  have a1 : arg (satState 49 97) 1 = 0x2000 := by decide
  have a2 : arg (satState 49 97) 2 = 0x8000 := by decide
  have ea : argAddr (satState 49 97) 0 = 0x20004 := by decide
  have esp : (satState 49 97).gpr .esp = 0x20000 := rfl
  have hlen : Spec.P384.curve.len = 48 := rfl
  sig_implies_sat [Spec.EcKey.P384.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
    Spec.EcKey.Instance.decompressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argSlots, argVal, argBytes, stackBelow, satState] [a0, a1, a2, ea, esp] using (satState 49 97)

theorem verified (hL : Proof.Weierstrass.Law Spec.P384.curve) :
    Verified target code (Spec.EcKey.P384.inst.decompressPublicKeyContract abi 28) :=
  decompress_verified (p384_ok) Spec.EcKey.P384.inst rfl Impl.EcKey.Compressed.rootThreeModFour (candidateThree_correct (p384_ok) (by decide +kernel)) (Proof.Weierstrass.rootFacts_three_mod_four hL (by decide +kernel)) sp ct sat

end VG.Proof.EcKey.Compressed.X86.P384Decompress
