module

import VerifiedGarbage.Proof.EcKey.Compressed.X86.Verified
import VerifiedGarbage.Proof.Ecdsa.X86.Secp256k1.Verified
public import VerifiedGarbage.Spec.EcKey.Secp256k1
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
meta import VerifiedGarbage.Impl.Ecdsa.Secp256k1.X86
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86.Contract
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86.CT
public import VerifiedGarbage.Impl.EcKey.Compressed.X86
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.X86
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.Contract
public import VerifiedGarbage.Proof.Ecdsa.X86.Layout
public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
public import VerifiedGarbage.Proof.Weierstrass.X86.InvInterface
public import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
import VerifiedGarbage.Proof.EcKey.Compressed.X86.CT

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86.Secp256k1

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86
open VG.Proof.Weierstrass.X86
open VG.Proof.Ecdsa.X86.Secp256k1

abbrev code : Prog isa := Impl.EcKey.Compressed.X86.compress secp256k1

materialize_aliases fns := code
materialize_shared baseline := code

theorem sp : SpOk code 28 := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

taint_summary mulCodecSum : taint ({ codecMulT (Spec.Secp256k1.curve.len + 1) with regs := .ofList [.esp, .edi] })
  (Impl.Weierstrass.X86.Mont.mulFn Impl.Weierstrass.Mont.secp256k1p.k Impl.Weierstrass.Mont.secp256k1p.m)

theorem ct : ConstantTime isa (compressContract Spec.Secp256k1.curve).pre
    (compressContract Spec.Secp256k1.curve).pub code := by
  obtain ⟨_, hc⟩ : ∃ h, (taint.check (codecT (Spec.Secp256k1.curve.len + 1)) code h).isSome = true := by
    native_taint_decide_sum [mulCodecSum]
  exact VG.Taint.constantTime (A := taint) (codecT (Spec.Secp256k1.curve.len + 1))
    (fun _ _ hs ht hp => codec_agree hs ht hp) hc

theorem sat : ∃ s, (Spec.EcKey.Secp256k1.inst.compressPublicKeyContract abi 28).pre s := by
  have a0 : arg (satState 65 33) 0 = 0x1000 := by decide
  have a1 : arg (satState 65 33) 1 = 0x2000 := by decide
  have a2 : arg (satState 65 33) 2 = 0x8000 := by decide
  have ea : argAddr (satState 65 33) 0 = 0x20004 := by decide
  have esp : (satState 65 33).gpr .esp = 0x20000 := rfl
  have hlen : Spec.Secp256k1.curve.len = 32 := rfl
  sig_implies_sat [Spec.EcKey.Secp256k1.inst, Spec.EcKey.Instance.compressPublicKeyContract,
    Spec.EcKey.Instance.compressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argSlots, argVal, argBytes, stackBelow, satState] [a0, a1, a2, ea, esp] using (satState 65 33)

theorem verified (hI : VG.Proof.Weierstrass.X86.Inv.InvSounds) :
    Verified target code (Spec.EcKey.Secp256k1.inst.compressPublicKeyContract abi 28) :=
  compress_verified (secp256k1_ok hI) Spec.EcKey.Secp256k1.inst rfl sp ct sat

end VG.Proof.EcKey.Compressed.X86.Secp256k1
