module

import VerifiedGarbage.Proof.EcKey.Compressed.X86.Verified
import VerifiedGarbage.Proof.Ecdsa.X86.P192.Verified
public import VerifiedGarbage.Spec.EcKey.P192
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.LitAlias
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.EcKey.Compressed.X86.MulTaint
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P192
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.LitAlias
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86.MulTaint
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P192
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.X86
meta import VerifiedGarbage.Impl.Ecdsa.P192.X86
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86.Contract
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86.CT
public import VerifiedGarbage.Impl.EcKey.Compressed.X86
public import VerifiedGarbage.Impl.Ecdsa.P192.X86
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.Contract
public import VerifiedGarbage.Proof.Ecdsa.X86.Layout
public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
public import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
import VerifiedGarbage.Proof.EcKey.Compressed.X86.CT

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86.P192

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86
open VG.Proof.Weierstrass.X86
open VG.Proof.Ecdsa.X86.P192

abbrev code : Prog isa := Impl.EcKey.Compressed.X86.compress p192

materialize_aliases fns := code
materialize_shared baseline := code

theorem sp : SpOk code 28 := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

taint_summary mulCodecSum : taint ({ codecMulT (Spec.P192.curve.len + 1) with regs := .ofList [.esp, .edi] })
  (Impl.Weierstrass.X86.Mont.mulFn Impl.Weierstrass.Mont.p192p.k Impl.Weierstrass.Mont.p192p.m)

theorem ct : ConstantTime isa (compressContract Spec.P192.curve).pre
    (compressContract Spec.P192.curve).pub code := by
  obtain ⟨_, hc⟩ : ∃ h, (taint.check (codecT (Spec.P192.curve.len + 1)) code h).isSome = true := by
    native_taint_decide_sum [mulCodecSum]
  exact VG.Taint.constantTime (A := taint) (codecT (Spec.P192.curve.len + 1))
    (fun _ _ hs ht hp => codec_agree hs ht hp) hc

theorem sat : ∃ s, (Spec.EcKey.P192.inst.compressPublicKeyContract abi 28).pre s := by
  have a0 : arg (satState 49 25) 0 = 0x1000 := by decide
  have a1 : arg (satState 49 25) 1 = 0x2000 := by decide
  have a2 : arg (satState 49 25) 2 = 0x8000 := by decide
  have ea : argAddr (satState 49 25) 0 = 0x20004 := by decide
  have esp : (satState 49 25).gpr .esp = 0x20000 := rfl
  have hlen : Spec.P192.curve.len = 24 := rfl
  sig_implies_sat [Spec.EcKey.P192.inst, Spec.EcKey.Instance.compressPublicKeyContract,
    Spec.EcKey.Instance.compressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argSlots, argVal, argBytes, stackBelow, satState] [a0, a1, a2, ea, esp] using (satState 49 25)

theorem verified :
    Verified target code (Spec.EcKey.P192.inst.compressPublicKeyContract abi 28) :=
  compress_verified (p192_ok) Spec.EcKey.P192.inst rfl sp ct sat

end VG.Proof.EcKey.Compressed.X86.P192
