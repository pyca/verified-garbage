module

import VerifiedGarbage.Proof.EcKey.Compressed.X86.Verified
import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP512r1.Verified
public import VerifiedGarbage.Spec.EcKey.BrainpoolP512r1
import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP512r1.Config
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.LitAlias
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.EcKey.Compressed.X86.MulTaint
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.BrainpoolP512r1
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.LitAlias
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86.MulTaint
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.BrainpoolP512r1
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.X86
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.X86
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86.Contract
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86.CT
public import VerifiedGarbage.Impl.EcKey.Compressed.X86
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.X86
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.Contract
public import VerifiedGarbage.Proof.Ecdsa.X86.Layout
public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
public import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
import VerifiedGarbage.Proof.EcKey.Compressed.X86.CT

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86.BrainpoolP512r1

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86
open VG.Proof.Weierstrass.X86
open VG.Proof.Ecdsa.X86.BrainpoolP512r1

abbrev code : Prog isa := Impl.EcKey.Compressed.X86.compress brainpoolp512r1

materialize_aliases fns := code
materialize_shared baseline := code

theorem sp : SpOk code 28 := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

taint_summary mulCodecSum : taint ({ codecMulT (Spec.BrainpoolP512r1.curve.len + 1) with regs := .ofList [.esp, .edi] })
  (Impl.Weierstrass.X86.Mont.mulFn Impl.Weierstrass.Mont.brainpoolp512r1p.k Impl.Weierstrass.Mont.brainpoolp512r1p.m)

theorem ct : ConstantTime isa (compressContract Spec.BrainpoolP512r1.curve).pre
    (compressContract Spec.BrainpoolP512r1.curve).pub code := by
  obtain ⟨_, hc⟩ : ∃ h, (taint.check (codecT (Spec.BrainpoolP512r1.curve.len + 1)) code h).isSome = true := by
    native_taint_decide_sum [mulCodecSum]
  exact VG.Taint.constantTime (A := taint) (codecT (Spec.BrainpoolP512r1.curve.len + 1))
    (fun _ _ hs ht hp => codec_agree hs ht hp) hc

theorem sat : ∃ s, (Spec.EcKey.BrainpoolP512r1.inst.compressPublicKeyContract abi 28).pre s := by
  have a0 : arg (satState 129 65) 0 = 0x1000 := by decide
  have a1 : arg (satState 129 65) 1 = 0x2000 := by decide
  have a2 : arg (satState 129 65) 2 = 0x8000 := by decide
  have ea : argAddr (satState 129 65) 0 = 0x20004 := by decide
  have esp : (satState 129 65).gpr .esp = 0x20000 := rfl
  have hlen : Spec.BrainpoolP512r1.curve.len = 64 := rfl
  sig_implies_sat [Spec.EcKey.BrainpoolP512r1.inst, Spec.EcKey.Instance.compressPublicKeyContract,
    Spec.EcKey.Instance.compressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argSlots, argVal, argBytes, stackBelow, satState] [a0, a1, a2, ea, esp] using (satState 129 65)

theorem verified :
    Verified target code (Spec.EcKey.BrainpoolP512r1.inst.compressPublicKeyContract abi 28) :=
  compress_verified (brainpoolp512r1_ok) Spec.EcKey.BrainpoolP512r1.inst rfl sp ct sat

end VG.Proof.EcKey.Compressed.X86.BrainpoolP512r1
