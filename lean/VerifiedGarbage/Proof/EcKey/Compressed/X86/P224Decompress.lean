module

import VerifiedGarbage.Proof.EcKey.Compressed.X86.DecompressVerified
import VerifiedGarbage.Proof.Ecdsa.X86.P224.Verified
public import VerifiedGarbage.Spec.EcKey.P224
import VerifiedGarbage.Proof.P224.Sqrt
import VerifiedGarbage.Proof.EcKey.Compressed.X86.Tonelli
import VerifiedGarbage.Proof.EcKey.Compressed.X86.DecompressCT
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86.DecompressCT
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86.RootCT
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.LitAlias
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.EcKey.Compressed.X86.MulTaint
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P224
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.LitAlias
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86.MulTaint
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P224
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.X86
meta import VerifiedGarbage.Impl.EcKey.Compressed.X86.Decompress
meta import VerifiedGarbage.Impl.Ecdsa.P224.X86
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86.Contract
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86.CT
import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Impl.EcKey.Compressed.X86.Decompress
public import VerifiedGarbage.Impl.Ecdsa.P224.X86
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.DecompressContract
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.DecompressMiddle
public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86.Tonelli

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86.P224Decompress

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86
open VG.Proof.Weierstrass.X86
open VG.Proof.Ecdsa.X86.P224

abbrev code : Prog isa := Impl.EcKey.Compressed.X86.decompress p224

materialize_aliases fns := code
materialize_shared baseline := code

theorem sp : SpOk code 28 := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

taint_summary mulSum : taint ({ codecMulT (2 * Spec.P224.curve.len + 1) with regs := .ofList [.esp, .edi, .esi], argLen := 0, argBases := [] })
  (Impl.Weierstrass.X86.Mont.mulFn Impl.Weierstrass.Mont.p224p.k Impl.Weierstrass.Mont.p224p.m)

taint_summary mulSumW : taint ({ codecMulT (2 * Spec.P224.curve.len + 1) with regs := .ofList [.esp, .edi], argLen := 0, argBases := [] })
  (Impl.Weierstrass.X86.Mont.mulFn Impl.Weierstrass.Mont.p224p.k Impl.Weierstrass.Mont.p224p.m)

theorem ct : ConstantTime isa (decompressContract Spec.P224.curve (fun a : Spec.Weierstrass.Fe Spec.P224.curve => Impl.EcKey.Compressed.rootTonelli a ((Spec.P224.curve.p - 1) / 2 ^ 96) 96 (Fin.ofNat Spec.P224.curve.p 11))).pre
    (decompressContract Spec.P224.curve (fun a : Spec.Weierstrass.Fe Spec.P224.curve => Impl.EcKey.Compressed.rootTonelli a ((Spec.P224.curve.p - 1) / 2 ^ 96) 96 (Fin.ofNat Spec.P224.curve.p 11))).pub code := by
  apply decompress_tonelli_ct p224_ok (by decide +kernel)
    (candidateTonelli_correct p224_ok (by decide +kernel) (by decide +kernel)) sp
  · apply VG.Taint.constantTime (A := taint) (codecT (2 * Spec.P224.curve.len + 1))
    · exact fun _ _ hs ht hp => codec_agree hs ht hp
    · taint_decide
  · obtain ⟨_, hc⟩ : ∃ h, (taint.check (rootT p224) (prepareRoot p224) h).isSome = true := by
      native_taint_decide_sum [mulSum]
    exact VG.Taint.constantTime (A := taint) (rootT p224) (fun _ _ _ _ hp => root_agree hp) hc
  · apply VG.Taint.constantTime (A := taint) (rootT p224)
    · exact fun _ _ _ _ hp => root_agree hp
    · taint_decide
  · obtain ⟨_, hc⟩ : ∃ h, (taint.check (powerT p224) (Impl.EcKey.Compressed.X86.squarePower p224) h).isSome = true := by
      native_taint_decide_sum [mulSum]
    exact VG.Taint.constantTime (A := taint) (powerT p224) (fun _ _ _ _ hp => power_agree hp) hc
  · obtain ⟨_, hc⟩ : ∃ h, (taint.check (rootT p224) (descentKeeps p224) h).isSome = true := by
      native_taint_decide_sum [mulSumW]
    exact VG.Taint.constantTime (A := taint) (rootT p224) (fun _ _ _ _ hp => root_agree hp) hc
  · obtain ⟨_, hc⟩ : ∃ h, (taint.check (rootT p224) (.seq (Impl.EcKey.Compressed.X86.selectRoot p224) (Impl.EcKey.Compressed.X86.checkRoot p224)) h).isSome = true := by
      native_taint_decide_sum [mulSumW]
    exact VG.Taint.constantTime (A := taint) (rootT p224) (fun _ _ _ _ hp => root_agree hp) hc
  · apply VG.Taint.constantTime (A := taint) (finishT p224)
    · exact fun _ _ hs ht hp => finish_agree hs ht hp.1 hp.2
    · taint_decide

theorem sat : ∃ s, (Spec.EcKey.P224.inst.decompressPublicKeyContract abi 28).pre s := by
  have a0 : arg (satState 29 57) 0 = 0x1000 := by decide
  have a1 : arg (satState 29 57) 1 = 0x2000 := by decide
  have a2 : arg (satState 29 57) 2 = 0x8000 := by decide
  have ea : argAddr (satState 29 57) 0 = 0x20004 := by decide
  have esp : (satState 29 57).gpr .esp = 0x20000 := rfl
  have hlen : Spec.P224.curve.len = 28 := rfl
  sig_implies_sat [Spec.EcKey.P224.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
    Spec.EcKey.Instance.decompressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argSlots, argVal, argBytes, stackBelow, satState] [a0, a1, a2, ea, esp] using (satState 29 57)

theorem verified (hL : Proof.Weierstrass.Law Spec.P224.curve) :
    Verified target code (Spec.EcKey.P224.inst.decompressPublicKeyContract abi 28) :=
  decompress_verified (p224_ok) Spec.EcKey.P224.inst rfl (fun a : Spec.Weierstrass.Fe Spec.P224.curve => Impl.EcKey.Compressed.rootTonelli a ((Spec.P224.curve.p - 1) / 2 ^ 96) 96 (Fin.ofNat Spec.P224.curve.p 11)) (candidateTonelli_correct (p224_ok) (by decide +kernel) (by decide +kernel)) (Proof.P224.rootFacts hL) sp ct sat

end VG.Proof.EcKey.Compressed.X86.P224Decompress
