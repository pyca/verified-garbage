module

import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.DecompressMain
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.InverseVerified
public import VerifiedGarbage.Spec.EcKey.P224
import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.InverseLit
import VerifiedGarbage.Proof.Ecdh.X86_64.P224.CheckVerified
import VerifiedGarbage.Proof.P224.Sqrt
import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.Tonelli
import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.DecompressCT
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.DecompressCT
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.X86_64.Decompress
meta import VerifiedGarbage.Impl.Ecdsa.P224.X86_64
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.InverseVerified
public import VerifiedGarbage.Impl.EcKey.Compressed.X86_64.Decompress
public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.DecompressContract
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.DecompressContract
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec

/-! # P224: instantiate the shared public-point decompression proof -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64.P224Decompress

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64.P224

abbrev root (a : Spec.Weierstrass.Fe Spec.P224.curve) :=
  Impl.EcKey.Compressed.rootTonelli a ((Spec.P224.curve.p - 1) / 2 ^ 96) 96 (Fin.ofNat Spec.P224.curve.p 11)

abbrev code (adx : Bool) : Prog isa := Impl.EcKey.Compressed.X86_64.decompress (Inverse.cfg adx)

materialize_shared baseline := code false

theorem inlineOk (adx : Bool) : (code adx).InlineOk = true := by
  cases adx <;> lit_decide

theorem hmx (adx : Bool) : (code adx).allInstrs (fun i => !loadsMxcsr i) = true := by
  cases adx <;> lit_decide

theorem ct (adx : Bool) : ConstantTime isa (decompressContract Spec.P224.curve root).pre
    (decompressContract Spec.P224.curve root).pub (code adx) := by
  cases adx <;> apply VG.Taint.constantTime (A := X86_64.taint) (decompressT Spec.P224.curve.len)
  all_goals first
    | exact fun _ _ h₁ h₂ hp => decompress_agree h₁ h₂ hp
    | taint_decide

theorem sat : ∃ s, (Spec.EcKey.P224.inst.decompressPublicKeyContract abi 8).pre s := by
  sig_implies_sat [Spec.EcKey.P224.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
    Spec.EcKey.Instance.decompressPublicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords,
    abi, argRegs, decompressSatState] [decompressSatState] using (decompressSatState Spec.P224.curve.len)

theorem verified (hL : Law Spec.P224.curve) (hI : InvSounds) (adx : Bool) :
    Verified target (code adx) (Spec.EcKey.P224.inst.decompressPublicKeyContract abi 8) := by
  have hc := Inverse.cfg_ok hI adx
  have hp : (Inverse.cfg adx).C.p % 4 ≠ 3 := by cases adx <;> decide +kernel
  have hn9 : (Inverse.cfg adx).n ≠ 9 := by cases adx <;> decide
  have hq : 0 < Impl.EcKey.Compressed.X86_64.rootQ (Inverse.cfg adx) := by
    cases adx <;> decide +kernel
  have hf := VG.Proof.P224.rootFacts hL
  have himp := decompress_implies Spec.EcKey.P224.inst _ hf sat
  refine Verified.of_inline_ct (inlineOk adx)
    (by
      cases adx
      · exact decompress_correct _ hc _ (candidateTonelli_correct hc hp hn9 hq) (inlineOk false) (hmx false)
      · exact decompress_correct _ hc _ (candidateTonelli_correct hc hp hn9 hq) (inlineOk true) (hmx true))
    (ct adx) himp (fun _ hs => Sig.clear_of_pre hs) ?_
  intro s b hv u hs hp
  exact decompress_post_patch _ _ s b hv u (himp.pre s hs) (Sig.clear_of_pre hs) hp

end VG.Proof.EcKey.Compressed.X86_64.P224Decompress
