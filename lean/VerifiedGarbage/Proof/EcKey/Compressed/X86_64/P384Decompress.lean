module

import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.DecompressMain
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.InverseVerified
public import VerifiedGarbage.Spec.EcKey.P384
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.InverseLit
import VerifiedGarbage.Proof.Ecdh.X86_64.P384.CheckVerified
import VerifiedGarbage.Proof.Weierstrass.Sqrt
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.X86_64.Decompress
meta import VerifiedGarbage.Impl.Ecdsa.P384.X86_64
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.InverseVerified
public import VerifiedGarbage.Impl.EcKey.Compressed.X86_64.Decompress
public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.DecompressContract
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.DecompressContract
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec

/-! # P384: instantiate the shared public-point decompression proof -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64.P384Decompress

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64.P384

abbrev code (adx : Bool) : Prog isa := Impl.EcKey.Compressed.X86_64.decompress (Inverse.cfg adx)

materialize_shared baseline := code false
materialize_shared accelerated := code true

theorem inlineOk (adx : Bool) : (code adx).InlineOk = true := by
  cases adx <;> lit_decide

theorem hmx (adx : Bool) : (code adx).allInstrs (fun i => !loadsMxcsr i) = true := by
  cases adx <;> lit_decide

theorem ct (adx : Bool) : ConstantTime isa (decompressContract Spec.P384.curve Impl.EcKey.Compressed.rootThreeModFour).pre
    (decompressContract Spec.P384.curve Impl.EcKey.Compressed.rootThreeModFour).pub (code adx) := by
  cases adx <;> apply VG.Taint.constantTime (A := X86_64.taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rsp])
  all_goals first
    | (intro s₁ s₂ _ _ hp
       obtain ⟨hsp, hout, hpk, hws⟩ := hp
       apply Taint.agree_ofRegs
       intro r hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl | rfl | rfl
       exact hout
       exact hpk
       exact hws
       exact hsp)
    | taint_decide

theorem sat : ∃ s, (Spec.EcKey.P384.inst.decompressPublicKeyContract abi 8).pre s := by
  sig_implies_sat [Spec.EcKey.P384.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
    Spec.EcKey.Instance.decompressPublicKeySig, Spec.P384.curve, Spec.EcKey.scratchWords,
    abi, argRegs, decompressSatState] [decompressSatState] using (decompressSatState Spec.P384.curve.len)

theorem verified (hL : Law Spec.P384.curve) (hI : InvSounds) (adx : Bool) :
    Verified target (code adx) (Spec.EcKey.P384.inst.decompressPublicKeyContract abi 8) := by
  have hc := (Inverse.cfg_ok hI adx).toBaseCfgOk
  have hp : (Inverse.cfg adx).C.p % 4 = 3 := by cases adx <;> decide +kernel
  have hf := rootFacts_three_mod_four hL (show Spec.P384.curve.p % 4 = 3 by decide +kernel)
  have himp := decompress_implies Spec.EcKey.P384.inst _ hf sat
  refine Verified.of_inline_ct (inlineOk adx)
    (by
      cases adx
      · exact decompress_correct _ hc _ (candidateThree_correct hc hp) (inlineOk false) (hmx false)
      · exact decompress_correct _ hc _ (candidateThree_correct hc hp) (inlineOk true) (hmx true))
    (ct adx) himp (fun _ hs => Sig.clear_of_pre hs) ?_
  intro s b hv u hs hp
  exact decompress_post_patch _ _ s b hv u (himp.pre s hs) (Sig.clear_of_pre hs) hp

end VG.Proof.EcKey.Compressed.X86_64.P384Decompress
