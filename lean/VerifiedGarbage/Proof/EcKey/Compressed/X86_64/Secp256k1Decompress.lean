module

import VerifiedGarbage.Proof.Framework.X86_64.ScrubFn
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
meta import VerifiedGarbage.Spec.EcKey.Secp256k1
public import VerifiedGarbage.Proof.EcKey.X86_64.Scrub.Out
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.EcKey.X86_64.Scrub.Out
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.DecompressMain
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Secp256k1.InverseVerified
public import VerifiedGarbage.Spec.EcKey.Secp256k1
import VerifiedGarbage.Proof.Ecdsa.X86_64.Secp256k1.InverseLit
import VerifiedGarbage.Proof.Weierstrass.Sqrt
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.X86_64.Decompress
meta import VerifiedGarbage.Impl.Ecdsa.Secp256k1.X86_64
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Secp256k1.InverseVerified
public import VerifiedGarbage.Impl.EcKey.Compressed.X86_64.Decompress
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.DecompressMain
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec

/-! # Secp256k1: instantiate the shared public-point decompression proof -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64.Secp256k1Decompress

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64.Secp256k1

abbrev code (adx : Bool) : Prog isa := Impl.EcKey.Compressed.X86_64.decompress (Inverse.cfg adx)

materialize_shared baseline := code false

theorem inlineOk (adx : Bool) : (code adx).InlineOk = true := by
  rw [show code adx = code false from rfl]
  lit_decide

theorem hmx (adx : Bool) : (code adx).allInstrs (fun i => !loadsMxcsr i) = true := by
  rw [show code adx = code false from rfl]
  lit_decide

theorem ct (adx : Bool) : ConstantTime isa (decompressContract Spec.Secp256k1.curve Impl.EcKey.Compressed.rootThreeModFour).pre
    (decompressContract Spec.Secp256k1.curve Impl.EcKey.Compressed.rootThreeModFour).pub (code adx) := by
  rw [show code adx = code false from rfl]
  apply VG.Taint.constantTime (A := X86_64.taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rsp])
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

theorem sat : ∃ s, (Spec.EcKey.Secp256k1.inst.decompressPublicKeyContract abi 8).pre s := by
  sig_implies_sat [Spec.EcKey.Secp256k1.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
    Spec.EcKey.Instance.decompressPublicKeySig, Spec.Secp256k1.curve, Spec.EcKey.scratchWords,
    abi, argRegs, decompressSatState] [decompressSatState] using (decompressSatState Spec.Secp256k1.curve.len)

theorem verified (hL : Law Spec.Secp256k1.curve) (hI : InvSounds) (adx : Bool) :
    Verified target (code adx) (Spec.EcKey.Secp256k1.inst.decompressPublicKeyContract abi 8) := by
  have hc := Inverse.cfg_ok hI adx
  have hp : (Inverse.cfg adx).C.p % 4 = 3 := by cases adx <;> decide +kernel
  have hf := rootFacts_three_mod_four hL (show Spec.Secp256k1.curve.p % 4 = 3 by decide +kernel)
  have himp := decompress_implies Spec.EcKey.Secp256k1.inst _ hf sat
  refine Verified.of_inline_ct (inlineOk adx)
    (by
      cases adx
      · exact decompress_correct _ hc _ (candidateThree_correct hc hp) (inlineOk false) (hmx false)
      · exact decompress_correct _ hc _ (candidateThree_correct hc hp) (inlineOk true) (hmx true))
    (ct adx) himp (fun _ hs => Sig.clear_of_pre hs) ?_
  intro s b hv u hs hp
  exact decompress_post_patch _ _ s b hv u (himp.pre s hs) (Sig.clear_of_pre hs) hp

/-! ## Without secret residue -/

theorem codeSp : (code false).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `vg_ec_secp256k1_decompress_public_key` as emitted (`Impl.EcKey.Compressed.X86_64.Fn.decompress`), its cleanup included, meets its
contract in constant time and returns without secret residue. -/
theorem scrubbed (hL : Law Spec.Secp256k1.curve) (hI : InvSounds) :
    VerifiedScrubbed target (Impl.EcKey.Compressed.X86_64.Fn.decompress (Inverse.cfg false))
      (Spec.EcKey.Secp256k1.inst.decompressPublicKeyApi.contract abi 8) 32 :=
  X86_64.Scrub.verifiedScrubbedAll (api := Spec.EcKey.Secp256k1.inst.decompressPublicKeyApi)
    { code := code false
      verified := verified hL hI false
      stack := 8
      spSafe := codeSp } .sse (EcKey.X86_64.Scrub.decompressOut _ _)

theorem spSafe : (Impl.EcKey.Compressed.X86_64.Fn.decompress (Inverse.cfg false)).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  X86_64.Scrub.scrubKs_spSafe codeSp

end VG.Proof.EcKey.Compressed.X86_64.Secp256k1Decompress
