module


public import VerifiedGarbage.Proof.EcKey.X86_64.Scrub.Out
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.EcKey.X86_64.Scrub.Out
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.EcKey.P256
import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.DecompressMain
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P256.InverseVerified
public import VerifiedGarbage.Spec.EcKey.P256
import VerifiedGarbage.Proof.Ecdsa.X86_64.P256.InverseLit
import VerifiedGarbage.Proof.Weierstrass.Sqrt
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.X86_64.Decompress
meta import VerifiedGarbage.Impl.Ecdsa.P256.X86_64
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P256.InverseVerified
public import VerifiedGarbage.Impl.EcKey.Compressed.X86_64.Decompress
public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.DecompressContract
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.DecompressContract
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec

/-! # P256: instantiate the shared public-point decompression proof -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64.P256Decompress

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64.P256

abbrev code (adx : Bool) : Prog isa := Impl.EcKey.Compressed.X86_64.decompress (Inverse.cfg adx)

materialize_shared baseline := code false
materialize_shared accelerated := code true

theorem inlineOk (adx : Bool) : (code adx).InlineOk = true := by
  cases adx <;> lit_decide

theorem hmx (adx : Bool) : (code adx).allInstrs (fun i => !loadsMxcsr i) = true := by
  cases adx <;> lit_decide

theorem ct (adx : Bool) : ConstantTime isa (decompressContract Spec.P256.curve Impl.EcKey.Compressed.rootThreeModFour).pre
    (decompressContract Spec.P256.curve Impl.EcKey.Compressed.rootThreeModFour).pub (code adx) := by
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

theorem sat : ∃ s, (Spec.EcKey.P256.inst.decompressPublicKeyContract abi 8).pre s := by
  sig_implies_sat [Spec.EcKey.P256.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
    Spec.EcKey.Instance.decompressPublicKeySig, Spec.P256.curve, Spec.EcKey.scratchWords,
    abi, argRegs, decompressSatState] [decompressSatState] using (decompressSatState Spec.P256.curve.len)

theorem verified (hL : Law Spec.P256.curve) (hI : InvSounds) (adx : Bool) :
    Verified target (code adx) (Spec.EcKey.P256.inst.decompressPublicKeyContract abi 8) := by
  have hc := (Inverse.cfg_ok hI adx).toBaseCfgOk
  have hp : (Inverse.cfg adx).C.p % 4 = 3 := by cases adx <;> decide +kernel
  have hf := rootFacts_three_mod_four hL (show Spec.P256.curve.p % 4 = 3 by decide +kernel)
  have himp := decompress_implies Spec.EcKey.P256.inst _ hf sat
  refine Verified.of_inline_ct (inlineOk adx)
    (by
      cases adx
      · exact decompress_correct _ hc _ (candidateThree_correct hc hp) (inlineOk false) (hmx false)
      · exact decompress_correct _ hc _ (candidateThree_correct hc hp) (inlineOk true) (hmx true))
    (ct adx) himp (fun _ hs => Sig.clear_of_pre hs) ?_
  intro s b hv u hs hp
  exact decompress_post_patch _ _ s b hv u (himp.pre s hs) (Sig.clear_of_pre hs) hp

/-! ## Without secret residue -/

/-- The granules of its stack that `vg_ec_p256_decompress_public_key` (or its
`_adx` variant) must wipe on return, from the residue analysis
(`X86_64.RScrub.keepFor`). -/
def scrubKs : Bool → List Nat
  | false => keep_for% Spec.EcKey.P256.inst.decompressPublicKeyApi.sig 8 (code false) []
  | true => keep_for% Spec.EcKey.P256.inst.decompressPublicKeyApi.sig 8 (code true) []

theorem scrubOk (adx : Bool) : ∃ h : VG.Taint.Hint X86_64.RTaint.FT,
    (VG.Taint.check X86_64.RTaint.rtaint (X86_64.RScrub.init Spec.EcKey.P256.inst.decompressPublicKeyApi.sig 8 [])
      (code adx) h).any (X86_64.RScrub.resOkB · 8 (scrubKs adx) (Impl.Scrub.X86_64.chunks 8)) = true := by
  cases adx <;> exact X86_64.RScrub.Analysed.ok_of _ (by taint_decide)

/-- `vg_ec_p256_decompress_public_key`, or its `_adx` variant, followed by
`Impl.Scrub.X86_64.scrubTail` (`X86_64.RScrub.withScrub`): it returns without
secret residue. -/
def scrubReg (hL : Law Spec.P256.curve) (hI : InvSounds) (adx : Bool) :
    Registration Spec.EcKey.P256.inst.decompressPublicKeyApi target :=
  X86_64.RScrub.withScrub {
    suffix := if adx then "_adx" else ""
    code := code adx
    verified := verified hL hI adx
    stack := 8 }
    (EcKey.X86_64.Scrub.decompressOut _ _) [] (X86_64.RScrub.pubOk_nil _)
    (some ⟨scrubKs adx, scrubOk adx⟩)

end VG.Proof.EcKey.Compressed.X86_64.P256Decompress
