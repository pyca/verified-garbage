module

meta import VerifiedGarbage.Spec.EcKey.BrainpoolP256r1
public import VerifiedGarbage.Proof.EcKey.X86_64.Scrub.Out
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.EcKey.X86_64.Scrub.Out
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.DecompressMain
public import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP256r1.InverseVerified
public import VerifiedGarbage.Spec.EcKey.BrainpoolP256r1
import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP256r1.InverseLit
import VerifiedGarbage.Proof.Weierstrass.Sqrt
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.X86_64.Decompress
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.X86_64
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP256r1.InverseVerified
public import VerifiedGarbage.Impl.EcKey.Compressed.X86_64.Decompress
public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.DecompressContract
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.DecompressContract
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec

/-! # BrainpoolP256r1: instantiate the shared public-point decompression proof -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64.BrainpoolP256r1Decompress

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64.BrainpoolP256r1

abbrev code (adx : Bool) : Prog isa := Impl.EcKey.Compressed.X86_64.decompress (Inverse.cfg adx)

materialize_shared baseline := code false

theorem inlineOk (adx : Bool) : (code adx).InlineOk = true := by
  rw [show code adx = code false from rfl]
  lit_decide

theorem hmx (adx : Bool) : (code adx).allInstrs (fun i => !loadsMxcsr i) = true := by
  rw [show code adx = code false from rfl]
  lit_decide

theorem ct (adx : Bool) : ConstantTime isa (decompressContract Spec.BrainpoolP256r1.curve Impl.EcKey.Compressed.rootThreeModFour).pre
    (decompressContract Spec.BrainpoolP256r1.curve Impl.EcKey.Compressed.rootThreeModFour).pub (code adx) := by
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

theorem sat : ∃ s, (Spec.EcKey.BrainpoolP256r1.inst.decompressPublicKeyContract abi 8).pre s := by
  sig_implies_sat [Spec.EcKey.BrainpoolP256r1.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
    Spec.EcKey.Instance.decompressPublicKeySig, Spec.BrainpoolP256r1.curve, Spec.EcKey.scratchWords,
    abi, argRegs, decompressSatState] [decompressSatState] using (decompressSatState Spec.BrainpoolP256r1.curve.len)

theorem verified (hL : Law Spec.BrainpoolP256r1.curve) (hI : InvSounds) (adx : Bool) :
    Verified target (code adx) (Spec.EcKey.BrainpoolP256r1.inst.decompressPublicKeyContract abi 8) := by
  have hc := Inverse.cfg_ok hI adx
  have hp : (Inverse.cfg adx).C.p % 4 = 3 := by cases adx <;> decide +kernel
  have hf := rootFacts_three_mod_four hL (show Spec.BrainpoolP256r1.curve.p % 4 = 3 by decide +kernel)
  have himp := decompress_implies Spec.EcKey.BrainpoolP256r1.inst _ hf sat
  refine Verified.of_inline_ct (inlineOk adx)
    (by
      cases adx
      · exact decompress_correct _ hc _ (candidateThree_correct hc hp) (inlineOk false) (hmx false)
      · exact decompress_correct _ hc _ (candidateThree_correct hc hp) (inlineOk true) (hmx true))
    (ct adx) himp (fun _ hs => Sig.clear_of_pre hs) ?_
  intro s b hv u hs hp
  exact decompress_post_patch _ _ s b hv u (himp.pre s hs) (Sig.clear_of_pre hs) hp

/-! ## Without secret residue -/

/-- The granules of its stack that `vg_ec_brainpoolp256r1_decompress_public_key` must wipe on
return, from the residue analysis (`X86_64.RScrub.keepFor`). -/
def scrubKs : List Nat :=
  keep_for% Spec.EcKey.BrainpoolP256r1.inst.decompressPublicKeyApi.sig 8 (code false) []

theorem scrubOk : ∃ h : VG.Taint.Hint X86_64.RTaint.FT,
    (VG.Taint.check X86_64.RTaint.rtaint (X86_64.RScrub.init Spec.EcKey.BrainpoolP256r1.inst.decompressPublicKeyApi.sig 8 [])
      (code false) h).any (X86_64.RScrub.resOkB · 8 scrubKs (Impl.Scrub.X86_64.chunks 8)) = true :=
  X86_64.RScrub.Analysed.ok_of _ (by taint_decide)

/-- `vg_ec_brainpoolp256r1_decompress_public_key`, followed by `Impl.Scrub.X86_64.scrubTail`
(`X86_64.RScrub.withScrub`): it returns without secret residue. -/
def scrubReg (hL : Law Spec.BrainpoolP256r1.curve) (hI : InvSounds) :
    Registration Spec.EcKey.BrainpoolP256r1.inst.decompressPublicKeyApi target :=
  X86_64.RScrub.withScrub {
    code := code false
    verified := verified hL hI false
    stack := 8 }
    (EcKey.X86_64.Scrub.decompressOut _ _) [] (X86_64.RScrub.pubOk_nil _) (some ⟨scrubKs, scrubOk⟩)

end VG.Proof.EcKey.Compressed.X86_64.BrainpoolP256r1Decompress
