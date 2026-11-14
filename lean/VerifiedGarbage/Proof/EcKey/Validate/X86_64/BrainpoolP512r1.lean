module

meta import VerifiedGarbage.Spec.EcKey.BrainpoolP512r1
public import VerifiedGarbage.Proof.EcKey.X86_64.Scrub.Out
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.EcKey.X86_64.Scrub.Out
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.EcKey.Validate.X86_64.Main
public import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP512r1.InverseVerified
public import VerifiedGarbage.Spec.EcKey.BrainpoolP512r1
import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP512r1.InverseLit
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Impl.EcKey.Validate.X86_64
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.X86_64
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP512r1.InverseVerified
public import VerifiedGarbage.Impl.EcKey.Validate.X86_64
public import VerifiedGarbage.Proof.EcKey.Validate.X86_64.Contract
meta import VerifiedGarbage.Proof.EcKey.Validate.X86_64.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec

/-! # BrainpoolP512r1: instantiate the shared encoded-point validation proof -/

@[expose] public section

namespace VG.Proof.EcKey.Validate.X86_64.BrainpoolP512r1

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64.BrainpoolP512r1

abbrev code (_adx : Bool) : Prog isa := Impl.EcKey.Validate.X86_64.validate Inverse.cfg

materialize_shared baseline := code false

theorem inlineOk (adx : Bool) : (code adx).InlineOk = true := by
  cases adx <;> lit_decide

theorem hmx (adx : Bool) : (code adx).allInstrs (fun i => !loadsMxcsr i) = true := by
  cases adx <;> lit_decide

theorem ct (adx : Bool) : ConstantTime isa (keyContract Spec.BrainpoolP512r1.curve).pre
    (keyContract Spec.BrainpoolP512r1.curve).pub (code adx) := by
  cases adx <;> apply VG.Taint.constantTime (A := X86_64.taint) (Taint.ofRegs [.rdi, .rsi, .rsp])
  all_goals first
    | (intro s₁ s₂ _ _ hp
       obtain ⟨hsp, hpk, hws⟩ := hp
       apply Taint.agree_ofRegs
       intro r hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl | rfl
       exact hpk
       exact hws
       exact hsp)
    | taint_decide

theorem sat : ∃ s, (Spec.EcKey.BrainpoolP512r1.inst.validatePublicKeyContract abi 8).pre s := by
  sig_implies_sat [Spec.EcKey.BrainpoolP512r1.inst, Spec.EcKey.Instance.validatePublicKeyContract,
    Spec.EcKey.Instance.validatePublicKeySig, Spec.BrainpoolP512r1.curve, Spec.EcKey.scratchWords,
    abi, argRegs, satState] [satState] using (satState Spec.BrainpoolP512r1.curve.len)

theorem verified (hI : InvSounds) (adx : Bool) :
    Verified target (code adx) (Spec.EcKey.BrainpoolP512r1.inst.validatePublicKeyContract abi 8) := by
  have hc := Inverse.cfg_ok hI
  refine Verified.of_inline_ct (inlineOk adx)
    (by simpa only [Inverse.cfg_C] using (correct Inverse.cfg hc (inlineOk adx) (hmx adx))) (ct adx)
    (implies Spec.EcKey.BrainpoolP512r1.inst sat) (fun _ hs => Sig.clear_of_pre hs) ?_
  intro s b hv u _ hp
  simpa only [keyContract, State.patch_gpr] using hp

/-! ## Without secret residue -/

/-- The granules of its stack that `vg_ec_brainpoolp512r1_validate_public_key` must wipe on
return, from the residue analysis (`X86_64.RScrub.keepFor`). -/
def scrubKs : List Nat :=
  keep_for% Spec.EcKey.BrainpoolP512r1.inst.validatePublicKeyApi.sig 8 (code false) []

theorem scrubOk : ∃ h : VG.Taint.Hint X86_64.RTaint.FT,
    (VG.Taint.check X86_64.RTaint.rtaint (X86_64.RScrub.init Spec.EcKey.BrainpoolP512r1.inst.validatePublicKeyApi.sig 8 [])
      (code false) h).any (X86_64.RScrub.resOkB · 8 scrubKs (Impl.Scrub.X86_64.chunks 8)) = true :=
  X86_64.RScrub.Analysed.ok_of _ (by taint_decide)

/-- `vg_ec_brainpoolp512r1_validate_public_key`, followed by `Impl.Scrub.X86_64.scrubTail`
(`X86_64.RScrub.withScrub`): it returns without secret residue. -/
def scrubReg (hI : InvSounds) :
    Registration Spec.EcKey.BrainpoolP512r1.inst.validatePublicKeyApi target :=
  X86_64.RScrub.withScrub {
    code := code false
    verified := verified hI false
    stack := 8 }
    (EcKey.X86_64.Scrub.validateOut _ _) [] (X86_64.RScrub.pubOk_nil _) (some ⟨scrubKs, scrubOk⟩)

end VG.Proof.EcKey.Validate.X86_64.BrainpoolP512r1
