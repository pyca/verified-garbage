module


public import VerifiedGarbage.Proof.EcKey.X86_64.Scrub.Out
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.EcKey.X86_64.Scrub.Out
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.EcKey.P521
import VerifiedGarbage.Proof.EcKey.Validate.X86_64.Main
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.InverseVerified
public import VerifiedGarbage.Spec.EcKey.P521
import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.InverseLit
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Impl.EcKey.Validate.X86_64
meta import VerifiedGarbage.Impl.Ecdsa.P521.X86_64
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.InverseVerified
public import VerifiedGarbage.Impl.EcKey.Validate.X86_64
public import VerifiedGarbage.Proof.EcKey.Validate.X86_64.Contract
meta import VerifiedGarbage.Proof.EcKey.Validate.X86_64.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec

/-! # P521: instantiate the shared encoded-point validation proof -/

@[expose] public section

namespace VG.Proof.EcKey.Validate.X86_64.P521

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64.P521

abbrev code (adx : Bool) : Prog isa := Impl.EcKey.Validate.X86_64.validate (Inverse.cfg adx)

materialize_shared baseline := code false
materialize_shared accelerated := code true

theorem inlineOk (adx : Bool) : (code adx).InlineOk = true := by
  cases adx <;> lit_decide

theorem hmx (adx : Bool) : (code adx).allInstrs (fun i => !loadsMxcsr i) = true := by
  cases adx <;> lit_decide

theorem ct (adx : Bool) : ConstantTime isa (keyContract Spec.P521.curve).pre
    (keyContract Spec.P521.curve).pub (code adx) := by
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

theorem sat : ∃ s, (Spec.EcKey.P521.inst.validatePublicKeyContract abi 8).pre s := by
  sig_implies_sat [Spec.EcKey.P521.inst, Spec.EcKey.Instance.validatePublicKeyContract,
    Spec.EcKey.Instance.validatePublicKeySig, Spec.P521.curve, Spec.EcKey.scratchWords,
    abi, argRegs, satState] [satState] using (satState Spec.P521.curve.len)

theorem verified (hI : InvSounds) (adx : Bool) :
    Verified target (code adx) (Spec.EcKey.P521.inst.validatePublicKeyContract abi 8) := by
  have hc := (Inverse.cfg_ok hI adx).toBaseCfgOk
  refine Verified.of_inline_ct (inlineOk adx)
    (by simpa only [Inverse.cfg_C] using (correct (Inverse.cfg adx) hc (inlineOk adx) (hmx adx))) (ct adx)
    (implies Spec.EcKey.P521.inst sat) (fun _ hs => Sig.clear_of_pre hs) ?_
  intro s b hv u _ hp
  simpa only [keyContract, State.patch_gpr] using hp

/-! ## Without secret residue -/

/-- The granules of its stack that `vg_ec_p521_validate_public_key` (or its
`_adx` variant) must wipe on return, from the residue analysis
(`X86_64.RScrub.keepFor`). -/
def scrubKs : Bool → List Nat
  | false => keep_for% Spec.EcKey.P521.inst.validatePublicKeyApi.sig 8 (code false) []
  | true => keep_for% Spec.EcKey.P521.inst.validatePublicKeyApi.sig 8 (code true) []

theorem scrubOk (adx : Bool) : ∃ h : VG.Taint.Hint X86_64.RTaint.FT,
    (VG.Taint.check X86_64.RTaint.rtaint (X86_64.RScrub.init Spec.EcKey.P521.inst.validatePublicKeyApi.sig 8 [])
      (code adx) h).any (X86_64.RScrub.resOkB · 8 (scrubKs adx) (Impl.Scrub.X86_64.chunks 8)) = true := by
  cases adx <;> exact X86_64.RScrub.Analysed.ok_of _ (by taint_decide)

/-- `vg_ec_p521_validate_public_key`, or its `_adx` variant, followed by
`Impl.Scrub.X86_64.scrubTail` (`X86_64.RScrub.withScrub`): it returns without
secret residue. -/
def scrubReg (hI : InvSounds) (adx : Bool) :
    Registration Spec.EcKey.P521.inst.validatePublicKeyApi target :=
  X86_64.RScrub.withScrub {
    suffix := if adx then "_adx" else ""
    code := code adx
    verified := verified hI adx
    stack := 8 }
    (EcKey.X86_64.Scrub.validateOut _ _) [] (X86_64.RScrub.pubOk_nil _)
    (some ⟨scrubKs adx, scrubOk adx⟩)

end VG.Proof.EcKey.Validate.X86_64.P521
