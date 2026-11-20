module

import VerifiedGarbage.Proof.Framework.X86_64.ScrubFn
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
public import VerifiedGarbage.Proof.EcKey.X86_64.Scrub.Out
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.EcKey.X86_64.Scrub.Out
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.EcKey.P224
public import VerifiedGarbage.Proof.EcKey.Validate.X86_64.Main
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.InverseVerified
public import VerifiedGarbage.Spec.EcKey.P224
import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.InverseLit
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Impl.EcKey.Validate.X86_64
meta import VerifiedGarbage.Impl.Ecdsa.P224.X86_64
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.InverseVerified
public import VerifiedGarbage.Impl.EcKey.Validate.X86_64
meta import VerifiedGarbage.Proof.EcKey.Validate.X86_64.Main
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec

/-! # P224: instantiate the shared encoded-point validation proof -/

@[expose] public section

namespace VG.Proof.EcKey.Validate.X86_64.P224

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64.P224

abbrev code (adx : Bool) : Prog isa := Impl.EcKey.Validate.X86_64.validate (Inverse.cfg adx)

materialize_shared baseline := code false

theorem inlineOk (adx : Bool) : (code adx).InlineOk = true := by
  cases adx <;> lit_decide

theorem hmx (adx : Bool) : (code adx).allInstrs (fun i => !loadsMxcsr i) = true := by
  cases adx <;> lit_decide

theorem ct (adx : Bool) : ConstantTime isa (keyContract Spec.P224.curve).pre
    (keyContract Spec.P224.curve).pub (code adx) := by
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

theorem sat : ∃ s, (Spec.EcKey.P224.inst.validatePublicKeyContract abi 8).pre s := by
  sig_implies_sat [Spec.EcKey.P224.inst, Spec.EcKey.Instance.validatePublicKeyContract,
    Spec.EcKey.Instance.validatePublicKeySig, Spec.P224.curve, Spec.EcKey.scratchWords,
    abi, argRegs, satState] [satState] using (satState Spec.P224.curve.len)

theorem verified (hI : InvSounds) (adx : Bool) :
    Verified target (code adx) (Spec.EcKey.P224.inst.validatePublicKeyContract abi 8) := by
  have hc := Inverse.cfg_ok hI adx
  refine Verified.of_inline_ct (inlineOk adx)
    (by simpa only [Inverse.cfg_C] using (correct (Inverse.cfg adx) hc (inlineOk adx) (hmx adx))) (ct adx)
    (implies Spec.EcKey.P224.inst sat) (fun _ hs => Sig.clear_of_pre hs) ?_
  intro s b hv u _ hp
  simpa only [keyContract, State.patch_gpr] using hp

/-! ## Without secret residue -/

theorem codeSp : (code false).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `vg_ec_p224_validate_public_key` as emitted (`Impl.EcKey.Validate.X86_64.Fn.validate`), its cleanup included, meets its
contract in constant time and returns without secret residue. -/
theorem scrubbed (hI : InvSounds) :
    VerifiedScrubbed target (Impl.EcKey.Validate.X86_64.Fn.validate (Inverse.cfg false))
      (Spec.EcKey.P224.inst.validatePublicKeyApi.contract abi 8) 32 :=
  X86_64.Scrub.verifiedScrubbedAll (api := Spec.EcKey.P224.inst.validatePublicKeyApi)
    { code := code false
      verified := verified hI false
      stack := 8
      spSafe := codeSp } .sse (EcKey.X86_64.Scrub.validateOut _ _)

theorem spSafe : (Impl.EcKey.Validate.X86_64.Fn.validate (Inverse.cfg false)).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  X86_64.Scrub.scrubKs_spSafe codeSp

end VG.Proof.EcKey.Validate.X86_64.P224
