module

import VerifiedGarbage.Proof.EcKey.Validate.X86_64.Main
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P192.InverseVerified
public import VerifiedGarbage.Spec.EcKey.P192
import VerifiedGarbage.Proof.Ecdsa.X86_64.P192.InverseLit
import VerifiedGarbage.Proof.Ecdh.X86_64.P192.CheckVerified
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Impl.EcKey.Validate.X86_64
meta import VerifiedGarbage.Impl.Ecdsa.P192.X86_64
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P192.InverseVerified
public import VerifiedGarbage.Impl.EcKey.Validate.X86_64
public import VerifiedGarbage.Proof.EcKey.Validate.X86_64.Contract
meta import VerifiedGarbage.Proof.EcKey.Validate.X86_64.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec

/-! # P192: instantiate the shared encoded-point validation proof -/

@[expose] public section

namespace VG.Proof.EcKey.Validate.X86_64.P192

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64.P192

abbrev code (adx : Bool) : Prog isa := Impl.EcKey.Validate.X86_64.validate (Inverse.cfg adx)

materialize_shared baseline := code false

theorem inlineOk (adx : Bool) : (code adx).InlineOk = true := by
  cases adx <;> lit_decide

theorem hmx (adx : Bool) : (code adx).allInstrs (fun i => !loadsMxcsr i) = true := by
  cases adx <;> lit_decide

theorem ct (adx : Bool) : ConstantTime isa (keyContract Spec.P192.curve).pre
    (keyContract Spec.P192.curve).pub (code adx) := by
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

theorem sat : ∃ s, (Spec.EcKey.P192.inst.validatePublicKeyContract abi 8).pre s := by
  sig_implies_sat [Spec.EcKey.P192.inst, Spec.EcKey.Instance.validatePublicKeyContract,
    Spec.EcKey.Instance.validatePublicKeySig, Spec.P192.curve, Spec.EcKey.scratchWords,
    abi, argRegs, satState] [satState] using (satState Spec.P192.curve.len)

theorem verified (hI : InvSounds) (adx : Bool) :
    Verified target (code adx) (Spec.EcKey.P192.inst.validatePublicKeyContract abi 8) := by
  have hc := Inverse.cfg_ok hI adx
  refine Verified.of_inline_ct (inlineOk adx)
    (by simpa only [Inverse.cfg_C] using (correct (Inverse.cfg adx) hc (inlineOk adx) (hmx adx))) (ct adx)
    (implies Spec.EcKey.P192.inst sat) (fun _ hs => Sig.clear_of_pre hs) ?_
  intro s b hv u _ hp
  simpa only [keyContract, State.patch_gpr] using hp

end VG.Proof.EcKey.Validate.X86_64.P192
