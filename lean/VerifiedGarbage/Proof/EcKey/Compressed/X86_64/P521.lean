module

import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
public import VerifiedGarbage.Proof.EcKey.X86_64.Scrub.Out
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.EcKey.X86_64.Scrub.Out
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.EcKey.P521
public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.Main
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.InverseVerified
public import VerifiedGarbage.Spec.EcKey.P521
import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.InverseLit
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.X86_64
meta import VerifiedGarbage.Impl.Ecdsa.P521.X86_64
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.InverseVerified
public import VerifiedGarbage.Impl.EcKey.Compressed.X86_64
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.Main
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec

/-! # P521: instantiate the shared public-point compression proof -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64.P521

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64.P521

abbrev code (adx : Bool) : Prog isa := Impl.EcKey.Compressed.X86_64.compress (Inverse.cfg adx)

materialize_shared baseline := code false
materialize_shared accelerated := code true

theorem inlineOk (adx : Bool) : (code adx).InlineOk = true := by
  cases adx <;> lit_decide

theorem hmx (adx : Bool) : (code adx).allInstrs (fun i => !loadsMxcsr i) = true := by
  cases adx <;> lit_decide

theorem ct (adx : Bool) : ConstantTime isa (compressContract Spec.P521.curve).pre
    (compressContract Spec.P521.curve).pub (code adx) := by
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

theorem sat : ∃ s, (Spec.EcKey.P521.inst.compressPublicKeyContract abi 8).pre s := by
  sig_implies_sat [Spec.EcKey.P521.inst, Spec.EcKey.Instance.compressPublicKeyContract,
    Spec.EcKey.Instance.compressPublicKeySig, Spec.P521.curve, Spec.EcKey.scratchWords,
    abi, argRegs, satState] [satState] using (satState Spec.P521.curve.len)

theorem verified (hI : InvSounds) (adx : Bool) :
    Verified target (code adx) (Spec.EcKey.P521.inst.compressPublicKeyContract abi 8) := by
  have hc := (Inverse.cfg_ok hI adx).toBaseCfgOk
  refine Verified.of_inline_ct (inlineOk adx)
    (by simpa only [Inverse.cfg_C] using (compress_correct (Inverse.cfg adx) hc (inlineOk adx) (hmx adx))) (ct adx)
    (compress_implies Spec.EcKey.P521.inst sat) (fun _ hs => Sig.clear_of_pre hs) ?_
  intro s b hv u hs hp
  exact compress_post_patch _ s b hv u (compress_implies _ sat |>.pre s hs)
    (Sig.clear_of_pre hs) hp

/-! ## Without secret residue -/

theorem codeSp (adx : Bool) : (code adx).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  cases adx <;> sp_safe

/-- `vg_ec_p521_compress_public_key`, or its `_adx` variant, as emitted (`Impl.EcKey.Compressed.X86_64.Fn.compress`), its cleanup
included, meets its contract in constant time and returns without secret residue. -/
theorem scrubbed (hI : InvSounds) (adx : Bool) :
    VerifiedScrubbed target (Impl.EcKey.Compressed.X86_64.Fn.compress (Inverse.cfg adx))
      (Spec.EcKey.P521.inst.compressPublicKeyApi.contract abi 8) 32 := by
  cases adx <;>
  exact X86_64.Scrub.verifiedScrubbedAll (api := Spec.EcKey.P521.inst.compressPublicKeyApi)
    { code := code _
      verified := verified hI _
      stack := 8
      spSafe := codeSp _ } .sse (EcKey.X86_64.Scrub.compressOut _ _)

theorem spSafe (adx : Bool) :
    (Impl.EcKey.Compressed.X86_64.Fn.compress (Inverse.cfg adx)).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  X86_64.Scrub.scrubKs_spSafe (codeSp adx)

end VG.Proof.EcKey.Compressed.X86_64.P521
