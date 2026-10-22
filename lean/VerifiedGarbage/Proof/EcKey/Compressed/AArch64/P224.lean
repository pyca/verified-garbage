module

public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Main
public import VerifiedGarbage.Spec.EcKey.P224
public import VerifiedGarbage.Proof.Ecdsa.AArch64.P224.Verified
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Ecdh.AArch64.P224.CheckVerified
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.AArch64
meta import VerifiedGarbage.Impl.Ecdsa.P224.AArch64
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
meta import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Contract

/-! # Instantiate shared compression with P224's field configuration -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64.P224

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64
open VG.Proof.Ecdsa.AArch64.P224

abbrev code : Prog isa := Impl.EcKey.Compressed.AArch64.compress p224

materialize_shared baseline := code

 theorem ct : ConstantTime isa (compressContract Spec.P224.curve).pre
    (compressContract Spec.P224.curve).pub code := by
  apply VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2])
  · intro s₁ s₂ _ _ hp
    obtain ⟨hsp, hout, hpk, hws⟩ := hp
    refine ⟨hsp, ?_⟩
    intro r hr
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hout
    · exact hpk
    · exact hws
  · taint_decide

 theorem sat : ∃ s, (Spec.EcKey.P224.inst.compressPublicKeyContract abi 0).pre s := by
  have hlen : Spec.P224.curve.len = 28 := rfl
  sig_implies_sat [Spec.EcKey.P224.inst, Spec.EcKey.Instance.compressPublicKeyContract,
    Spec.EcKey.Instance.compressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argRegs, satState] [satState] using (satState 28)

 theorem verified (hI : Proof.Weierstrass.AArch64.InvSounds) :
    Verified target code (Spec.EcKey.P224.inst.compressPublicKeyContract abi 0) :=
  Verified.of_correct (compress_correct p224 (p224_ok hI).toBaseCfgOk
    (by lit_decide) (by lit_decide) (by lit_decide)) ct (compress_implies _ sat)

end VG.Proof.EcKey.Compressed.AArch64.P224
