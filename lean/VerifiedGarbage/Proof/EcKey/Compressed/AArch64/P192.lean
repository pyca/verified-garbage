module

public import VerifiedGarbage.Impl.EcKey.P192.AArch64
public import VerifiedGarbage.Proof.EcKey.AArch64.Scrub
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Main
public import VerifiedGarbage.Spec.EcKey.P192
import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Config
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Weierstrass.AArch64.P192Literals
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.P192Literals
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.AArch64
meta import VerifiedGarbage.Impl.Ecdsa.P192.AArch64
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
meta import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Contract
public import VerifiedGarbage.Impl.EcKey.Compressed.AArch64
public import VerifiedGarbage.Impl.Ecdsa.P192.AArch64
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Contract
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec

/-! # Instantiate shared compression with P-192's field configuration -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64.P192

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64
open VG.Proof.Ecdsa.AArch64.P192

abbrev code : Prog isa := Impl.EcKey.Compressed.AArch64.compress p192

materialize_shared baseline := code

 theorem ct : ConstantTime isa (compressContract Spec.P192.curve).pre
    (compressContract Spec.P192.curve).pub code := by
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

 theorem sat : ∃ s, (Spec.EcKey.P192.inst.compressPublicKeyContract abi 0).pre s := by
  have hlen : Spec.P192.curve.len = 24 := rfl
  sig_implies_sat [Spec.EcKey.P192.inst, Spec.EcKey.Instance.compressPublicKeyContract,
    Spec.EcKey.Instance.compressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argRegs, satState] [satState] using (satState 24)

 theorem verified (hI : Proof.Weierstrass.AArch64.InvSounds) :
    Verified target code (Spec.EcKey.P192.inst.compressPublicKeyContract abi 0) :=
  Verified.of_correct (compress_correct p192 (p192_ok hI)
    (by lit_decide) (by lit_decide) (by lit_decide)) ct (compress_implies _ sat)

/-- `vg_ec_p192_compress_public_key` as it is emitted, its cleanup included
(`Impl.EcKey.AArch64.Fn.compressP192`), meets its contract in constant time and
returns without secret residue. -/
theorem scrubbed (hI : Proof.Weierstrass.AArch64.InvSounds) :
    VerifiedScrubbed AArch64.target Impl.EcKey.AArch64.Fn.compressP192
      (Spec.EcKey.P192.inst.compressPublicKeyContract abi 0) 32 :=
  AArch64.Scrub.verifiedScrubbedAll (api := Spec.EcKey.P192.inst.compressPublicKeyApi)
    { code := code, verified := verified hI } _
    (Proof.EcKey.AArch64.Scrub.compressOk _) (by dsimp only; lit_decide)

end VG.Proof.EcKey.Compressed.AArch64.P192
