module

public import VerifiedGarbage.Impl.EcKey.BrainpoolP384r1.AArch64
public import VerifiedGarbage.Proof.EcKey.AArch64.Scrub
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Main
public import VerifiedGarbage.Spec.EcKey.BrainpoolP384r1
import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP384r1.Config
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Weierstrass.AArch64.BrainpoolP384r1Literals
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.BrainpoolP384r1Literals
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.AArch64
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.AArch64
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
meta import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Contract
public import VerifiedGarbage.Impl.EcKey.Compressed.AArch64
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.AArch64
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Contract
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec

/-! # Instantiate shared compression with BrainpoolP384r1's field configuration -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64.BrainpoolP384r1

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64
open VG.Proof.Ecdsa.AArch64.BrainpoolP384r1

abbrev code : Prog isa := Impl.EcKey.Compressed.AArch64.compress brainpoolp384r1

materialize_shared baseline := code

 theorem ct : ConstantTime isa (compressContract Spec.BrainpoolP384r1.curve).pre
    (compressContract Spec.BrainpoolP384r1.curve).pub code := by
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

 theorem sat : ∃ s, (Spec.EcKey.BrainpoolP384r1.inst.compressPublicKeyContract abi 0).pre s := by
  sig_implies_sat [Spec.EcKey.BrainpoolP384r1.inst, Spec.EcKey.Instance.compressPublicKeyContract,
    Spec.EcKey.Instance.compressPublicKeySig, Spec.BrainpoolP384r1.curve, Spec.EcKey.scratchWords,
    abi, argRegs, satState] [satState] using (satState Spec.BrainpoolP384r1.curve.len)

 theorem verified (hI : Proof.Weierstrass.AArch64.InvSounds) :
    Verified target code (Spec.EcKey.BrainpoolP384r1.inst.compressPublicKeyContract abi 0) :=
  Verified.of_correct (compress_correct brainpoolp384r1 (brainpoolp384r1_ok hI)
    (by lit_decide) (by lit_decide) (by lit_decide)) ct (compress_implies _ sat)

/-- `vg_ec_brainpoolp384r1_compress_public_key` as it is emitted, its cleanup included
(`Impl.EcKey.AArch64.Fn.compressBrainpoolP384r1`), meets its contract in constant time and
returns without secret residue. -/
theorem scrubbed (hI : Proof.Weierstrass.AArch64.InvSounds) :
    VerifiedScrubbed AArch64.target Impl.EcKey.AArch64.Fn.compressBrainpoolP384r1
      (Spec.EcKey.BrainpoolP384r1.inst.compressPublicKeyContract abi 0) 32 :=
  AArch64.ScrubAll.verifiedScrubbed (api := Spec.EcKey.BrainpoolP384r1.inst.compressPublicKeyApi)
    { code := code, verified := verified hI } _
    (Proof.EcKey.AArch64.Scrub.compressOk _) (by dsimp only; lit_decide)

end VG.Proof.EcKey.Compressed.AArch64.BrainpoolP384r1
