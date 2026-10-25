module

import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Main
public import VerifiedGarbage.Spec.EcKey.Secp256k1
import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.Config
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Weierstrass.AArch64.Secp256k1Literals
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Secp256k1Literals
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.AArch64
meta import VerifiedGarbage.Impl.Ecdsa.Secp256k1.AArch64
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
meta import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Contract
public import VerifiedGarbage.Impl.EcKey.Compressed.AArch64
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.AArch64
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Contract
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec

/-! # Instantiate shared compression with Secp256k1's field configuration -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64.Secp256k1

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64
open VG.Proof.Ecdsa.AArch64.Secp256k1

abbrev code : Prog isa := Impl.EcKey.Compressed.AArch64.compress secp256k1

materialize_shared baseline := code

 theorem ct : ConstantTime isa (compressContract Spec.Secp256k1.curve).pre
    (compressContract Spec.Secp256k1.curve).pub code := by
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

 theorem sat : ∃ s, (Spec.EcKey.Secp256k1.inst.compressPublicKeyContract abi 0).pre s := by
  sig_implies_sat [Spec.EcKey.Secp256k1.inst, Spec.EcKey.Instance.compressPublicKeyContract,
    Spec.EcKey.Instance.compressPublicKeySig, Spec.Secp256k1.curve, Spec.EcKey.scratchWords,
    abi, argRegs, satState] [satState] using (satState Spec.Secp256k1.curve.len)

 theorem verified (hI : Proof.Weierstrass.AArch64.InvSounds) :
    Verified target code (Spec.EcKey.Secp256k1.inst.compressPublicKeyContract abi 0) :=
  Verified.of_correct (compress_correct secp256k1 (secp256k1_ok hI)
    (by lit_decide) (by lit_decide) (by lit_decide)) ct (compress_implies _ sat)

end VG.Proof.EcKey.Compressed.AArch64.Secp256k1
