module

public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.DecompressMain
public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Tonelli
import VerifiedGarbage.Proof.P224.Sqrt
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.LaneTaint
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneTaint
import VerifiedGarbage.Proof.Weierstrass.Sqrt
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
meta import VerifiedGarbage.Impl.EcKey.Compressed.AArch64.Decompress
meta import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Contract

/-! # Instantiate shared compression with P224's field configuration -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64.P224Decompress

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64
open VG.Proof.Ecdsa.AArch64.P224

 abbrev root (a : Spec.Weierstrass.Fe Spec.P224.curve) :=
  Impl.EcKey.Compressed.rootTonelli a ((Spec.P224.curve.p - 1) / 2 ^ 96) 96
    (Fin.ofNat Spec.P224.curve.p 11)

abbrev code : Prog isa := Impl.EcKey.Compressed.AArch64.decompress p224

materialize_shared baseline := code

 theorem ct : ConstantTime isa (decompressContract Spec.P224.curve root).pre
    (decompressContract Spec.P224.curve root).pub code := by
  apply VG.Taint.constantTime (A := LaneTaint.taint) (LaneTaint.ofRegs [.x0, .x1, .x2])
  · intro s₁ s₂ _ _ hp
    obtain ⟨hsp, hout, hpk, hws⟩ := hp
    refine ⟨⟨hsp, ?_⟩, by simp [LaneTaint.AgreeV, LaneTaint.ofRegs, LaneTaint.empty, LaneTaint.get]⟩
    intro r hr
    change r ∈ Taint.ofRegs [.x0, .x1, .x2] at hr
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hout
    · exact hpk
    · exact hws
  · taint_decide

 theorem sat : ∃ s, (Spec.EcKey.P224.inst.decompressPublicKeyContract abi 0).pre s := by
  have hlen : Spec.P224.curve.len = 28 := rfl
  sig_implies_sat [Spec.EcKey.P224.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
    Spec.EcKey.Instance.decompressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argRegs, decompressSatState] [decompressSatState] using (decompressSatState 28)

 theorem calls : CallsKeep code := by lit_decide
 theorem untouched : KeepsUntouched code := by lit_decide
 theorem vec : code.allInstrs keepsV = true := by lit_decide

 theorem chain_r : Proof.Weierstrass.AArch64.ChainOk
    (Impl.EcKey.Compressed.AArch64.rootChain p224
      ((Impl.EcKey.Compressed.AArch64.rootQ p224 + 1) / 2))
    ((Impl.EcKey.Compressed.AArch64.rootQ p224 + 1) / 2) := by
  apply Proof.Weierstrass.AArch64.ChainOk.of_check
  decide +kernel

 theorem chain_q : Proof.Weierstrass.AArch64.ChainOk
    (Impl.EcKey.Compressed.AArch64.rootChain p224 (Impl.EcKey.Compressed.AArch64.rootQ p224))
    (Impl.EcKey.Compressed.AArch64.rootQ p224) := by
  apply Proof.Weierstrass.AArch64.ChainOk.of_check
  decide +kernel

 theorem body_no_v27 : ∀ i ∈ instrs (Impl.EcKey.Compressed.AArch64.descentBody p224),
    vdstOf i ≠ some .v27 := by
  have h : (Impl.EcKey.Compressed.AArch64.descentBody p224).allInstrs
      (fun i => (vdstOf i).isNone) = true := by lit_decide
  intro i hi he
  have h' := List.all_eq_true.mp ((Code.allInstrs_eq _ _) ▸ h) i hi
  rw [he] at h'
  cases h'

 theorem verified (hL : Proof.Weierstrass.Law Spec.P224.curve)
    (hI : Proof.Weierstrass.AArch64.InvSounds) :
    Verified target code (Spec.EcKey.P224.inst.decompressPublicKeyContract abi 0) := by
  have hc := (p224_ok hI).toBaseCfgOk
  exact Verified.of_correct (decompress_correct p224 hc _
    (candidateTonelli_correct hc (by decide +kernel) (by decide +kernel) chain_r chain_q body_no_v27)
    (by lit_decide) (by lit_decide) (by lit_decide)) ct
    (decompress_implies Spec.EcKey.P224.inst _
      (Proof.P224.rootFacts hL) sat)

end VG.Proof.EcKey.Compressed.AArch64.P224Decompress
