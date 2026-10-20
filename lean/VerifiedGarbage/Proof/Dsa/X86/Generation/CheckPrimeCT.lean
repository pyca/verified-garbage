module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.CheckTrialCT
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Weierstrass.Point
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Dsa.X86.Generation.CheckPrimeCTState
import VerifiedGarbage.Proof.Dsa.X86.Generation.CheckTrialCT

/-! # Trial acceptance gates the complete public-input primality engine -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp
open VG.Impl.Dsa.X86.Generation

theorem checkPrime_ct (G : PrimeConfig) (large : 8161 < G.modulus) : RelCT isa (Two (CheckPrimeAt G))
    (checkPrime G.len) (fun _ _ => True) := by
  unfold checkPrime
  refine RelCT.seq (checkTrial_ct G large) (RelCT.seq
    (two_piece (Ψ := fun p s => PrimeFromAt G p.frame s ∧
      s.zf = some (decide (Spec.RsaKeyGen.obviouslyComposite (8 * G.len) G.modulus = false)))
      [.eax] ?_ (by taint_decide) ?_) ?_)
  · intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hs.2.trans ht.2.symm
  · intro p s R
    refine wp_cmpi fun t st _ zf => WP.block_nil ?_
    refine ⟨R.1.keep st.mem (st.keeps []) (by simp), ?_⟩
    rw [zf, R.2]
    cases Spec.RsaKeyGen.obviouslyComposite (8 * G.len) G.modulus <;> decide +kernel
  · apply two_ite (fun _ _ _ hs ht => by simp only [eval, hs.2, ht.2])
    · exact two_map (fun p => p.frame) (fun _ _ h => h.1.1) (primeFromFrame_ct G)
    · refine two_taint [.esp] ?_ (by taint_decide)
      intro p s t hs ht
      exact frameAt_pins _ p.frame.frame s t hs.1.1.frame ht.1.1.frame
end VG.Proof.Dsa.X86.Generation
