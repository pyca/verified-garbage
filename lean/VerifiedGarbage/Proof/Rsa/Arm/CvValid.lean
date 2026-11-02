module

public import VerifiedGarbage.Proof.Rsa.Arm.CvFinish
import VerifiedGarbage.Proof.Rsa.Arm.CvLoads
import VerifiedGarbage.Proof.Rsa.Arm.InvParts
import VerifiedGarbage.Proof.Framework.Block

/-! # `vg_rsa_crt_values` on ARMv7: a valid modulus (`valid_ok`) -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Rsa.Arm.Keys VG.Proof.Bignum.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm

/-- What a valid modulus leaves. -/
def ValidPost (s0 t : State) : Prop := ∃ X₁ X₂ V R₂ R₃ X : Nat,
  (0 < cvP s0 → X₁ = cvN s0 / cvP s0 ∧ X₂ = cvN s0 % cvP s0) ∧
  (1 < cvM s0 → V = Nat.gcd (cvQ s0) (cvM s0) ∧ (cvM s0 : Int) ∣ (X : Int) * cvQ s0 - V ∧ X < cvM s0) ∧
  (0 < 2 * (cvP s0 / 2) → R₂ = cvD s0 % (2 * (cvP s0 / 2))) ∧
  (0 < 2 * (cvQ s0 / 2) → R₃ = cvD s0 % (2 * (cvQ s0 / 2))) ∧
  Outs s0 t (maskOf (cvP s0) (cvQ s0) X₁ X₂ V) R₂ R₃ X

theorem valid_ok [VG.Proof.Rsa.Arm.Keys.InvLaw] {s0 s : State} (h : Base s0 s) : WP isa valid s (ValidPost s0) := by
  unfold valid
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (loads_ok h) fun t1 h1 => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (WP.seq_iff.mp (divN_ok h1)) fun u hu => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono hu fun t2 h2 => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _), checks_eq]
  refine (wp_seqs_append (by unfold checksA invSetup; simp) (by unfold checksB; simp)).mpr
    (WP.mono (checksA_ok h2) fun t3 h3 => WP.mono (checksB_ok h3) fun t4 h4 => ?_)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (divP_ok h4) fun t5 h5 => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (WP.seq_iff.mp (divQ_ok h5)) fun u' hu' => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono hu' fun t6 h6 => ?_
  rw [show seqs [Code.block (ctx ++ [Instr.ldr .r10 .r8 sDp, Instr.ldr .r12 .r8 sDq]), stores] =
    .seq (.block glue) stores from rfl]
  refine WP.mono (finish_ok h6) fun t ⟨V, iV, outs⟩ => ?_
  exact ⟨_, _, V, _, _, _, h2.div, iV, h6.dp, h6.dq, outs⟩

end VG.Proof.Rsa.Arm.CrtValues
