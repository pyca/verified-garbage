module

public import VerifiedGarbage.Proof.Rsa.Arm.CvFinish
import VerifiedGarbage.Proof.Rsa.Arm.CvLoads
public import VerifiedGarbage.Proof.Rsa.Arm.CvWords
public import VerifiedGarbage.Proof.Rsa.KeyCheckWords
import VerifiedGarbage.Proof.Rsa.KeyCheckMath
import VerifiedGarbage.Proof.Rsa.Arm.CvSpec
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

theorem Outs.congr {s0 t : State} {c : Bool} {R₂ R₃ R₂' R₃' X : Nat} (o : Outs s0 t c R₂ R₃ X)
    (e₂ : c = true → R₂ = R₂') (e₃ : c = true → R₃ = R₃') : Outs s0 t c R₂' R₃' X := by
  cases c
  · exact ⟨o.done, o.ret, o.dp, o.dq, o.qi⟩
  · rw [← e₂ rfl, ← e₃ rfl]; exact o

/-- For a balanced key, `p q < 2^(32 w)`. -/
theorem pq_lt {s0 : State} (hB : BalCv s0) (hp : cvP s0 < 2 ^ (32 * (cvW s0 / 2)))
    (hq : cvQ s0 < 2 ^ (32 * (cvW s0 / 2))) : cvP s0 * cvQ s0 < 2 ^ (32 * cvW s0) := by
  have hW : (2 : Nat) ^ (32 * cvW s0) = 2 ^ (32 * (cvW s0 / 2)) * 2 ^ (32 * (cvW s0 / 2)) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hW]; exact VG.Proof.Rsa.mul_lt_sq hp hq

/-- The mask of a balanced key's checks is that of the division of `n` by `p`. -/
theorem maskW_eq {s0 : State} (hm : Spec.Rsa.modulusValid (cvN s0) (cvK s0) = true) (hB : BalCv s0)
    (hp : cvP s0 < 2 ^ (32 * (cvW s0 / 2))) (hq : cvQ s0 < 2 ^ (32 * (cvW s0 / 2))) (V : Nat) :
    maskOf (cvP s0) (cvQ s0) (xW s0) 0 V = maskOf (cvP s0) (cvQ s0) (cvN s0 / cvP s0) (cvN s0 % cvP s0) V := by
  have hN := (VG.Proof.Rsa.modulusValid_facts hm).1
  simp only [xW, Nat.mod_eq_of_lt (pq_lt hB hp hq)]
  by_cases e : cvP s0 * cvQ s0 = cvN s0
  · obtain ⟨a, b, c⟩ := (pq_iff hN).mpr e
    simp only [e, ↓reduceIte, maskOf, VG.Proof.Rsa.CrtValues.maskOf, b, c]
  · have r : ¬(cvP s0 % 2 = 1 ∧ cvN s0 / cvP s0 = cvQ s0 ∧ cvN s0 % cvP s0 = 0) := fun h => e ((pq_iff hN).mp h)
    simp only [e, ↓reduceIte, maskOf, VG.Proof.Rsa.CrtValues.maskOf]
    rw [decide_eq_false (by omega), decide_eq_false (fun ⟨a, b, c, _⟩ => r ⟨a, b, c⟩)]

/-- Under the mask, a balanced key's remainders by words are those modulo `p - 1` and `q - 1`. -/
theorem remW_eq {s0 : State} (hm : Spec.Rsa.modulusValid (cvN s0) (cvK s0) = true) (hB : BalCv s0)
    (hp : cvP s0 < 2 ^ (32 * (cvW s0 / 2))) (hq : cvQ s0 < 2 ^ (32 * (cvW s0 / 2))) {V : Nat}
    (w16 : 16 ≤ cvW s0) (hc : maskOf (cvP s0) (cvQ s0) (xW s0) 0 V = true) :
    VG.Proof.Rsa.fixT (cvW s0 / 2) (2 * (cvP s0 / 2)) = 2 * (cvP s0 / 2) ∧
      VG.Proof.Rsa.fixT (cvW s0 / 2) (2 * (cvQ s0 / 2)) = 2 * (cvQ s0 / 2) := by
  have e : cvP s0 * cvQ s0 = cvN s0 := by
    simp only [xW, Nat.mod_eq_of_lt (pq_lt hB hp hq), maskOf, VG.Proof.Rsa.CrtValues.maskOf,
      decide_eq_true_eq] at hc
    by_contra n
    simp [n] at hc
  obtain ⟨-, a, b⟩ := VG.Proof.Rsa.top_words hm rfl (by simp only [cvW] at w16; omega) hp hq e
  exact ⟨VG.Proof.Rsa.fixT_of_ge a, VG.Proof.Rsa.fixT_of_ge b⟩

theorem valid_ok [VG.Proof.Rsa.Arm.Keys.InvLaw] {s0 s : State} (h : Base s0 s)
    (hm : Spec.Rsa.modulusValid (cvN s0) (cvK s0) = true) : WP isa valid s (ValidPost s0) := by
  unfold valid
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (loads_ok h) fun t1 h1 => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (shapeCv_ok h1) fun t2 ⟨h2, z2⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  rw [show seqs [Code.block (ctx ++ [Instr.ldr .r10 .r8 sDp, Instr.ldr .r12 .r8 sDq]), stores] =
    .seq (.block glue) stores from rfl]
  refine WP.ite t2.z rfl (fun hz => ?_) (fun _ => ?_)
  · -- A balanced key.
    rw [z2] at hz
    have hB : BalCv s0 := of_decide_eq_true hz
    have hp : cvP s0 < 2 ^ (32 * (cvW s0 / 2)) :=
      bytes_lt_half (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact hB.1) hB.2.2
    have hq : cvQ s0 < 2 ^ (32 * (cvW s0 / 2)) :=
      bytes_lt_half (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact hB.2.1) hB.2.2
    refine WP.mono (midW_ok h2 hB) fun t3 ⟨h3, e2, e3⟩ => ?_
    refine WP.mono (finish_ok h3) fun t ⟨V, iV, outs⟩ => ?_
    refine ⟨_, _, V, _, _, _, fun _ => ⟨rfl, rfl⟩, iV, fun _ => rfl, fun _ => rfl, ?_⟩
    rw [← maskW_eq hm hB hp hq V]
    exact outs.congr (fun hc => by rw [e2, fP, (remW_eq hm hB hp hq h.pre.w16.1 hc).1])
      (fun hc => by rw [e3, fQ, (remW_eq hm hB hp hq h.pre.w16.1 hc).2])
  · -- Any key: `n` divided by `p`.
    unfold midD
    rw [wp_seqs_cons (List.cons_ne_nil _ _)]
    refine WP.mono (WP.seq_iff.mp (divN_ok h2)) fun u hu => ?_
    rw [wp_seqs_cons (List.cons_ne_nil _ _)]
    refine WP.mono hu fun t3 h3 => ?_
    rw [wp_seqs_cons (List.cons_ne_nil _ _), checks_eq]
    refine (wp_seqs_append (by unfold checksA invSetup; simp) (by unfold checksB; simp)).mpr
      (WP.mono (checksA_ok h3) fun t4 h4 => WP.mono (checksB_ok h4) fun t5 h5 => ?_)
    rw [wp_seqs_cons (List.cons_ne_nil _ _)]
    refine WP.mono (divP_ok h5) fun t6 h6 => ?_
    rw [wp_seqs_cons (List.cons_ne_nil _ _)]
    refine WP.mono (WP.seq_iff.mp (divQ_ok h6)) fun u' hu' => ?_
    refine WP.mono hu' fun t7 h7 => ?_
    refine WP.mono (finish_ok h7.toM) fun t ⟨V, iV, outs⟩ => ?_
    exact ⟨_, _, V, _, _, _, h3.div, iV, h7.dp, h7.dq, outs⟩

end VG.Proof.Rsa.Arm.CrtValues
