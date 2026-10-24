module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.RandomSign.Attempt
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Zero
import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Save
import VerifiedGarbage.Proof.Dsa.RandomSign
import VerifiedGarbage.Proof.Dsa.RandomSignResult
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# Randomized DSA signing on PPC64LE: the function

`randomSign_correct`: `vg_dsa_sign_random` meets `rsContract`. In its frame,
the entry (`entry_ok`), the scan of q (`prepareQ_ok`), the attempts
(`attempts_ok`, or none when `q ≤ 1`) and the exit (`finish_ok`) follow one
another; the result is `randomSignBytes`'s (`rsRes_eq`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.RS

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random VG.Impl.Dsa.PPC64LE.RandomSign
open VG.Proof.Mont
open VG.Proof.Dsa.PPC64LE.Rnd
open VG.Proof.Dsa (RandomSignInput RandomSignResultRel randomSignDraw randomSignRemaining)
open VG.Proof.Dsa.Random (sampleStatus)

theorem attempts_ok {s₀ : State} (h : rsContract.pre s₀) (hq : 1 < qOf s₀) :
    ∀ a u t, AttInv s₀ a u t → WP isa attempts t (AttOut s₀) := by
  intro a u t hi
  unfold attempts
  refine WP.loop (M := isa) (fun n (t : State) => ∃ u, AttInv s₀ n u t) (fun n t ⟨u, hi⟩ =>
    WP.mono (attempt_ok h hq hi) fun t' h' => ?_) a t ⟨u, hi⟩
  rcases h' with ⟨e, o⟩ | ⟨e, m, hm, u', hi'⟩
  · exact .inl ⟨e, o⟩
  · exact .inr ⟨e, m, hm, u', hi'⟩

/-- The specification's result is the attempts'. -/
theorem rsRes_eq {s₀ : State} (h : rsContract.pre s₀) : rsRes s₀ = resOf s₀ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    lv, -, hkl, -⟩ := h
  simp only [rsRes, resOf, randomSignRemaining, inpOf, randOf, Spec.Dsa.randomSignBytes, List.drop_zero]
  rw [ite_eq_right (by
    simp only [decide_eq_true lv, Bool.not_true, VG.Proof.Bignum.bytesAt_length, hkl, Bool.false_or,
      bne_self_eq_false, Bool.false_eq_true, not_false_eq_true])]
  simp only [rlOf, RL.kl, hkl]
  rfl

end VG.Proof.Dsa.PPC64LE.RS
