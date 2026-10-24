module

import VerifiedGarbage.Proof.Dsa.PPC64LE.RandomSign.Call
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Dsa.PPC64LE.RandomSign
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Ctx
public import VerifiedGarbage.Proof.Dsa.PPC64LE.RandomSign.Ctx
public import VerifiedGarbage.Spec.RsaPss

/-!
# Randomized DSA signing on PPC64LE: after a call of `vg_dsa_sign`

`callFinish_ok`: a signature leaves the status 1; a zero result spends an
attempt, and leaves the status 4 while one is left, else 0.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.RS

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random VG.Impl.Dsa.PPC64LE.RandomSign

theorem eval_zero_w (s : State) (r : Reg) : isa.eval (.zero .w r) s = some ((s.gpr r).setWidth 32 == 0) := by
  change VG.PPC64LE.eval (.zero .w r) s = _
  simp [VG.PPC64LE.eval, State.read, Size.bits]

theorem setWidth_beq_zero {x : BitVec 64} {st : Nat} (h : (x.setWidth 32).toNat = st) :
    (x.setWidth 32 == 0) = decide (st = 0) := by
  by_cases hs : st = 0
  · subst hs
    simp only [decide_true, beq_iff_eq]
    exact BitVec.eq_of_toNat_eq h
  · simp only [hs, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e
    rw [e] at h
    exact hs h.symm

/-- What `callFinish` leaves, after a call whose result's low word is `st`. -/
theorem callFinish_ok {s : State} {a st : Nat} (h26 : s.gpr .r26 = BitVec.ofNat 64 a) (ha : 1 ≤ a) (ha' : a ≤ 8)
    (h3 : ((s.gpr .r3).setWidth 32).toNat = st) :
    WP isa callFinish s fun t =>
      t.mem = s.mem ∧ Keep [.r26, .r31] s t ∧
        (st ≠ 0 → t.gpr .r31 = BitVec.ofNat 64 1 ∧ t.gpr .r26 = s.gpr .r26) ∧
        (st = 0 → t.gpr .r26 = BitVec.ofNat 64 (a - 1) ∧
          t.gpr .r31 = BitVec.ofNat 64 (if a - 1 = 0 then 0 else 4)) := by
  unfold callFinish
  refine WP.ite (decide (st = 0)) (by rw [eval_zero_w, setWidth_beq_zero h3]) (fun hz => ?_) (fun hz => ?_)
  · simp only [decide_eq_true_eq] at hz
    refine WP.seq (WP.mono (WP.keep [.r26] (Q := fun t => t.mem = s.mem ∧ t.gpr .r26 = BitVec.ofNat 64 (a - 1))
      (by prun [h26, VG.Offset.ofNat_sub_ofNat ha]) (by decide)) fun t₁ ⟨⟨m1, a26⟩, k1⟩ => ?_)
    refine WP.ite (decide (a - 1 ≠ 0)) (eval_nonzero_ofNat' _ _ (by omega) a26) (fun hn => ?_) (fun hn => ?_)
    · simp only [decide_eq_true_eq] at hn
      refine WP.mono (WP.keep [.r31] (Q := fun t => t.mem = t₁.mem ∧ t.gpr .r31 = BitVec.ofNat 64 4) (by prun)
        (by decide)) fun t ⟨⟨tm, t31⟩, k2⟩ => ⟨tm.trans m1, (k1.trans k2).mono (by decide), fun h => absurd hz h,
          fun _ => ⟨(k2.gpr _ (by decide)).trans a26, by rw [t31, ite_eq_right hn]⟩⟩
    · simp only [decide_eq_false_iff_not, Decidable.not_not] at hn
      refine WP.mono (WP.keep [.r31] (Q := fun t => t.mem = t₁.mem ∧ t.gpr .r31 = BitVec.ofNat 64 0) (by prun)
        (by decide)) fun t ⟨⟨tm, t31⟩, k2⟩ => ⟨tm.trans m1, (k1.trans k2).mono (by decide), fun h => absurd hz h,
          fun _ => ⟨(k2.gpr _ (by decide)).trans a26, by rw [t31, ite_eq_left hn]⟩⟩
  · simp only [decide_eq_false_iff_not] at hz
    refine WP.mono (WP.keep [.r31] (Q := fun t => t.mem = s.mem ∧ t.gpr .r31 = BitVec.ofNat 64 1) (by prun)
      (by decide)) fun t ⟨⟨tm, t31⟩, k⟩ => ⟨tm, k.mono (by decide), fun _ => ⟨t31, k.gpr _ (by decide)⟩,
        fun h => absurd h hz⟩

end VG.Proof.Dsa.PPC64LE.RS
