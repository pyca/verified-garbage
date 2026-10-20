module
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCall
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignRunning

import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignAttempt
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSampleLoop

/-! Functional correctness and termination of the outer signing retry loop. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64
open VG.Proof.Dsa.Random
open VG.Proof.Dsa (RandomSignResultRel randomSignRemaining randomSignDraw)

def RandomSignLoopPost {extra : Nat} {s : State} (h : RandomSignABI extra s)
    (hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)) (start : Nat) (result : Spec.Dsa.RandomSignResult) (t : State) : Prop :=
  (∃ fuel, RandomSignRunning h hq (start + result.used) fuel t) ∧
  word t.mem (randomBase s) Random.oStatus = BitVec.ofNat 64 result.status ∧
  (result.status = 1 → Spec.Rsa.bytesAt t.mem (s.gpr .x0) (s.gpr .x1).toNat =
    result.signature.getD (List.replicate (s.gpr .x1).toNat 0))

def RandomSignLoopInv {extra : Nat} {s : State} (h : RandomSignABI extra s)
    (hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)) (start : Nat) (result : Spec.Dsa.RandomSignResult)
    (fuel : Nat) (t : State) : Prop :=
  0 < fuel ∧ fuel ≤ 8 ∧ ∃ used, RandomSignRunning h hq used fuel t ∧
    RandomSignResultRel (randomInput s) start result used fuel

private theorem sample_none_status {draw : VG.Spec.Dsa.Random.Sample} (h : draw.scalar = none) :
    sampleStatus draw ≠ 1 ∧ (BitVec.ofNat 64 (sampleStatus draw) : BitVec 64) ≠ 4 := by
  simp only [sampleStatus, h]
  split <;> decide

private theorem attempt_progress (v : Backend) {s t : State} {h : RandomSignABI v.stack s}
    {hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {start fuel : Nat} {result : Spec.Dsa.RandomSignResult}
    (hi : RandomSignLoopInv h hq start result fuel t) :
    WP isa (RandomSign.attempt (randomSignerName v) (SignVerify.sign v.mul)) t fun u =>
      Scr u (randomBase s) Random.frameBytes ∧ u.sp = randomBase s ∧
      ((word u.mem (randomBase s) Random.oStatus ≠ 4 ∧ RandomSignLoopPost h hq start result u) ∨
        (word u.mem (randomBase s) Random.oStatus = 4 ∧ ∃ k < fuel, RandomSignLoopInv h hq start result k u)) := by
  obtain ⟨hpos, hbound, used, hr, hrel⟩ := hi
  cases fuel with
  | zero => omega
  | succ fuel =>
    refine WP.mono (random_sign_attempt v hr hpos (by omega)) fun u hu => ?_
    cases hc : (randomSignDraw (randomInput s) used).scalar with
    | none =>
      simp only [RandomSignAttemptPost, hc] at hu
      obtain ⟨hr', hs⟩ := hu
      obtain ⟨_, _, hready⟩ := hr'.ready
      obtain ⟨_, hstatus, hused⟩ := hrel.sample_none hc
      have hne := sample_none_status hc
      refine ⟨hready.scr, hready.sp, Or.inl ⟨by rw [hs]; exact hne.2,
        ⟨fuel + 1, by rw [hused]; exact hr'⟩, by rw [hs, hstatus], ?_⟩⟩
      intro he
      exact False.elim (hne.1 (hstatus.symm.trans he))
    | some k =>
      simp only [RandomSignAttemptPost, hc] at hu
      cases hs : randomSingleResult s k with
      | some sig =>
        simp only [hs, Option.isSome_some, ite_true] at hu
        obtain ⟨hr', hword, hout⟩ := hu
        obtain ⟨_, _, hready⟩ := hr'.ready
        obtain ⟨hsig, hstatus, hused⟩ := hrel.success hc hs
        refine ⟨hready.scr, hready.sp, Or.inl ⟨by rw [hword]; decide,
          ⟨fuel + 1, by rw [hused]; exact hr'⟩, by rw [hword, hstatus]; rfl,
          fun _ => ?_⟩⟩
        rw [hsig]
        exact hout
      | none =>
        simp only [hs, Option.isSome_none, Bool.false_eq_true, ite_false, Nat.add_sub_cancel] at hu
        obtain ⟨hr', hword, _⟩ := hu
        obtain ⟨_, _, hready⟩ := hr'.ready
        have hrel' := hrel.retry hc hs
        by_cases hz : fuel = 0
        · subst fuel
          obtain ⟨_, hstatus, hused⟩ := hrel'.exhausted
          refine ⟨hready.scr, hready.sp, Or.inl ⟨by rw [hword]; decide,
            ⟨0, by rw [hused]; exact hr'⟩, by rw [hword, hstatus]; rfl, ?_⟩⟩
          intro he
          omega
        · have hn : fuel + 1 ≠ 1 := by omega
          refine ⟨hready.scr, hready.sp, Or.inr ⟨by rw [hword, ite_eq_right hn], fuel,
            by omega, by omega, by omega, used + (randomSignDraw (randomInput s) used).used, hr', hrel'⟩⟩

theorem random_sign_loop_correct (v : Backend) {s t : State} {h : RandomSignABI v.stack s}
    {hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)} {used fuel : Nat}
    (hr : RandomSignRunning h hq used fuel t) (hpos : 0 < fuel) (hbound : fuel ≤ 8) :
    WP isa (.loop (.seq (RandomSign.attempt (randomSignerName v) (SignVerify.sign v.mul))
      (.block (Random.statusTest 4))) (.zero .x .x4)) t
      (RandomSignLoopPost h hq used (randomSignRemaining (randomInput s) used fuel)) := by
  apply random_statusLoop_rule _ (randomBase s) (RandomSignLoopInv h hq used (randomSignRemaining (randomInput s) used fuel))
  · intro n a b ⟨hp, hb, k, hk, hrel⟩ hm hkeep
    exact ⟨hp, hb, k, hk.congr hm hkeep, hrel⟩
  · intro a b ⟨⟨n, hn⟩, hs, hout⟩ hm hkeep
    exact ⟨⟨n, hn.congr hm hkeep⟩, by rw [hm]; exact hs, fun h => by rw [hm]; exact hout h⟩
  · intro n a ha
    exact attempt_progress v ha
  · exact ⟨hpos, hbound, used, hr, RandomSignResultRel.refl _ _ _⟩

end VG.Proof.Dsa.AArch64
