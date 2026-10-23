module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Ready
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Write
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.TripleDes.PPC64LE
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (desCore)

/-- The word after the first `k` passes of the block. -/
def passesDone (keys : Nat → DesSchedule) (direction : Direction) (x : BitVec 64) :
    Nat → BitVec 64
  | 0 => x
  | k + 1 => desCore (keys (passOf direction (3 - k)).1) (passOf direction (3 - k)).2
      (passesDone keys direction x k)

def blockCore (keys : Nat → DesSchedule) (direction : Direction) (x : BitVec 64) : BitVec 64 :=
  match direction with
  | .encrypt => desCore (keys 2) .encrypt (desCore (keys 1) .decrypt (desCore (keys 0) .encrypt x))
  | .decrypt => desCore (keys 0) .decrypt (desCore (keys 1) .encrypt (desCore (keys 2) .decrypt x))

theorem blockCore_passesDone (keys : Nat → DesSchedule) (direction : Direction) (x : BitVec 64) :
    blockCore keys direction x = passesDone keys direction x 3 := by
  cases direction <;> rfl

/-- The loop's invariant, with `m` passes left. -/
structure BodyInv (keys : Nat → DesSchedule) (base : Addr) (direction : Direction)
    (x : BitVec 64) (origin : State) (m : Nat) (s : State) : Prop where
  pos : 1 ≤ m
  le : m ≤ 3
  passes : s.gpr .r19 = BitVec.ofNat 64 m
  word : WordState (passesDone keys direction x (3 - m)) s
  ready : Ready keys base s
  stable : Stable origin s

theorem blockBody_ok (keys : Nat → DesSchedule) (base : Addr) (s : State) (x : BitVec 64)
    (direction : Direction) (hready : Ready keys base s) (hword : WordState x s) :
    WP isa (blockBody direction) s
      (fun t => WordState (blockCore keys direction x) t ∧ Ready keys base t ∧ Stable s t) := by
  let s₁ := s.write .r19 (BitVec.ofNat 64 3)
  have hregs : ∀ r, r ≠ .r19 → s₁.gpr r = s.gpr r := fun r h => gpr_write_of_ne _ _ h
  have hframe : Frame [spillRegion s] s.mem s₁.mem := Frame.refl _ _
  have hstable : Stable s s₁ := ⟨rfl, rfl,
    fun q hq => hregs q (by revert hq; cases q <;> decide), hframe⟩
  apply WP.seq
  refine WP.of_runBlock ⟨s₁, ?_, ?_⟩
  · rw [runBlock_cons, imm, exec_li (by decide), runStep_some, runBlock_nil]
  refine WP.loop (M := isa) (BodyInv keys base direction x s) ?_ 3 s₁
    ⟨by decide, by decide, gpr_write_self _ _ _, ?_,
      hready.congr (hregs .r5 (by decide)) (hregs .r3 (by decide)) rfl rfl hframe, hstable⟩
  · rintro m t ⟨hpos, hle, hpasses, hw, hr, hst⟩
    refine WP.mono (pass_word_ok keys base t _ direction ⟨hpos, hle⟩ hr hw hpasses)
      fun u ⟨hwu, hru, hsu, hpu, hzu⟩ => ?_
    have hdone : desCore (keys (passOf direction m).1) (passOf direction m).2
        (passesDone keys direction x (3 - m)) = passesDone keys direction x (3 - (m - 1)) := by
      rw [show 3 - (m - 1) = 3 - m + 1 by omega, passesDone, show 3 - (3 - m) = m by omega]
    rw [hdone] at hwu
    by_cases hlast : m = 1
    · subst m
      refine Or.inl ⟨by rw [hzu]; rfl, ?_, hru, hst.trans hsu⟩
      rw [blockCore_passesDone]
      exact hwu
    · refine Or.inr ⟨by rw [hzu]; simp [hlast], m - 1, by omega,
        ⟨by omega, by omega, hpu, hwu, hru, hst.trans hsu⟩⟩
  · exact ⟨(hregs .r14 (by decide)).trans hword.left, (hregs .r15 (by decide)).trans hword.right⟩

end VG.Proof.TripleDes.PPC64LE
