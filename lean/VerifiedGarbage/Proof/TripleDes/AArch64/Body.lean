module

public import VerifiedGarbage.Proof.TripleDes.AArch64.Ready
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64
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
  passes : passesOf s = BitVec.ofNat 64 m
  word : WordState (passesDone keys direction x (3 - m)) s
  ready : Ready keys base s
  stable : Stable origin s

theorem blockBody_ok (keys : Nat → DesSchedule) (base : Addr) (s : State) (x : BitVec 64)
    (direction : Direction) (hready : Ready keys base s) (hword : WordState x s) :
    WP isa (blockBody direction) s
      (fun t => WordState (blockCore keys direction x) t ∧ Ready keys base t ∧ Stable s t) := by
  let s₀ := s.write .x .x3 ((BitVec.ofNat 16 3).setWidth 64)
  let s₁ := s₀.setV .v1 (ofVDwords (s₀.gpr .x3) (s₀.gpr .x3))
  have hbase : s₁.gpr .x2 = s.gpr .x2 := by
    simp only [s₁, s₀, gpr_setV, gpr_write, reduceCtorEq, ite_false]
  have hrd : s₁.rd = s.rd := by simp only [s₁, s₀, rd_setV, rd_write]
  have hwr : s₁.wr = s.wr := by simp only [s₁, s₀, wr_setV, wr_write]
  have hsp : s₁.sp = s.sp := by simp only [s₁, s₀, sp_setV, sp_write]
  have hmem : s₁.mem = s.mem := by simp only [s₁, s₀, mem_setV, mem_write]
  have hframe : Frame [spillRegion s] s.mem s₁.mem := by rw [hmem]; exact Frame.refl _ _
  have hregs : ∀ r, r ≠ .x3 → s₁.gpr r = s.gpr r := by
    intro r hr
    simp only [s₁, s₀, gpr_setV, gpr_write, hr, ite_false]
  have hstable : Stable s s₁ := ⟨hrd, hwr, hsp,
    fun q hq => hregs q (by revert hq; cases q <;> decide), hframe⟩
  apply WP.seq
  refine WP.of_runBlock ⟨s₁, ?_, ?_⟩
  · rw [runBlock_cons, imm, show exec (.movz .x .x3 (BitVec.ofNat 16 3) 0) s = some s₀ from rfl,
      runStep_some, runBlock_cons, show exec (.vop (.dup .d2 .v1 .x3)) s₀ = some s₁ from rfl,
      runStep_some, runBlock_nil]
  refine WP.loop (M := isa) (BodyInv keys base direction x s) ?_ 3 s₁
    ⟨by decide, by decide, ?_, ?_, hready.congr hbase (hregs .x0 (by decide)) hrd hwr hframe,
      hstable⟩
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
  · rw [passesOf, v_setV_self, VG.AArch64.vdword_ofVDwords_0]
    rfl
  · exact ⟨(hregs .x19 (by decide)).trans hword.left, (hregs .x20 (by decide)).trans hword.right⟩

end VG.Proof.TripleDes.AArch64
