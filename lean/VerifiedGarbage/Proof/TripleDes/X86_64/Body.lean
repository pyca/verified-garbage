module

public import VerifiedGarbage.Proof.TripleDes.X86_64.Ready
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.TripleDes.X86_64.RoundLit

@[expose] public section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64
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

theorem passesInit_ok (s : State) (hwrite : InRegions s.wr (passesAddr s) 8) :
    ∃ s', runBlock isa [imm .rax 3, .store (memOp .rdx 456) .rax] s = some s' ∧
      s'.mem = s.mem.writeW (passesAddr s) (BitVec.ofNat 64 3) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) := by
  unfold passesAddr at hwrite
  have hoff : BitVec.ofInt 64 (Int.ofNat 456) = BitVec.ofNat 64 456 := rfl
  refine ⟨_, by
    simp only [imm, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.ea,
      memOp, hoff, State.store64, gpr_setReg, mem_setReg, wr_setReg, reduceCtorEq,
      ite_false, ite_true, hwrite, Option.map_some]
    rfl, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · intro r hr
    simp only [gpr_setReg, hr, ite_false]

/-- The loop's invariant, with `m` passes left. -/
structure BodyInv (keys : Nat → DesSchedule) (base : Addr) (direction : Direction)
    (x : BitVec 64) (origin : State) (m : Nat) (s : State) : Prop where
  pos : 1 ≤ m
  le : m ≤ 3
  passes : s.mem.readW (passesAddr s) 64 = BitVec.ofNat 64 m
  word : WordState (passesDone keys direction x (3 - m)) s
  ready : Ready keys base s
  stable : Stable origin s

theorem blockBody_ok (keys : Nat → DesSchedule) (base : Addr) (s : State) (x : BitVec 64)
    (direction : Direction) (hready : Ready keys base s) (hword : WordState x s) :
    WP isa (blockBody direction) s
      (fun t => WordState (blockCore keys direction x) t ∧ Ready keys base t ∧ Stable s t) := by
  obtain ⟨s₁, run₁, mem₁, rd₁, wr₁, regs₁⟩ := passesInit_ok s hready.passesWrite
  have hbase : s₁.gpr .rdx = s.gpr .rdx := regs₁ .rdx (by decide)
  have hframe : Frame [workRegion s] s.mem s₁.mem := by
    rw [mem₁]
    exact (countWrite_frame _ _ _).sub (by
      intro q hq
      obtain rfl := List.mem_singleton.mp hq
      exact ⟨_, List.mem_singleton_self _, passes_sub_work s⟩)
  have hstable : Stable s s₁ := ⟨rd₁, wr₁, fun q hq => regs₁ q (by revert hq; cases q <;> decide),
    hframe⟩
  apply WP.seq
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  refine WP.loop (M := isa) (BodyInv keys base direction x s) ?_ 3 s₁
    ⟨by decide, by decide, ?_, ?_, hready.congr hbase rd₁ wr₁ hframe, hstable⟩
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
  · rw [show passesAddr s₁ = passesAddr s from congrArg (· + BitVec.ofNat 64 456) hbase, mem₁]
    exact Mem.readW_writeW_self64 _ _ _
  · exact ⟨(regs₁ .r12 (by decide)).trans hword.left, (regs₁ .r13 (by decide)).trans hword.right⟩

end VG.Proof.TripleDes.X86_64
