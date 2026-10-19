module

public import VerifiedGarbage.Proof.Seed.AArch64.KeyStore
public import VerifiedGarbage.Proof.Seed.AArch64.KeyRounds
import VerifiedGarbage.Proof.Seed.AArch64.Batch
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# The key schedule's computation on AArch64

`keyBody_ok`: from `x3 = Key0 || Key1` and `x4 = Key2 || Key3`, the rounds,
the two `g16`s and the copies write `G` of the 32 inputs (`gInput`) to the
schedule.
-/

@[expose] public section

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.AArch64.RegUpd VG.Impl.Seed.AArch64 VG.Proof.Seed
open VG.Proof.Aes.AArch64 (layerWrites)

/-- The rounds and the count of halves, between loading the key and the loop. -/
def keyPre : List Instr := (List.range 16).flatMap keyRound ++ [.movz .x .x3 2 0]

theorem gSlot_lo {i : Nat} (hi : i < 16) : gSlot i = tSlot 0 := by simp [gSlot, hi]
theorem gSlot_hi {w : Nat} (hw : w < 16) : gSlot (16 + w) = uSlot := by
  simp [gSlot, show ¬ 16 + w < 16 by omega]

theorem schedR_sep {s : State} {k : Nat} (hk : k + 64 ≤ 128)
    (h : (⟨s.gpr .x1, 128⟩ : Region).Disjoint (scratchR s)) : (outR s (k / 4)).Disjoint (scratchR s) := by
  refine h.sub_left ?_
  exact Offset.sub_base _ (by omega)

theorem lane_sub_work {s : State} {k b : Nat} (hk : k ∈ arrays) (hb : b < 16) :
    Region.Sub ⟨laneA s k b, 4⟩ (workR s) := by
  have := arrays_bound k hk
  exact Offset.sub_base _ (by omega)

/-- A lane after a frame over regions apart from the scratch buffer. -/
theorem lv_frame {s s' : State} {R : Region} (hx5 : s'.gpr .x5 = s.gpr .x5) (hf : Frame [R] s.mem s'.mem)
    (hd : R.Disjoint (scratchR s)) {k b : Nat} (hk : k ∈ arrays) (hb : b < 16) : lv s' k b = lv s k b := by
  simp only [lv, laneA, hx5]
  refine hf.readW (r := ⟨s.gpr .x5 + BitVec.ofNat 64 (8 * k + 4 * b), 4⟩) (Region.contains_self _ _) ?_
    (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact (hd.sub_right (lane_in hk hb s |> fun _ => by
    have := arrays_bound k hk
    exact Offset.sub_base _ (by unfold scratchSlots; omega))).symm

theorem keyPre_ok (key : Spec.Seed.Block) {s : State} (h : Room s)
    (h3 : s.gpr .x3 = kx (keyWords key 0)) (h4 : s.gpr .x4 = ky (keyWords key 0)) :
    ∃ s', runBlock isa keyPre s = some s' ∧ Room s' ∧
      (∀ w < 16, lv s' (tSlot 0) w = gInput key w) ∧ (∀ w < 16, lv s' uSlot w = gInput key (16 + w)) ∧
      s'.gpr .x3 = BitVec.ofNat 64 2 ∧ (∀ r ∈ [Reg.x5, .x1], s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [arraysR s] s.mem s'.mem := by
  obtain ⟨s1, e1, inv⟩ := keyRounds_ok key h h3 h4 16 (Nat.le_refl _)
  let s2 := s1.write .x .x3 (BitVec.ofNat 64 2)
  have e2 : runBlock isa [.movz .x .x3 2 0] s1 = some s2 := by
    rw [runBlock_cons, show exec (.movz .x .x3 2 0) s1 = some s2 by simp [exec, s2]; rfl, runStep_some, runBlock_nil]
  have g2 : ∀ r, r ≠ .x3 → s2.gpr r = s1.gpr r := fun r hr => gpr_write_of_ne _ _ _ hr
  have x5_1 : s1.gpr .x5 = s.gpr .x5 := inv.regs _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have x5_2 : s2.gpr .x5 = s.gpr .x5 := (g2 _ (by decide)).trans x5_1
  have lv2 : ∀ k b, lv s2 k b = lv s1 k b := fun k b => by
    simp only [lv, laneA, g2 _ (show Reg.x5 ≠ .x3 by decide)]; rfl
  refine ⟨s2, runBlock_trans e1 e2, room_congr h x5_2 inv.wr, fun w hw => ?_, fun w hw => ?_,
    by simp [s2, gpr_write], fun r hr => ?_, inv.rd, inv.wr, inv.frame⟩
  · rw [lv2, ← inv.lanes w (by omega), gSlot_lo hw, Nat.mod_eq_of_lt hw]
  · rw [lv2, ← inv.lanes (16 + w) (by omega), gSlot_hi hw, show (16 + w) % 16 = w by omega]
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl <;>
      rw [g2 _ (by decide), inv.regs _ (by decide) (by decide) (by decide) (by decide) (by decide)]

/-- `add x1, x1, 64; sub x3, x3, 1`. -/
theorem halfTail_ok (t : State) :
    ∃ t', runBlock isa [.addImm .x .x1 .x1 64, .subImm .x .x3 .x3 1] t = some t' ∧
      t'.gpr .x1 = t.gpr .x1 + BitVec.ofNat 64 64 ∧ t'.gpr .x3 = t.gpr .x3 - BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .x1 → r ≠ .x3 → t'.gpr r = t.gpr r) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine ⟨_, by
    rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons, exec_subImm_x (by decide),
      runStep_some, runBlock_nil], ?_⟩
  refine ⟨by simp [gpr_write, State.read], by simp [gpr_write, State.read], fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  simp [gpr_write, h1, h2]

/-- After `c` of the two halves: `x1` at the schedule's word `16 c`, `x3` the
halves left, `G`'s words holding the next sixteen inputs, the schedule's
words before `16 c` done. -/
structure HalfInv (key : Spec.Seed.Block) (s : State) (S : Addr) (c : Nat) (t : State) : Prop where
  room : Room t
  x5 : t.gpr .x5 = s.gpr .x5
  x1 : t.gpr .x1 = S + BitVec.ofNat 64 (64 * c)
  x3 : t.gpr .x3 = BitVec.ofNat 64 (2 - c)
  cur : ∀ w < 16, lv t (tSlot 0) w = gInput key (16 * c + w)
  next : c = 0 → ∀ w < 16, lv t uSlot w = gInput key (16 + w)
  done : ∀ i < 16 * c, t.mem.readW (S + BitVec.ofNat 64 (4 * i)) 32 = Spec.Seed.g (gInput key i)
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [workR s, ⟨S, 128⟩] s.mem t.mem

theorem keyHalves_wp (key : Spec.Seed.Block) {s : State} {S : Addr} (hin : (⟨S, 128⟩ : Region) ∈ s.wr)
    (hsep : (⟨S, 128⟩ : Region).Disjoint (scratchR s)) (h0 : HalfInv key s S 0 s) {Q : State → Prop}
    (hQ : ∀ t, (∀ i < 32, t.mem.readW (S + BitVec.ofNat 64 (4 * i)) 32 = Spec.Seed.g (gInput key i)) →
      t.gpr .x5 = s.gpr .x5 → t.rd = s.rd → t.wr = s.wr → Frame [workR s, ⟨S, 128⟩] s.mem t.mem → Q t) :
    WP isa (.loop keyHalf (.nonzero .x .x3)) s Q := by
  refine WP.loop (M := isa) (fun n t => ∃ c, c < 2 ∧ n = 2 - c ∧ HalfInv key s S c t) (fun n t ht => ?_) 2 s
    ⟨0, by decide, rfl, h0⟩
  obtain ⟨c, hc, rfl, hi⟩ := ht
  have scrS : ∀ t : State, t.gpr .x5 = s.gpr .x5 → scratchR t = scratchR s := fun t h => by simp only [scratchR, h]
  have workS : ∀ t : State, t.gpr .x5 = s.gpr .x5 → workR t = workR s := fun t h => by simp only [workR, h]
  have schedWork : (⟨S, 128⟩ : Region).Disjoint (workR s) :=
    hsep.sub_right (Region.sub_prefix (by unfold scratchSlots; omega))
  -- `G` of the sixteen
  obtain ⟨t2, e2, g2, keep2, room2, rd2, wr2, -, regs2, f2⟩ := g16_lanes hi.room
  have x5_2 : t2.gpr .x5 = s.gpr .x5 := (regs2 _ (by decide)).trans hi.x5
  have x1_2 : t2.gpr .x1 = S + BitVec.ofNat 64 (64 * c) := (regs2 _ (by decide)).trans hi.x1
  have out2 : (outR t2 0).Disjoint (scratchR t2) := by
    rw [scrS t2 x5_2]; simp only [outR, x1_2, Nat.mul_zero]; rw [BitVec.add_zero]
    exact hsep.sub_left (Offset.sub_base _ (by omega))
  -- the copy
  obtain ⟨t3, e3, v3, g3, rd3, wr3, f3⟩ := keyStore_ok 0 (by decide) room2
    (fun w hw => by
      rw [x1_2, wr2, hi.wr, Offset.add_add]
      exact ⟨_, hin, Offset.contains_base _ (by omega) (by omega)⟩) out2 16 (Nat.le_refl _)
  obtain ⟨t4, e4, x1_4', x3_4', g4, m4, rd4, wr4⟩ := halfTail_ok t3
  have x5_4 : t4.gpr .x5 = s.gpr .x5 := by rw [g4 _ (by decide) (by decide), g3 _ (by decide), x5_2]
  have x3_4 : t4.gpr .x3 = BitVec.ofNat 64 (2 - (c + 1)) := by
    rw [x3_4', g3 _ (by decide), regs2 _ (by decide), hi.x3, Offset.ofNat_sub_ofNat (by omega)]
    congr 1
  have x1_4 : t4.gpr .x1 = S + BitVec.ofNat 64 (64 * (c + 1)) := by
    rw [x1_4', g3 _ (by decide), x1_2, Offset.add_add, show 64 * c + 64 = 64 * (c + 1) by omega]
  have ev4 : isa.eval (.nonzero .x .x3) t4 = some (decide (c = 0)) := by
    show some (t4.read .x .x3 != 0) = _
    rw [show t4.read .x .x3 = t4.gpr .x3 by simp [State.read], x3_4]
    congr 1
    have : 2 - (c + 1) < 2 ^ 64 := by omega
    rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl <;> decide
  -- the schedule's words so far
  have lvS : ∀ (t t' : State) (rs : List Region), Frame rs t.mem t'.mem →
      ∀ i, (∀ r ∈ rs, (⟨S + BitVec.ofNat 64 (4 * i), 4⟩ : Region).Disjoint r) →
      t'.mem.readW (S + BitVec.ofNat 64 (4 * i)) 32 = t.mem.readW (S + BitVec.ofNat 64 (4 * i)) 32 :=
    fun t t' rs hf i hd => hf.readW (Region.contains_self _ _) hd (by decide)
  have done4 : ∀ i < 16 * (c + 1), t4.mem.readW (S + BitVec.ofNat 64 (4 * i)) 32 = Spec.Seed.g (gInput key i) := by
    intro i hi'
    rw [m4]
    by_cases hlo : i < 16 * c
    · rw [lvS t2 t3 _ f3 i (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; simp only [outR, x1_2, Nat.mul_zero]
          rw [BitVec.add_zero]
          exact Offset.disjoint _ (Or.inl (by omega)) (by omega) (by omega)),
        lvS t t2 _ f2 i (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [workS t hi.x5]
          exact schedWork.sub_left (Offset.sub_base _ (by omega))), hi.done i hlo]
    · obtain ⟨w, rfl⟩ : ∃ w, i = 16 * c + w := ⟨i - 16 * c, by omega⟩
      have := v3 w (by omega)
      rw [x1_2, Offset.add_add, show 64 * c + 4 * (0 + w) = 4 * (16 * c + w) by omega] at this
      rw [this, g2 w (by omega), hi.cur w (by omega)]
  have frame4 : Frame [workR s, ⟨S, 128⟩] s.mem t4.mem := by
    rw [m4]
    refine (hi.frame.trans (f2.sub ?_)).trans (f3.sub ?_)
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact ⟨workR s, List.mem_cons_self, by rw [workS t hi.x5]; exact fun _ h => h⟩
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
      simp only [outR, x1_2, Nat.mul_zero]; rw [BitVec.add_zero]
      exact Offset.sub_base _ (by omega)
  have room4 : Room t4 := room_congr hi.room (x5_4.trans hi.x5.symm) (by rw [wr4, wr3, wr2, hi.wr])
  refine WP.seq (WP.of_runBlock ⟨t4, runBlock_trans (runBlock_trans e2 e3) e4, ?_⟩)
  refine WP.ite (decide (c = 0)) ev4 (fun hb => ?_) (fun hb => ?_)
  · -- the second sixteen inputs
    have hc0 : c = 0 := by simpa using hb
    subst hc0
    obtain ⟨t5, e5, room5, v5, f5, rd5, wr5, g5⟩ := keyMove_ok room4
    refine WP.of_runBlock ⟨t5, e5, .inr ⟨?_, 1, by omega, 1, by omega, rfl, ?_⟩⟩
    · show some (t5.read .x .x3 != 0) = some true
      rw [show t5.read .x .x3 = t5.gpr .x3 by simp [State.read], g5 _ (by decide) (by decide), x3_4]
      decide
    have x5_5 : t5.gpr .x5 = s.gpr .x5 := (g5 _ (by decide) (by decide)).trans x5_4
    have workF : Frame [workR s] t4.mem t5.mem := by
      refine f5.sub fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨workR s, List.mem_cons_self, by rw [← workS t4 x5_4]; exact arraysR_sub_work t4⟩
    refine ⟨room5, x5_5, by rw [g5 _ (by decide) (by decide), x1_4], by rw [g5 _ (by decide) (by decide), x3_4],
      fun w hw => ?_, fun h => absurd h (by decide), fun i hi' => ?_, by rw [rd5, rd4, rd3, rd2, hi.rd],
      by rw [wr5, wr4, wr3, wr2, hi.wr],
      frame4.trans (workF.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩)⟩
    · rw [v5 _ (by decide) w hw, show newVal spMove (tSlot 0) (fun k' => lv t4 k' w) = lv t4 uSlot w from rfl,
        show lv t4 uSlot w = lv t3 uSlot w by
          simp only [lv, laneA, m4, g4 _ (show Reg.x5 ≠ .x1 by decide) (show Reg.x5 ≠ .x3 by decide)],
        lv_frame (g3 _ (by decide)) f3 out2 (by decide) hw, keep2 uSlot (by decide) (by decide) w hw,
        hi.next rfl w hw]
    · rw [lvS t4 t5 _ workF i (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact schedWork.sub_left (Offset.sub_base _ (by omega)))]
      exact done4 i hi'
  · -- the end
    have hc1 : c = 1 := by simp at hb; omega
    subst hc1
    refine WP.block_nil (.inl ⟨?_, hQ t4 done4 x5_4 (by rw [rd4, rd3, rd2, hi.rd])
      (by rw [wr4, wr3, wr2, hi.wr]) frame4⟩)
    show some (t4.read .x .x3 != 0) = some false
    rw [show t4.read .x .x3 = t4.gpr .x3 by simp [State.read], x3_4]
    decide

end VG.Proof.Seed.AArch64
