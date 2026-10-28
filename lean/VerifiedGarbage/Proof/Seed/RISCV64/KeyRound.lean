module

import VerifiedGarbage.Proof.Seed.RISCV64.Round
public import VerifiedGarbage.Impl.Seed.RISCV64.ExpandKey
public import VerifiedGarbage.Proof.Seed.RISCV64.Lanes
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Seed.RISCV64.Steps

/-!
# A round of the key schedule on RISC-V

As on PPC64LE (`Proof/Seed/PPC64LE/KeyRound.lean`): `keyRound_ok`:
`keyRound j` writes round `j + 1`'s two inputs of `G`, from
`t5 = Key0 || Key1` and `t6 = Key2 || Key3`, to their lanes, and rotates one
of the two (two shifts and an `or`).
-/

@[expose] public section

namespace VG.Proof.Seed.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Impl.Seed.RISCV64
open VG.Impl.Aes.RISCV64 (sb shrI shlI)

/-- `t` is `s` with the register `d` set to `v`. -/
structure Upd (s t : State) (d : Reg) (v : BitVec 64) : Prop where
  gpr : ∀ x, t.gpr x = if x = d then v else s.gpr x
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem Upd.self {s t : State} {d : Reg} {v : BitVec 64} (h : Upd s t d v) : t.gpr d = v := by
  simp [h.gpr]

theorem Upd.other {s t : State} {d : Reg} {v : BitVec 64} (h : Upd s t d v) {x : Reg} (hx : x ≠ d) :
    t.gpr x = s.gpr x := by
  rw [h.gpr]; simp [hx]

theorem Upd.lane {s t : State} {d : Reg} {v : BitVec 64} (h : Upd s t d v) (hd : d ≠ sb) (k b : Nat) :
    lv t k b = lv s k b := by
  simp only [lv, laneA, h.mem, h.other (Ne.symm hd)]

theorem upd_write (s : State) (d : Reg) (v : BitVec 64) : Upd s (s.write d v) d v :=
  ⟨fun _ => gpr_write _ _ _ _, rfl, rfl, rfl, rfl⟩

theorem step_x (s : State) (i : Instr) (d : Reg) (v : BitVec 64) (h : exec i s = some (s.write d v)) :
    ∃ t, exec i s = some t ∧ Upd s t d v :=
  ⟨_, h, upd_write s d v⟩

theorem gSlot_mem (i : Nat) : gSlot i ∈ arrays := by
  unfold gSlot; split <;> decide

/-- `G`'s inputs have distinct lanes. -/
theorem gIn_apart : ∀ i < 32, ∀ i' < 32, i ≠ i' → gSlot i ≠ gSlot i' ∨ i % 16 ≠ i' % 16 := by decide

/-- The first input of `G` in round `j + 1`, from `Key0 || Key1` and `Key2 || Key3`. -/
def gIn0 (x y : BitVec 64) (c : BitVec 32) : BitVec 32 := (x >>> 32).setWidth 32 + (y >>> 32).setWidth 32 - c

/-- The second. -/
def gIn1 (x y : BitVec 64) (c : BitVec 32) : BitVec 32 := x.setWidth 32 - y.setWidth 32 + c

/-- A store of `t0`'s low half to a lane. -/
theorem step_store_lane {s : State} (h : Room s) {k b : Nat} (hk : k ∈ arrays) (hb : b < 16) :
    ∃ t, exec (stW k b .t0) s = some t ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.mem = s.mem.writeW (laneA s k b) ((s.gpr .t0).setWidth 32) :=
  ⟨_, exec_stW_lane h hk hb .t0, rfl, rfl, rfl, rfl, rfl⟩

theorem exec_shr (s : State) (d n : Reg) (k : Nat) (hk : k < 64) :
    exec (shrI d n k) s = some (s.write d (s.gpr n >>> k)) := by
  rw [shrI, exec_shift_d hk]

theorem exec_shl (s : State) (d n : Reg) (k : Nat) (hk : k < 64) :
    exec (shlI d n k) s = some (s.write d (s.gpr n <<< k)) := by
  rw [shlI, exec_shift_d hk]

/-- `li32`, run. -/
theorem li32_run (s : State) (d : Reg) (w : BitVec 32) :
    ∃ t, runBlock isa (Impl.Words.RISCV64.li32 d w) s = some t ∧ Upd s t d (sext32 w) := by
  obtain ⟨t, ht, e⟩ := run_of_wp (ByteLoad.li32_ok (s := s) (d := d) w)
  exact ⟨t, ht, e ▸ upd_write s d _⟩

/-- A rotation by two shifts and an `or`. -/
theorem rot_run (s : State) (x : Reg) (hx : x ≠ .t0) (r : Nat) (hr : 0 < r) (hr' : r < 64) :
    ∃ t, runBlock isa [shrI .t0 x r, shlI x x (64 - r), .logic .or x x .t0] s = some t ∧
      t.gpr x = (s.gpr x).rotateRight r ∧ (∀ y, y ≠ .t0 → y ≠ x → t.gpr y = s.gpr y) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  obtain ⟨s1, e1, u1⟩ := step_x s (shrI .t0 x r) .t0 (s.gpr x >>> r) (exec_shr _ _ _ _ hr')
  obtain ⟨s2, e2, u2⟩ := step_x s1 (shlI x x (64 - r)) x (s1.gpr x <<< (64 - r))
    (exec_shl _ _ _ _ (by omega))
  obtain ⟨s3, e3, u3⟩ := step_x s2 (.logic .or x x .t0) x (s2.gpr x ||| s2.gpr .t0) exec_logic
  refine ⟨s3, ?_, ?_, fun y a b => ?_, by rw [u3.mem, u2.mem, u1.mem], by rw [u3.rd, u2.rd, u1.rd],
    by rw [u3.wr, u2.wr, u1.wr], by rw [u3.sp, u2.sp, u1.sp]⟩
  · rw [runBlock_cons, e1, runStep_some, runBlock_cons, e2, runStep_some, runBlock_cons, e3,
      runStep_some, runBlock_nil]
  · rw [u3.self, u2.self, u2.other (Ne.symm hx), u1.self, u1.other hx, BitVec.or_comm,
      BitVec.rotateRight_def, Nat.mod_eq_of_lt hr']
  · rw [u3.other b, u2.other b, u1.other a]

theorem keyRound_ok {j : Nat} (hj : j < 16) {s : State} (h : Room s) :
    ∃ s', runBlock isa (keyRound j) s = some s' ∧
      lv s' (gSlot (2 * j)) (2 * j % 16) = gIn0 (s.gpr .t5) (s.gpr .t6) (kcs.getD j 0) ∧
      lv s' (gSlot (2 * j + 1)) ((2 * j + 1) % 16) = gIn1 (s.gpr .t5) (s.gpr .t6) (kcs.getD j 0) ∧
      (∀ k ∈ arrays, ∀ b < 16, (k ≠ gSlot (2 * j) ∨ b ≠ 2 * j % 16) →
        (k ≠ gSlot (2 * j + 1) ∨ b ≠ (2 * j + 1) % 16) → lv s' k b = lv s k b) ∧
      s'.gpr .t5 = (if j % 2 = 0 then (s.gpr .t5).rotateRight 8 else s.gpr .t5) ∧
      s'.gpr .t6 = (if j % 2 = 0 then s.gpr .t6 else (s.gpr .t6).rotateRight 56) ∧
      (∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → r ≠ .t5 → r ≠ .t6 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [arraysR s] s.mem s'.mem := by
  have hb0 : 2 * j % 16 < 16 := Nat.mod_lt _ (by decide)
  have hb1 : (2 * j + 1) % 16 < 16 := Nat.mod_lt _ (by decide)
  have hd : gSlot (2 * j + 1) ≠ gSlot (2 * j) ∨ (2 * j + 1) % 16 ≠ 2 * j % 16 :=
    gIn_apart _ (by omega) _ (by omega) (by omega)
  let c := kcs.getD j 0
  obtain ⟨s1, e1, u1⟩ := step_x s (shrI .t0 .t5 32) .t0 (s.gpr .t5 >>> 32) (exec_shr _ _ _ _ (by decide))
  obtain ⟨s2, e2, u2⟩ := step_x s1 (shrI .t1 .t6 32) .t1 (s1.gpr .t6 >>> 32) (exec_shr _ _ _ _ (by decide))
  obtain ⟨s3, e3, u3⟩ := step_x s2 (addW .t0 .t0 .t1) .t0 (s2.gpr .t0 + s2.gpr .t1) rfl
  obtain ⟨s4, e4, u4⟩ := li32_run s3 .t2 c
  obtain ⟨s6, e6, u6⟩ := step_x s4 (.sub .t0 .t0 .t2) .t0 (s4.gpr .t0 - s4.gpr .t2) rfl
  have g6 : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → s6.gpr r = s.gpr r := fun r a b c' => by
    rw [u6.other a, u4.other c', u3.other a, u2.other b, u1.other a]
  have room6 : Room s6 := room_congr h (g6 _ (by decide) (by decide) (by decide))
    (by rw [u6.wr, u4.wr, u3.wr, u2.wr, u1.wr])
  obtain ⟨s7, e7, g7, rd7, wr7, sp7, m7⟩ := step_store_lane room6 (gSlot_mem (2 * j)) hb0
  obtain ⟨s8, e8, u8⟩ := step_x s7 (.sub .t0 .t5 .t6) .t0 (s7.gpr .t5 - s7.gpr .t6) rfl
  obtain ⟨s9, e9, u9⟩ := step_x s8 (addW .t0 .t0 .t2) .t0 (s8.gpr .t0 + s8.gpr .t2) rfl
  have room9 : Room s9 := room_congr room6 (by rw [u9.other (by decide), u8.other (by decide), g7])
    (by rw [u9.wr, u8.wr, wr7])
  obtain ⟨s10, e10, g10, rd10, wr10, sp10, m10⟩ := step_store_lane room9 (gSlot_mem (2 * j + 1)) hb1
  have sb_6 : s6.gpr sb = s.gpr sb := g6 _ (by decide) (by decide) (by decide)
  have sb_9 : s9.gpr sb = s.gpr sb := by rw [u9.other (by decide), u8.other (by decide), g7, sb_6]
  have lA6 : ∀ k b, laneA s6 k b = laneA s k b := fun k b => by simp only [laneA, sb_6]
  have lA9 : ∀ k b, laneA s9 k b = laneA s k b := fun k b => by simp only [laneA, sb_9]
  -- the values
  have hc : (s4.gpr .t2).setWidth 32 = c := by rw [u4.self, lo32_sext]
  have v6 : (s6.gpr .t0).setWidth 32 = gIn0 (s.gpr .t5) (s.gpr .t6) c := by
    rw [u6.self, lo32_sub, hc, u4.other (by decide), u3.self, lo32_add,
      u2.other (by decide), u2.self, u1.self, u1.other (by decide)]
    rfl
  have v9 : (s9.gpr .t0).setWidth 32 = gIn1 (s.gpr .t5) (s.gpr .t6) c := by
    rw [u9.self, lo32_add, u8.self, lo32_sub, u8.other (show Reg.t2 ≠ .t0 by decide), g7,
      u6.other (show Reg.t2 ≠ .t0 by decide), hc, g6 .t5 (by decide) (by decide) (by decide),
      g6 .t6 (by decide) (by decide) (by decide)]
    rfl
  have mem9 : s9.mem = s7.mem := by rw [u9.mem, u8.mem]
  have mem6 : s6.mem = s.mem := by rw [u6.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have hrun : runBlock isa (([shrI .t0 .t5 32, shrI .t1 .t6 32, addW .t0 .t0 .t1] : List Instr) ++
      Impl.Words.RISCV64.li32 .t2 c ++
      ([.sub .t0 .t0 .t2, stW (gSlot (2 * j)) (2 * j % 16) .t0, .sub .t0 .t5 .t6, addW .t0 .t0 .t2,
        stW (gSlot (2 * j + 1)) ((2 * j + 1) % 16) .t0] : List Instr)) s = some s10 := by
    refine runBlock_trans (runBlock_trans ?_ e4) ?_
    · rw [runBlock_cons, e1, runStep_some, runBlock_cons, e2, runStep_some, runBlock_cons, e3, runStep_some,
        runBlock_nil]
    · rw [runBlock_cons, e6, runStep_some, runBlock_cons, e7, runStep_some, runBlock_cons, e8, runStep_some,
        runBlock_cons, e9, runStep_some, runBlock_cons, e10, runStep_some, runBlock_nil]
  -- the lanes after both stores
  have lv10 : ∀ k ∈ arrays, ∀ b < 16, lv s10 k b =
      ((s.mem.writeW (laneA s (gSlot (2 * j)) (2 * j % 16)) (gIn0 (s.gpr .t5) (s.gpr .t6) c)).writeW
        (laneA s (gSlot (2 * j + 1)) ((2 * j + 1) % 16)) (gIn1 (s.gpr .t5) (s.gpr .t6) c)).readW
        (laneA s k b) 32 := by
    intro k _ b _
    simp only [lv, laneA, g10, u9.other (show sb ≠ .t0 by decide), u8.other (show sb ≠ .t0 by decide),
      g7]
    rw [m10, mem9, m7, lA9, lA6, v6, v9, mem6]
    simp only [laneA, sb_6]
  have lane0 : lv s10 (gSlot (2 * j)) (2 * j % 16) = gIn0 (s.gpr .t5) (s.gpr .t6) c := by
    rw [lv10 _ (gSlot_mem _) _ hb0, readW_writeW_lane (gSlot_mem _) hb0 (gSlot_mem _) hb1
      (by rcases hd with h | h; exact Or.inl (Ne.symm h); exact Or.inr (Ne.symm h)), Mem.readW_writeW_self32]
  have lane1 : lv s10 (gSlot (2 * j + 1)) ((2 * j + 1) % 16) = gIn1 (s.gpr .t5) (s.gpr .t6) c := by
    rw [lv10 _ (gSlot_mem _) _ hb1, Mem.readW_writeW_self32]
  have lanes : ∀ k ∈ arrays, ∀ b < 16, (k ≠ gSlot (2 * j) ∨ b ≠ 2 * j % 16) →
      (k ≠ gSlot (2 * j + 1) ∨ b ≠ (2 * j + 1) % 16) → lv s10 k b = lv s k b := by
    intro k hk b hb h0 h1
    rw [lv10 k hk b hb, readW_writeW_lane hk hb (gSlot_mem _) hb1 h1,
      readW_writeW_lane hk hb (gSlot_mem _) hb0 h0]
    rfl
  have frame : Frame [arraysR s] s.mem s10.mem := by
    rw [m10, mem9, m7, lA9, lA6, mem6]
    exact ((Frame.refl _ _).writeW List.mem_cons_self _ (lane_inArrays (gSlot_mem _) hb0 s)).writeW
      List.mem_cons_self _ (lane_inArrays (gSlot_mem _) hb1 s)
  have G10 : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → s10.gpr r = s.gpr r := by
    intro r ha hb hc'
    rw [g10, u9.other ha, u8.other ha, g7, g6 r ha hb hc']
  have rd10' : s10.rd = s.rd := by rw [rd10, u9.rd, u8.rd, rd7, u6.rd, u4.rd, u3.rd, u2.rd, u1.rd]
  have wr10' : s10.wr = s.wr := by rw [wr10, u9.wr, u8.wr, wr7, u6.wr, u4.wr, u3.wr, u2.wr, u1.wr]
  have sp10' : s10.sp = s.sp := by rw [sp10, u9.sp, u8.sp, sp7, u6.sp, u4.sp, u3.sp, u2.sp, u1.sp]
  have sb10 : s10.gpr sb = s.gpr sb := G10 _ (by decide) (by decide) (by decide)
  have lvR : ∀ {t : State}, t.gpr sb = s10.gpr sb → t.mem = s10.mem → ∀ k b, lv t k b = lv s10 k b :=
    fun ht hm k b => by simp only [lv, laneA, ht, hm]
  -- the rotation
  by_cases hj2 : j % 2 = 0
  · obtain ⟨s11, e11, r11, o11, m11, rd11, wr11, sp11⟩ := rot_run s10 .t5 (by decide) 8 (by decide) (by decide)
    have sb11 : s11.gpr sb = s10.gpr sb := o11 _ (by decide) (by decide)
    refine ⟨s11, ?_, by rw [lvR sb11 m11]; exact lane0, by rw [lvR sb11 m11]; exact lane1,
      fun k hk b hb h0 h1 => by rw [lvR sb11 m11, lanes k hk b hb h0 h1], ?_, ?_,
      fun r ha hb hc' h3 _ => by rw [o11 r ha h3, G10 r ha hb hc'], by rw [rd11, rd10'], by rw [wr11, wr10'],
      by rw [sp11, sp10'], by rw [m11]; exact frame⟩
    · have : keyRound j = ([shrI .t0 .t5 32, shrI .t1 .t6 32, addW .t0 .t0 .t1] : List Instr) ++
          Impl.Words.RISCV64.li32 .t2 c ++
          ([.sub .t0 .t0 .t2, stW (gSlot (2 * j)) (2 * j % 16) .t0, .sub .t0 .t5 .t6, addW .t0 .t0 .t2,
            stW (gSlot (2 * j + 1)) ((2 * j + 1) % 16) .t0] : List Instr) ++
          [shrI .t0 .t5 8, shlI .t5 .t5 56, .logic .or .t5 .t5 .t0] := by
        simp only [keyRound, hj2, ite_true, keyA, keyB, c]; rfl
      rw [this]
      exact runBlock_trans hrun e11
    · rw [r11, G10 _ (by decide) (by decide) (by decide), ite_eq_left_iff.mpr (fun h => absurd hj2 h)]
    · rw [o11 _ (by decide) (by decide), G10 _ (by decide) (by decide) (by decide),
        ite_eq_left_iff.mpr (fun h => absurd hj2 h)]
  · obtain ⟨s11, e11, r11, o11, m11, rd11, wr11, sp11⟩ := rot_run s10 .t6 (by decide) 56 (by decide) (by decide)
    have sb11 : s11.gpr sb = s10.gpr sb := o11 _ (by decide) (by decide)
    refine ⟨s11, ?_, by rw [lvR sb11 m11]; exact lane0, by rw [lvR sb11 m11]; exact lane1,
      fun k hk b hb h0 h1 => by rw [lvR sb11 m11, lanes k hk b hb h0 h1], ?_, ?_,
      fun r ha hb hc' _ h4 => by rw [o11 r ha h4, G10 r ha hb hc'], by rw [rd11, rd10'], by rw [wr11, wr10'],
      by rw [sp11, sp10'], by rw [m11]; exact frame⟩
    · have : keyRound j = ([shrI .t0 .t5 32, shrI .t1 .t6 32, addW .t0 .t0 .t1] : List Instr) ++
          Impl.Words.RISCV64.li32 .t2 c ++
          ([.sub .t0 .t0 .t2, stW (gSlot (2 * j)) (2 * j % 16) .t0, .sub .t0 .t5 .t6, addW .t0 .t0 .t2,
            stW (gSlot (2 * j + 1)) ((2 * j + 1) % 16) .t0] : List Instr) ++
          [shrI .t0 .t6 56, shlI .t6 .t6 8, .logic .or .t6 .t6 .t0] := by
        simp only [keyRound, hj2, ite_false, keyA, keyB, c]; rfl
      rw [this]
      exact runBlock_trans hrun e11
    · rw [o11 _ (by decide) (by decide), G10 _ (by decide) (by decide) (by decide),
        ite_eq_right_iff.mpr (fun h => absurd h hj2)]
    · rw [r11, G10 _ (by decide) (by decide) (by decide), ite_eq_right_iff.mpr (fun h => absurd h hj2)]

end VG.Proof.Seed.RISCV64
