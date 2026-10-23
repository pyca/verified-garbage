module

import VerifiedGarbage.Proof.Seed.PPC64LE.Round
public import VerifiedGarbage.Impl.Seed.PPC64LE.ExpandKey
public import VerifiedGarbage.Proof.Seed.PPC64LE.Lanes
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# A round of the key schedule on PPC64LE

`keyRound_ok`: `keyRound j` writes round `j + 1`'s two inputs of `G`, from
`r6 = Key0 || Key1` and `r7 = Key2 || Key3`, to their lanes, and rotates
one of the two.
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.PPC64LE.RegUpd VG.Impl.Seed.PPC64LE VG.Impl.Aes.PPC64LE

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

theorem Upd.lane {s t : State} {d : Reg} {v : BitVec 64} (h : Upd s t d v) (hd : d ≠ .r8) (k b : Nat) :
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

/-- A store of `r9`'s low half to a lane. -/
theorem step_store_lane {s : State} (h : Room s) {k b : Nat} (hk : k ∈ arrays) (hb : b < 16) :
    ∃ t, exec (stW k b .r9) s = some t ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.mem = s.mem.writeW (laneA s k b) ((s.gpr .r9).setWidth 32) :=
  ⟨_, exec_stW_lane h hk hb .r9, rfl, rfl, rfl, rfl, rfl⟩

theorem keyRound_ok {j : Nat} (hj : j < 16) {s : State} (h : Room s) :
    ∃ s', runBlock isa (keyRound j) s = some s' ∧
      lv s' (gSlot (2 * j)) (2 * j % 16) = gIn0 (s.gpr .r6) (s.gpr .r7) (kcs.getD j 0) ∧
      lv s' (gSlot (2 * j + 1)) ((2 * j + 1) % 16) = gIn1 (s.gpr .r6) (s.gpr .r7) (kcs.getD j 0) ∧
      (∀ k ∈ arrays, ∀ b < 16, (k ≠ gSlot (2 * j) ∨ b ≠ 2 * j % 16) →
        (k ≠ gSlot (2 * j + 1) ∨ b ≠ (2 * j + 1) % 16) → lv s' k b = lv s k b) ∧
      s'.gpr .r6 = (if j % 2 = 0 then (s.gpr .r6).rotateRight 8 else s.gpr .r6) ∧
      s'.gpr .r7 = (if j % 2 = 0 then s.gpr .r7 else (s.gpr .r7).rotateRight 56) ∧
      (∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r6 → r ≠ .r7 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [arraysR s] s.mem s'.mem := by
  have hb0 : 2 * j % 16 < 16 := Nat.mod_lt _ (by decide)
  have hb1 : (2 * j + 1) % 16 < 16 := Nat.mod_lt _ (by decide)
  have hd : gSlot (2 * j + 1) ≠ gSlot (2 * j) ∨ (2 * j + 1) % 16 ≠ 2 * j % 16 :=
    gIn_apart _ (by omega) _ (by omega) (by omega)
  let c := kcs.getD j 0
  obtain ⟨s1, e1, u1⟩ := step_x s (shrI .r9 .r6 32) .r9 (s.gpr .r6 >>> 32)
    (by rw [shrI, exec_lsr_d (by decide)])
  obtain ⟨s2, e2, u2⟩ := step_x s1 (shrI .r10 .r7 32) .r10 (s1.gpr .r7 >>> 32)
    (by rw [shrI, exec_lsr_d (by decide)])
  obtain ⟨s3, e3, u3⟩ := step_x s2 (addW .r9 .r9 .r10) .r9 (s2.gpr .r9 + s2.gpr .r10) rfl
  obtain ⟨s4, e4, u4⟩ := step_x s3 (.lis .r11 (c.extractLsb' 16 16)) .r11
    ((c.extractLsb' 16 16 ++ (0 : BitVec 16)).signExtend 64) exec_lis
  obtain ⟨s5, e5, u5⟩ := step_x s4 (.ori .r11 .r11 (c.extractLsb' 0 16)) .r11
    (s4.gpr .r11 ||| (c.extractLsb' 0 16).setWidth 64) exec_ori
  obtain ⟨s6, e6, u6⟩ := step_x s5 (subW .r9 .r9 .r11) .r9 (s5.gpr .r9 - s5.gpr .r11) rfl
  have g6 : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → s6.gpr r = s.gpr r := fun r a b c' => by
    rw [u6.other a, u5.other c', u4.other c', u3.other a, u2.other b, u1.other a]
  have room6 : Room s6 := room_congr h (g6 _ (by decide) (by decide) (by decide))
    (by rw [u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr])
  obtain ⟨s7, e7, g7, rd7, wr7, sp7, m7⟩ := step_store_lane room6 (gSlot_mem (2 * j)) hb0
  obtain ⟨s8, e8, u8⟩ := step_x s7 (subW .r9 .r6 .r7) .r9 (s7.gpr .r6 - s7.gpr .r7) rfl
  obtain ⟨s9, e9, u9⟩ := step_x s8 (addW .r9 .r9 .r11) .r9 (s8.gpr .r9 + s8.gpr .r11) rfl
  have room9 : Room s9 := room_congr room6 (by rw [u9.other (by decide), u8.other (by decide), g7])
    (by rw [u9.wr, u8.wr, wr7])
  obtain ⟨s10, e10, g10, rd10, wr10, sp10, m10⟩ := step_store_lane room9 (gSlot_mem (2 * j + 1)) hb1
  have r9_6 : s6.gpr .r8 = s.gpr .r8 := g6 _ (by decide) (by decide) (by decide)
  have r9_9 : s9.gpr .r8 = s.gpr .r8 := by rw [u9.other (by decide), u8.other (by decide), g7, r9_6]
  have lA6 : ∀ k b, laneA s6 k b = laneA s k b := fun k b => by simp only [laneA, r9_6]
  have lA9 : ∀ k b, laneA s9 k b = laneA s k b := fun k b => by simp only [laneA, r9_9]
  -- the values
  have hc : (s5.gpr .r11).setWidth 32 = c := by
    rw [u5.self, u4.self]; exact lis_ori c
  have v6 : (s6.gpr .r9).setWidth 32 = gIn0 (s.gpr .r6) (s.gpr .r7) c := by
    rw [u6.self, lo32_sub, hc, u5.other (by decide), u4.other (by decide), u3.self, lo32_add,
      u2.other (by decide), u2.self, u1.self, u1.other (by decide)]
    rfl
  have v9 : (s9.gpr .r9).setWidth 32 = gIn1 (s.gpr .r6) (s.gpr .r7) c := by
    rw [u9.self, lo32_add, u8.self, lo32_sub, u8.other (show Reg.r11 ≠ .r9 by decide), g7,
      u6.other (show Reg.r11 ≠ .r9 by decide), hc, g6 .r6 (by decide) (by decide) (by decide),
      g6 .r7 (by decide) (by decide) (by decide)]
    rfl
  have mem9 : s9.mem = s7.mem := by rw [u9.mem, u8.mem]
  have mem6 : s6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have hrun : runBlock isa ([shrI .r9 .r6 32, shrI .r10 .r7 32, addW .r9 .r9 .r10,
      .lis .r11 (c.extractLsb' 16 16), .ori .r11 .r11 (c.extractLsb' 0 16),
      subW .r9 .r9 .r11, stW (gSlot (2 * j)) (2 * j % 16) .r9,
      subW .r9 .r6 .r7, addW .r9 .r9 .r11, stW (gSlot (2 * j + 1)) ((2 * j + 1) % 16) .r9] :
      List Instr) s = some s10 := by
    rw [runBlock_cons, e1, runStep_some, runBlock_cons, e2, runStep_some, runBlock_cons, e3, runStep_some,
      runBlock_cons, e4, runStep_some, runBlock_cons, e5, runStep_some, runBlock_cons, e6, runStep_some,
      runBlock_cons, e7, runStep_some, runBlock_cons, e8, runStep_some, runBlock_cons, e9, runStep_some,
      runBlock_cons, e10, runStep_some, runBlock_nil]
  -- the lanes after both stores
  have lv10 : ∀ k ∈ arrays, ∀ b < 16, lv s10 k b =
      ((s.mem.writeW (laneA s (gSlot (2 * j)) (2 * j % 16)) (gIn0 (s.gpr .r6) (s.gpr .r7) c)).writeW
        (laneA s (gSlot (2 * j + 1)) ((2 * j + 1) % 16)) (gIn1 (s.gpr .r6) (s.gpr .r7) c)).readW
        (laneA s k b) 32 := by
    intro k _ b _
    simp only [lv, laneA, g10, u9.other (show Reg.r8 ≠ .r9 by decide), u8.other (show Reg.r8 ≠ .r9 by decide),
      g7]
    rw [m10, mem9, m7, lA9, lA6, v6, v9, mem6]
    simp only [laneA, r9_6]
  have lane0 : lv s10 (gSlot (2 * j)) (2 * j % 16) = gIn0 (s.gpr .r6) (s.gpr .r7) c := by
    rw [lv10 _ (gSlot_mem _) _ hb0, readW_writeW_lane (gSlot_mem _) hb0 (gSlot_mem _) hb1
      (by rcases hd with h | h; exact Or.inl (Ne.symm h); exact Or.inr (Ne.symm h)), Mem.readW_writeW_self32]
  have lane1 : lv s10 (gSlot (2 * j + 1)) ((2 * j + 1) % 16) = gIn1 (s.gpr .r6) (s.gpr .r7) c := by
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
  have G10 : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → s10.gpr r = s.gpr r := by
    intro r ha hb hc'
    rw [g10, u9.other ha, u8.other ha, g7, g6 r ha hb hc']
  have rd10' : s10.rd = s.rd := by rw [rd10, u9.rd, u8.rd, rd7, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]
  have wr10' : s10.wr = s.wr := by rw [wr10, u9.wr, u8.wr, wr7, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]
  have sp10' : s10.sp = s.sp := by rw [sp10, u9.sp, u8.sp, sp7, u6.sp, u5.sp, u4.sp, u3.sp, u2.sp, u1.sp]
  -- the rotation
  by_cases hj2 : j % 2 = 0
  · obtain ⟨s11, e11, u11⟩ := step_x s10 (rorI .r6 .r6 8) .r6 ((s10.gpr .r6).rotateRight 8)
      (by rw [rorI, exec_rotr_d (by decide)])
    refine ⟨s11, ?_, by rw [← lane0]; exact u11.lane (by decide) _ _, by rw [← lane1]; exact u11.lane (by decide) _ _,
      fun k hk b hb h0 h1 => by rw [u11.lane (by decide), lanes k hk b hb h0 h1], ?_, ?_,
      fun r ha hb hc' h3 _ => by rw [u11.other h3, G10 r ha hb hc'], by rw [u11.rd, rd10'], by rw [u11.wr, wr10'],
      by rw [u11.sp, sp10'], by rw [u11.mem]; exact frame⟩
    · have : keyRound j = [shrI .r9 .r6 32, shrI .r10 .r7 32, addW .r9 .r9 .r10,
          .lis .r11 (c.extractLsb' 16 16), .ori .r11 .r11 (c.extractLsb' 0 16),
          subW .r9 .r9 .r11, stW (gSlot (2 * j)) (2 * j % 16) .r9,
          subW .r9 .r6 .r7, addW .r9 .r9 .r11, stW (gSlot (2 * j + 1)) ((2 * j + 1) % 16) .r9] ++
          [rorI .r6 .r6 8] := by simp only [keyRound, hj2, ite_true]; rfl
      rw [this]
      exact runBlock_trans hrun (by rw [runBlock_cons, e11, runStep_some, runBlock_nil])
    · rw [u11.self, G10 _ (by decide) (by decide) (by decide), ite_eq_left_iff.mpr (fun h => absurd hj2 h)]
    · rw [u11.other (by decide), G10 _ (by decide) (by decide) (by decide),
        ite_eq_left_iff.mpr (fun h => absurd hj2 h)]
  · obtain ⟨s11, e11, u11⟩ := step_x s10 (rorI .r7 .r7 56) .r7 ((s10.gpr .r7).rotateRight 56)
      (by rw [rorI, exec_rotr_d (by decide)])
    refine ⟨s11, ?_, by rw [← lane0]; exact u11.lane (by decide) _ _, by rw [← lane1]; exact u11.lane (by decide) _ _,
      fun k hk b hb h0 h1 => by rw [u11.lane (by decide), lanes k hk b hb h0 h1], ?_, ?_,
      fun r ha hb hc' _ h4 => by rw [u11.other h4, G10 r ha hb hc'], by rw [u11.rd, rd10'], by rw [u11.wr, wr10'],
      by rw [u11.sp, sp10'], by rw [u11.mem]; exact frame⟩
    · have : keyRound j = [shrI .r9 .r6 32, shrI .r10 .r7 32, addW .r9 .r9 .r10,
          .lis .r11 (c.extractLsb' 16 16), .ori .r11 .r11 (c.extractLsb' 0 16),
          subW .r9 .r9 .r11, stW (gSlot (2 * j)) (2 * j % 16) .r9,
          subW .r9 .r6 .r7, addW .r9 .r9 .r11, stW (gSlot (2 * j + 1)) ((2 * j + 1) % 16) .r9] ++
          [rorI .r7 .r7 56] := by simp only [keyRound, hj2, ite_false]; rfl
      rw [this]
      exact runBlock_trans hrun (by rw [runBlock_cons, e11, runStep_some, runBlock_nil])
    · rw [u11.other (by decide), G10 _ (by decide) (by decide) (by decide),
        ite_eq_right_iff.mpr (fun h => absurd h hj2)]
    · rw [u11.self, G10 _ (by decide) (by decide) (by decide), ite_eq_right_iff.mpr (fun h => absurd h hj2)]

end VG.Proof.Seed.PPC64LE
