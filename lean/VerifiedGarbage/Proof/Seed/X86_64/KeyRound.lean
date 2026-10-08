import VerifiedGarbage.Proof.Seed.X86_64.Round
import VerifiedGarbage.Impl.Seed.X86_64.ExpandKey

/-!
# A round of the key schedule on x86-64

`keyRound_ok`: `keyRound j` writes round `j + 1`'s two inputs of `G`, from
`r10 = Key0 || Key1` and `r11 = Key2 || Key3`, to their lanes, and rotates
one of the two.
-/

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Seed.X86_64 VG.Impl.Aes.X86_64

-- The steps share one set of rewrites, not all of which each uses.
set_option linter.unusedSimpArgs false

theorem exec_movR' (s : State) (d r : Reg) : exec (movR d r) s = some (s.setReg d (s.gpr r)) := rfl

theorem exec_shrI (s : State) (d : Reg) {n : Nat} (h1 : 1 ≤ n) (h2 : n ≤ 63) :
    exec (shrI d n) s = some ((s.setFlags (some ((s.gpr d).getLsbD (n - 1)))
      (if n = 1 then some (s.gpr d).msb else none) (some (s.gpr d >>> n == 0))
      (some (s.gpr d >>> n).msb)).setReg d (s.gpr d >>> n)) := by
  simp only [shrI, exec, execShift, h1, h2, and_self, ite_true]

theorem exec_rorI (s : State) (d : Reg) {n : Nat} (h1 : 1 ≤ n) (h2 : n ≤ 63) :
    exec (rorI d n) s = some ((s.setFlags (some ((s.gpr d).rotateRight n).msb)
      (if n = 1 then some (((s.gpr d).rotateRight n).msb ^^ ((s.gpr d).rotateRight n).getMsbD 1) else none)
      s.zf s.sf).setReg d ((s.gpr d).rotateRight n)) := by
  simp only [rorI, exec, execShift, h1, h2, and_self, ite_true]

theorem exec_add32_reg (s : State) (d r : Reg) :
    exec (.alu32 .add d (.reg r)) s =
      some ((arithFlags s ((s.gpr d).setWidth 32 + (s.gpr r).setWidth 32)
        (decide (2 ^ 32 ≤ ((s.gpr d).setWidth 32).toNat + ((s.gpr r).setWidth 32).toNat))
        (addOverflow ((s.gpr d).setWidth 32) ((s.gpr r).setWidth 32)
          ((s.gpr d).setWidth 32 + (s.gpr r).setWidth 32))).setReg32 d
        ((s.gpr d).setWidth 32 + (s.gpr r).setWidth 32)) := rfl

theorem exec_sub32_reg (s : State) (d r : Reg) :
    exec (.alu32 .sub d (.reg r)) s =
      some ((arithFlags s ((s.gpr d).setWidth 32 - (s.gpr r).setWidth 32)
        (decide (((s.gpr d).setWidth 32).toNat < ((s.gpr r).setWidth 32).toNat))
        (subOverflow ((s.gpr d).setWidth 32) ((s.gpr r).setWidth 32)
          ((s.gpr d).setWidth 32 - (s.gpr r).setWidth 32))).setReg32 d
        ((s.gpr d).setWidth 32 - (s.gpr r).setWidth 32)) := rfl

theorem exec_add32_imm (s : State) (d : Reg) (v : BitVec 32) :
    exec (.alu32 .add d (.imm v)) s =
      some ((arithFlags s ((s.gpr d).setWidth 32 + v)
        (decide (2 ^ 32 ≤ ((s.gpr d).setWidth 32).toNat + v.toNat))
        (addOverflow ((s.gpr d).setWidth 32) v ((s.gpr d).setWidth 32 + v))).setReg32 d
        ((s.gpr d).setWidth 32 + v)) := rfl

theorem exec_sub32_imm (s : State) (d : Reg) (v : BitVec 32) :
    exec (.alu32 .sub d (.imm v)) s =
      some ((arithFlags s ((s.gpr d).setWidth 32 - v)
        (decide (((s.gpr d).setWidth 32).toNat < v.toNat))
        (subOverflow ((s.gpr d).setWidth 32) v ((s.gpr d).setWidth 32 - v))).setReg32 d
        ((s.gpr d).setWidth 32 - v)) := rfl

theorem laneA_setFlags (s : State) (a b c d : Option Bool) (k i : Nat) :
    laneA (s.setFlags a b c d) k i = laneA s k i := rfl

theorem gSlot_mem (i : Nat) : gSlot i ∈ arrays := by
  unfold gSlot; split <;> decide

/-- `G`'s inputs have distinct lanes. -/
theorem gIn_apart : ∀ i < 32, ∀ i' < 32, i ≠ i' → gSlot i ≠ gSlot i' ∨ i % 16 ≠ i' % 16 := by decide

/-- The first input of `G` in round `j + 1`, from `Key0 || Key1` and `Key2 || Key3`. -/
def gIn0 (x y : BitVec 64) (c : BitVec 32) : BitVec 32 := (x >>> 32).setWidth 32 + (y >>> 32).setWidth 32 - c

/-- The second. -/
def gIn1 (x y : BitVec 64) (c : BitVec 32) : BitVec 32 := x.setWidth 32 - y.setWidth 32 + c

/-- `t` is `s` with the register `d` set to `v` (and perhaps the flags). -/
structure Upd (s t : State) (d : Reg) (v : BitVec 64) : Prop where
  gpr : ∀ x, t.gpr x = if x = d then v else s.gpr x
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem Upd.self {s t : State} {d : Reg} {v : BitVec 64} (h : Upd s t d v) : t.gpr d = v := by
  simp [h.gpr]

theorem Upd.other {s t : State} {d : Reg} {v : BitVec 64} (h : Upd s t d v) {x : Reg} (hx : x ≠ d) :
    t.gpr x = s.gpr x := by
  rw [h.gpr]; simp [hx]

theorem Upd.lane {s t : State} {d : Reg} {v : BitVec 64} (h : Upd s t d v) (hd : d ≠ .r9) (k b : Nat) :
    lv t k b = lv s k b := by
  simp only [lv, laneA, h.mem, h.other (Ne.symm hd)]

theorem upd_of {s t : State} {d : Reg} {v : BitVec 64} (e : t = s.setReg d v) : Upd s t d v :=
  ⟨fun x => by subst e; rw [gpr_setReg], by subst e; rfl, by subst e; rfl, by subst e; rfl⟩

theorem upd_flags {s t : State} {d : Reg} {v : BitVec 64} (a b c e : Option Bool)
    (h : t = (s.setFlags a b c e).setReg d v) : Upd s t d v :=
  ⟨fun x => by subst h; rw [gpr_setReg, gpr_setFlags], by subst h; rfl, by subst h; rfl, by subst h; rfl⟩

theorem upd_arith {s t : State} {d : Reg} {w : Nat} (x : BitVec w) (c o : Bool) (v : BitVec 32)
    (h : t = (arithFlags s x c o).setReg32 d v) : Upd s t d (v.setWidth 64) :=
  ⟨fun y => by subst h; rw [State.setReg32, gpr_setReg, gpr_arithFlags], by subst h; rfl, by subst h; rfl,
    by subst h; rfl⟩

theorem step_movR (s : State) (d r : Reg) : ∃ t, exec (movR d r) s = some t ∧ Upd s t d (s.gpr r) :=
  ⟨_, exec_movR' s d r, upd_of rfl⟩

theorem step_shrI (s : State) (d : Reg) {n : Nat} (h1 : 1 ≤ n) (h2 : n ≤ 63) :
    ∃ t, exec (shrI d n) s = some t ∧ Upd s t d (s.gpr d >>> n) :=
  ⟨_, exec_shrI s d h1 h2, upd_flags _ _ _ _ rfl⟩

theorem step_rorI (s : State) (d : Reg) {n : Nat} (h1 : 1 ≤ n) (h2 : n ≤ 63) :
    ∃ t, exec (rorI d n) s = some t ∧ Upd s t d ((s.gpr d).rotateRight n) :=
  ⟨_, exec_rorI s d h1 h2, upd_flags _ _ _ _ rfl⟩

theorem step_add32_reg (s : State) (d r : Reg) :
    ∃ t, exec (.alu32 .add d (.reg r)) s = some t ∧
      Upd s t d (((s.gpr d).setWidth 32 + (s.gpr r).setWidth 32).setWidth 64) :=
  ⟨_, exec_add32_reg s d r, upd_arith _ _ _ _ rfl⟩

theorem step_sub32_reg (s : State) (d r : Reg) :
    ∃ t, exec (.alu32 .sub d (.reg r)) s = some t ∧
      Upd s t d (((s.gpr d).setWidth 32 - (s.gpr r).setWidth 32).setWidth 64) :=
  ⟨_, exec_sub32_reg s d r, upd_arith _ _ _ _ rfl⟩

theorem step_add32_imm (s : State) (d : Reg) (v : BitVec 32) :
    ∃ t, exec (.alu32 .add d (.imm v)) s = some t ∧ Upd s t d (((s.gpr d).setWidth 32 + v).setWidth 64) :=
  ⟨_, exec_add32_imm s d v, upd_arith _ _ _ _ rfl⟩

theorem step_sub32_imm (s : State) (d : Reg) (v : BitVec 32) :
    ∃ t, exec (.alu32 .sub d (.imm v)) s = some t ∧ Upd s t d (((s.gpr d).setWidth 32 - v).setWidth 64) :=
  ⟨_, exec_sub32_imm s d v, upd_arith _ _ _ _ rfl⟩

/-- A store of `rax`'s low half to a lane. -/
theorem step_store_lane {s : State} (h : Room s) {k b : Nat} (hk : k ∈ arrays) (hb : b < 16) :
    ∃ t, exec (.store32 (lane .r9 k b) .rax) s = some t ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.mem = s.mem.writeW (laneA s k b) ((s.gpr .rax).setWidth 32) :=
  ⟨_, exec_store32_lane h hk hb .rax, rfl, rfl, rfl, rfl⟩

theorem keyRound_ok {j : Nat} (hj : j < 16) {s : State} (h : Room s) :
    ∃ s', runBlock isa (keyRound j) s = some s' ∧
      lv s' (gSlot (2 * j)) (2 * j % 16) = gIn0 (s.gpr .r10) (s.gpr .r11) (kcs.getD j 0) ∧
      lv s' (gSlot (2 * j + 1)) ((2 * j + 1) % 16) = gIn1 (s.gpr .r10) (s.gpr .r11) (kcs.getD j 0) ∧
      (∀ k ∈ arrays, ∀ b < 16, (k ≠ gSlot (2 * j) ∨ b ≠ 2 * j % 16) →
        (k ≠ gSlot (2 * j + 1) ∨ b ≠ (2 * j + 1) % 16) → lv s' k b = lv s k b) ∧
      s'.gpr .r10 = (if j % 2 = 0 then (s.gpr .r10).rotateRight 8 else s.gpr .r10) ∧
      s'.gpr .r11 = (if j % 2 = 0 then s.gpr .r11 else (s.gpr .r11).rotateRight 56) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [arraysR s] s.mem s'.mem := by
  have hb0 : 2 * j % 16 < 16 := Nat.mod_lt _ (by decide)
  have hb1 : (2 * j + 1) % 16 < 16 := Nat.mod_lt _ (by decide)
  have hd : gSlot (2 * j + 1) ≠ gSlot (2 * j) ∨ (2 * j + 1) % 16 ≠ 2 * j % 16 :=
    gIn_apart _ (by omega) _ (by omega) (by omega)
  let c := kcs.getD j 0
  obtain ⟨s1, e1, u1⟩ := step_movR s .rax .r10
  obtain ⟨s2, e2, u2⟩ := step_shrI s1 .rax (n := 32) (by decide) (by decide)
  obtain ⟨s3, e3, u3⟩ := step_movR s2 .rcx .r11
  obtain ⟨s4, e4, u4⟩ := step_shrI s3 .rcx (n := 32) (by decide) (by decide)
  obtain ⟨s5, e5, u5⟩ := step_add32_reg s4 .rax .rcx
  obtain ⟨s6, e6, u6⟩ := step_sub32_imm s5 .rax c
  have room6 : Room s6 := room_congr h (by rw [u6.other (by decide), u5.other (by decide),
    u4.other (by decide), u3.other (by decide), u2.other (by decide), u1.other (by decide)])
    (by rw [u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr])
  obtain ⟨s7, e7, g7, rd7, wr7, m7⟩ := step_store_lane room6 (gSlot_mem (2 * j)) hb0
  obtain ⟨s8, e8, u8⟩ := step_movR s7 .rax .r10
  obtain ⟨s9, e9, u9⟩ := step_sub32_reg s8 .rax .r11
  obtain ⟨s10, e10, u10⟩ := step_add32_imm s9 .rax c
  have room10 : Room s10 := room_congr room6 (by rw [u10.other (by decide), u9.other (by decide),
    u8.other (by decide), g7]) (by rw [u10.wr, u9.wr, u8.wr, wr7])
  obtain ⟨s11, e11, g11, rd11, wr11, m11⟩ := step_store_lane room10 (gSlot_mem (2 * j + 1)) hb1
  have r9_6 : s6.gpr .r9 = s.gpr .r9 := by rw [u6.other (by decide), u5.other (by decide),
    u4.other (by decide), u3.other (by decide), u2.other (by decide), u1.other (by decide)]
  have r9_10 : s10.gpr .r9 = s.gpr .r9 := by
    rw [u10.other (by decide), u9.other (by decide), u8.other (by decide), g7, r9_6]
  have lA6 : ∀ k b, laneA s6 k b = laneA s k b := fun k b => by simp only [laneA, r9_6]
  have lA10 : ∀ k b, laneA s10 k b = laneA s k b := fun k b => by simp only [laneA, r9_10]
  -- the values
  have v6 : (s6.gpr .rax).setWidth 32 = gIn0 (s.gpr .r10) (s.gpr .r11) c := by
    rw [u6.self, setWidth_setWidth_32, u5.self, setWidth_setWidth_32, u4.other (by decide), u4.self,
      u3.self, u3.other (by decide), u2.self, u2.other (by decide), u1.self, u1.other (by decide)]
    rfl
  have v10 : (s10.gpr .rax).setWidth 32 = gIn1 (s.gpr .r10) (s.gpr .r11) c := by
    rw [u10.self, setWidth_setWidth_32, u9.self, setWidth_setWidth_32, u8.self, u8.other (by decide), g7,
      u6.other (by decide), u5.other (by decide), u4.other (by decide), u3.other (by decide),
      u2.other (by decide), u1.other (by decide), u6.other (by decide), u5.other (by decide),
      u4.other (by decide), u3.other (by decide), u2.other (by decide), u1.other (by decide)]
    rfl
  have mem10 : s10.mem = s7.mem := by rw [u10.mem, u9.mem, u8.mem]
  have mem6 : s6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have hrun : runBlock isa ([movR .rax .r10, shrI .rax 32, movR .rcx .r11, shrI .rcx 32,
      .alu32 .add .rax (.reg .rcx), .alu32 .sub .rax (.imm c), .store32 (gIn (2 * j)) .rax,
      movR .rax .r10, .alu32 .sub .rax (.reg .r11), .alu32 .add .rax (.imm c),
      .store32 (gIn (2 * j + 1)) .rax] : List Instr) s = some s11 := by
    rw [runBlock_cons, e1, runStep_some, runBlock_cons, e2, runStep_some, runBlock_cons, e3, runStep_some,
      runBlock_cons, e4, runStep_some, runBlock_cons, e5, runStep_some, runBlock_cons, e6, runStep_some,
      runBlock_cons, gIn, e7, runStep_some, runBlock_cons, e8, runStep_some, runBlock_cons, e9, runStep_some,
      runBlock_cons, e10, runStep_some, runBlock_cons, gIn, e11, runStep_some, runBlock_nil]
  -- the lanes after both stores
  have lv11 : ∀ k ∈ arrays, ∀ b < 16, lv s11 k b =
      ((s.mem.writeW (laneA s (gSlot (2 * j)) (2 * j % 16)) (gIn0 (s.gpr .r10) (s.gpr .r11) c)).writeW
        (laneA s (gSlot (2 * j + 1)) ((2 * j + 1) % 16)) (gIn1 (s.gpr .r10) (s.gpr .r11) c)).readW
        (laneA s k b) 32 := by
    intro k _ b _
    simp only [lv, laneA, g11, u10.other (show Reg.r9 ≠ .rax by decide), u9.other (show Reg.r9 ≠ .rax by decide),
      u8.other (show Reg.r9 ≠ .rax by decide), g7]
    rw [m11, mem10, m7, lA10, lA6, v6, v10, mem6]
    simp only [laneA, r9_6]
  have lane0 : lv s11 (gSlot (2 * j)) (2 * j % 16) = gIn0 (s.gpr .r10) (s.gpr .r11) c := by
    rw [lv11 _ (gSlot_mem _) _ hb0, readW_writeW_lane (gSlot_mem _) hb0 (gSlot_mem _) hb1
      (by rcases hd with h | h; exact Or.inl (Ne.symm h); exact Or.inr (Ne.symm h)), Mem.readW_writeW_self32]
  have lane1 : lv s11 (gSlot (2 * j + 1)) ((2 * j + 1) % 16) = gIn1 (s.gpr .r10) (s.gpr .r11) c := by
    rw [lv11 _ (gSlot_mem _) _ hb1, Mem.readW_writeW_self32]
  have lanes : ∀ k ∈ arrays, ∀ b < 16, (k ≠ gSlot (2 * j) ∨ b ≠ 2 * j % 16) →
      (k ≠ gSlot (2 * j + 1) ∨ b ≠ (2 * j + 1) % 16) → lv s11 k b = lv s k b := by
    intro k hk b hb h0 h1
    rw [lv11 k hk b hb, readW_writeW_lane hk hb (gSlot_mem _) hb1 h1,
      readW_writeW_lane hk hb (gSlot_mem _) hb0 h0]
    rfl
  have frame : Frame [arraysR s] s.mem s11.mem := by
    rw [m11, mem10, m7, lA10, lA6, mem6]
    exact ((Frame.refl _ _).writeW List.mem_cons_self _ (lane_inArrays (gSlot_mem _) hb0 s)).writeW
      List.mem_cons_self _ (lane_inArrays (gSlot_mem _) hb1 s)
  have G11 : ∀ r, r ≠ .rax → r ≠ .rcx → s11.gpr r = s.gpr r := by
    intro r ha hc
    rw [g11, u10.other ha, u9.other ha, u8.other ha, g7, u6.other ha, u5.other ha, u4.other hc, u3.other hc,
      u2.other ha, u1.other ha]
  have rd11' : s11.rd = s.rd := by rw [rd11, u10.rd, u9.rd, u8.rd, rd7, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]
  have wr11' : s11.wr = s.wr := by rw [wr11, u10.wr, u9.wr, u8.wr, wr7, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]
  -- the rotation
  by_cases hj2 : j % 2 = 0
  · obtain ⟨s12, e12, u12⟩ := step_rorI s11 .r10 (n := 8) (by decide) (by decide)
    refine ⟨s12, ?_, by rw [← lane0]; exact u12.lane (by decide) _ _, by rw [← lane1]; exact u12.lane (by decide) _ _,
      fun k hk b hb h0 h1 => by rw [u12.lane (by decide), lanes k hk b hb h0 h1], ?_, ?_,
      fun r ha hc h10 _ => by rw [u12.other h10, G11 r ha hc], by rw [u12.rd, rd11'], by rw [u12.wr, wr11'],
      by rw [u12.mem]; exact frame⟩
    · have : keyRound j = [movR .rax .r10, shrI .rax 32, movR .rcx .r11, shrI .rcx 32,
          .alu32 .add .rax (.reg .rcx), .alu32 .sub .rax (.imm c), .store32 (gIn (2 * j)) .rax,
          movR .rax .r10, .alu32 .sub .rax (.reg .r11), .alu32 .add .rax (.imm c),
          .store32 (gIn (2 * j + 1)) .rax] ++ [rorI .r10 8] := by simp only [keyRound, hj2, ite_true]; rfl
      rw [this]
      exact runBlock_trans hrun (by rw [runBlock_cons, e12, runStep_some, runBlock_nil])
    · rw [u12.self, G11 _ (by decide) (by decide), ite_eq_left_iff.mpr (fun h => absurd hj2 h)]
    · rw [u12.other (by decide), G11 _ (by decide) (by decide), ite_eq_left_iff.mpr (fun h => absurd hj2 h)]
  · obtain ⟨s12, e12, u12⟩ := step_rorI s11 .r11 (n := 56) (by decide) (by decide)
    refine ⟨s12, ?_, by rw [← lane0]; exact u12.lane (by decide) _ _, by rw [← lane1]; exact u12.lane (by decide) _ _,
      fun k hk b hb h0 h1 => by rw [u12.lane (by decide), lanes k hk b hb h0 h1], ?_, ?_,
      fun r ha hc _ h11 => by rw [u12.other h11, G11 r ha hc], by rw [u12.rd, rd11'], by rw [u12.wr, wr11'],
      by rw [u12.mem]; exact frame⟩
    · have : keyRound j = [movR .rax .r10, shrI .rax 32, movR .rcx .r11, shrI .rcx 32,
          .alu32 .add .rax (.reg .rcx), .alu32 .sub .rax (.imm c), .store32 (gIn (2 * j)) .rax,
          movR .rax .r10, .alu32 .sub .rax (.reg .r11), .alu32 .add .rax (.imm c),
          .store32 (gIn (2 * j + 1)) .rax] ++ [rorI .r11 56] := by simp only [keyRound, hj2, ite_false]; rfl
      rw [this]
      exact runBlock_trans hrun (by rw [runBlock_cons, e12, runStep_some, runBlock_nil])
    · rw [u12.other (by decide), G11 _ (by decide) (by decide), ite_eq_right_iff.mpr (fun h => absurd h hj2)]
    · rw [u12.self, G11 _ (by decide) (by decide), ite_eq_right_iff.mpr (fun h => absurd h hj2)]

end VG.Proof.Seed.X86_64
