module

public import VerifiedGarbage.Spec.Seed.Contract
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Seed.AArch64.ConstantTime
public import VerifiedGarbage.Proof.Seed.Scratch
public import VerifiedGarbage.Impl.Seed.AArch64.ExpandKey
public import VerifiedGarbage.Proof.Seed.AArch64.Round
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Seed.KeySchedule
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Seed.AArch64.Verified
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Seed.Memory
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Seed.SboxLit
import VerifiedGarbage.Proof.Framework.AArch64.Straight
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Seed.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch

/-! ### `Seed.AArch64.KeyRound`, which only this module used -/

section

/-!
# A round of the key schedule on AArch64

`keyRound_ok`: `keyRound j` writes round `j + 1`'s two inputs of `G`, from
`x3 = Key0 || Key1` and `x4 = Key2 || Key3`, to their lanes, and rotates
one of the two.
-/

@[expose] public section

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.AArch64.RegUpd VG.Impl.Seed.AArch64 VG.Impl.Aes.AArch64

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

theorem Upd.lane {s t : State} {d : Reg} {v : BitVec 64} (h : Upd s t d v) (hd : d ≠ .x5) (k b : Nat) :
    lv t k b = lv s k b := by
  simp only [lv, laneA, h.mem, h.other (Ne.symm hd)]

theorem upd_write (s : State) (sz : Size) (d : Reg) (v : BitVec sz.bits) :
    Upd s (s.write sz d v) d (v.setWidth 64) :=
  ⟨fun _ => gpr_write _ _ _ _ _, rfl, rfl, rfl, rfl⟩

theorem step_x (s : State) (i : Instr) (d : Reg) (v : BitVec 64) (h : exec i s = some (s.write .x d v)) :
    ∃ t, exec i s = some t ∧ Upd s t d v :=
  ⟨_, h, by simpa using upd_write s .x d v⟩

theorem step_w (s : State) (i : Instr) (d : Reg) (v : BitVec 32) (h : exec i s = some (s.write .w d v)) :
    ∃ t, exec i s = some t ∧ Upd s t d (v.setWidth 64) :=
  ⟨_, h, upd_write s .w d v⟩

theorem gSlot_mem (i : Nat) : gSlot i ∈ arrays := by
  unfold gSlot; split <;> decide

/-- `G`'s inputs have distinct lanes. -/
theorem gIn_apart : ∀ i < 32, ∀ i' < 32, i ≠ i' → gSlot i ≠ gSlot i' ∨ i % 16 ≠ i' % 16 := by decide

/-- The first input of `G` in round `j + 1`, from `Key0 || Key1` and `Key2 || Key3`. -/
def gIn0 (x y : BitVec 64) (c : BitVec 32) : BitVec 32 := (x >>> 32).setWidth 32 + (y >>> 32).setWidth 32 - c

/-- The second. -/
def gIn1 (x y : BitVec 64) (c : BitVec 32) : BitVec 32 := x.setWidth 32 - y.setWidth 32 + c

/-- A store of `x14`'s low half to a lane. -/
theorem step_store_lane {s : State} (h : Room s) {k b : Nat} (hk : k ∈ arrays) (hb : b < 16) :
    ∃ t, exec (stW k b .x14) s = some t ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.mem = s.mem.writeW (laneA s k b) ((s.gpr .x14).setWidth 32) :=
  ⟨_, exec_stW_lane h hk hb .x14, rfl, rfl, rfl, rfl, rfl⟩

theorem keyRound_ok {j : Nat} (hj : j < 16) {s : State} (h : Room s) :
    ∃ s', runBlock isa (keyRound j) s = some s' ∧
      lv s' (gSlot (2 * j)) (2 * j % 16) = gIn0 (s.gpr .x3) (s.gpr .x4) (kcs.getD j 0) ∧
      lv s' (gSlot (2 * j + 1)) ((2 * j + 1) % 16) = gIn1 (s.gpr .x3) (s.gpr .x4) (kcs.getD j 0) ∧
      (∀ k ∈ arrays, ∀ b < 16, (k ≠ gSlot (2 * j) ∨ b ≠ 2 * j % 16) →
        (k ≠ gSlot (2 * j + 1) ∨ b ≠ (2 * j + 1) % 16) → lv s' k b = lv s k b) ∧
      s'.gpr .x3 = (if j % 2 = 0 then (s.gpr .x3).rotateRight 8 else s.gpr .x3) ∧
      s'.gpr .x4 = (if j % 2 = 0 then s.gpr .x4 else (s.gpr .x4).rotateRight 56) ∧
      (∀ r, r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x3 → r ≠ .x4 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [arraysR s] s.mem s'.mem := by
  have hb0 : 2 * j % 16 < 16 := Nat.mod_lt _ (by decide)
  have hb1 : (2 * j + 1) % 16 < 16 := Nat.mod_lt _ (by decide)
  have hd : gSlot (2 * j + 1) ≠ gSlot (2 * j) ∨ (2 * j + 1) % 16 ≠ 2 * j % 16 :=
    gIn_apart _ (by omega_using [hj]) _ (by omega_using [hj]) (by omega_using [])
  let c := kcs.getD j 0
  obtain ⟨s1, e1, u1⟩ := step_x s (lsrI .x14 .x3 32) .x14 (s.gpr .x3 >>> 32)
    (by rw [lsrI, exec_lsr_x (by decide), read_x])
  obtain ⟨s2, e2, u2⟩ := step_x s1 (lsrI .x15 .x4 32) .x15 (s1.gpr .x4 >>> 32)
    (by rw [lsrI, exec_lsr_x (by decide), read_x])
  obtain ⟨s3, e3, u3⟩ := step_w s2 (addW .x14 .x14 .x15) .x14 (s2.read .w .x14 + s2.read .w .x15) rfl
  obtain ⟨s4, e4, u4⟩ := step_w s3 (.movz .w .x16 (c.extractLsb' 0 16) 0) .x16 ((c.extractLsb' 0 16).setWidth 32)
    exec_movz_w
  obtain ⟨s5, e5, u5⟩ := step_w s4 (.movk .w .x16 (c.extractLsb' 16 16) 1) .x16
    ((s4.gpr .x16).setWidth 32 &&& (0xFFFF : BitVec 32) ||| (c.extractLsb' 16 16).setWidth 32 <<< 16)
    exec_movk_w
  obtain ⟨s6, e6, u6⟩ := step_w s5 (subW .x14 .x14 .x16) .x14 (s5.read .w .x14 - s5.read .w .x16) rfl
  have g6 : ∀ r, r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → s6.gpr r = s.gpr r := fun r a b c' => by
    rw [u6.other a, u5.other c', u4.other c', u3.other a, u2.other b, u1.other a]
  have room6 : Room s6 := room_congr h (g6 _ (by decide) (by decide) (by decide))
    (by rw [u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr])
  obtain ⟨s7, e7, g7, rd7, wr7, sp7, m7⟩ := step_store_lane room6 (gSlot_mem (2 * j)) hb0
  obtain ⟨s8, e8, u8⟩ := step_w s7 (subW .x14 .x3 .x4) .x14 (s7.read .w .x3 - s7.read .w .x4) rfl
  obtain ⟨s9, e9, u9⟩ := step_w s8 (addW .x14 .x14 .x16) .x14 (s8.read .w .x14 + s8.read .w .x16) rfl
  have room9 : Room s9 := room_congr room6 (by rw [u9.other (by decide), u8.other (by decide), g7])
    (by rw [u9.wr, u8.wr, wr7])
  obtain ⟨s10, e10, g10, rd10, wr10, sp10, m10⟩ := step_store_lane room9 (gSlot_mem (2 * j + 1)) hb1
  have r9_6 : s6.gpr .x5 = s.gpr .x5 := g6 _ (by decide) (by decide) (by decide)
  have r9_9 : s9.gpr .x5 = s.gpr .x5 := by rw [u9.other (by decide), u8.other (by decide), g7, r9_6]
  have lA6 : ∀ k b, laneA s6 k b = laneA s k b := fun k b => by simp only [laneA, r9_6]
  have lA9 : ∀ k b, laneA s9 k b = laneA s k b := fun k b => by simp only [laneA, r9_9]
  -- the values
  have hc : (s5.gpr .x16).setWidth 32 = c := by
    rw [u5.self, setWidth_setWidth_32, u4.self, setWidth_setWidth_32]
    simpa using movz_movk c
  have v6 : (s6.gpr .x14).setWidth 32 = gIn0 (s.gpr .x3) (s.gpr .x4) c := by
    rw [u6.self, setWidth_setWidth_32]
    simp only [State.read, Size.bits]
    rw [hc, u5.other (by decide), u4.other (by decide), u3.self, setWidth_setWidth_32]
    simp only [State.read, Size.bits]
    rw [u2.other (by decide), u2.self, u1.self, u1.other (by decide)]
    rfl
  have v9 : (s9.gpr .x14).setWidth 32 = gIn1 (s.gpr .x3) (s.gpr .x4) c := by
    rw [u9.self, setWidth_setWidth_32]
    simp only [State.read, Size.bits]
    rw [u8.self, setWidth_setWidth_32, u8.other (show Reg.x16 ≠ .x14 by decide), g7,
      u6.other (show Reg.x16 ≠ .x14 by decide), hc]
    simp only [State.read, Size.bits]
    rw [g7, g6 .x3 (by decide) (by decide) (by decide), g6 .x4 (by decide) (by decide) (by decide)]
    rfl
  have mem9 : s9.mem = s7.mem := by rw [u9.mem, u8.mem]
  have mem6 : s6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have hrun : runBlock isa ([lsrI .x14 .x3 32, lsrI .x15 .x4 32, addW .x14 .x14 .x15,
      .movz .w .x16 (c.extractLsb' 0 16) 0, .movk .w .x16 (c.extractLsb' 16 16) 1,
      subW .x14 .x14 .x16, stW (gSlot (2 * j)) (2 * j % 16) .x14,
      subW .x14 .x3 .x4, addW .x14 .x14 .x16, stW (gSlot (2 * j + 1)) ((2 * j + 1) % 16) .x14] :
      List Instr) s = some s10 := by
    rw [runBlock_cons, e1, runStep_some, runBlock_cons, e2, runStep_some, runBlock_cons, e3, runStep_some,
      runBlock_cons, e4, runStep_some, runBlock_cons, e5, runStep_some, runBlock_cons, e6, runStep_some,
      runBlock_cons, e7, runStep_some, runBlock_cons, e8, runStep_some, runBlock_cons, e9, runStep_some,
      runBlock_cons, e10, runStep_some, runBlock_nil]
  -- the lanes after both stores
  have lv10 : ∀ k ∈ arrays, ∀ b < 16, lv s10 k b =
      ((s.mem.writeW (laneA s (gSlot (2 * j)) (2 * j % 16)) (gIn0 (s.gpr .x3) (s.gpr .x4) c)).writeW
        (laneA s (gSlot (2 * j + 1)) ((2 * j + 1) % 16)) (gIn1 (s.gpr .x3) (s.gpr .x4) c)).readW
        (laneA s k b) 32 := by
    intro k _ b _
    simp only [lv, laneA, g10, u9.other (show Reg.x5 ≠ .x14 by decide), u8.other (show Reg.x5 ≠ .x14 by decide),
      g7]
    rw [m10, mem9, m7, lA9, lA6, v6, v9, mem6]
    simp only [laneA, r9_6]
  have lane0 : lv s10 (gSlot (2 * j)) (2 * j % 16) = gIn0 (s.gpr .x3) (s.gpr .x4) c := by
    rw [lv10 _ (gSlot_mem _) _ hb0, readW_writeW_lane (gSlot_mem _) hb0 (gSlot_mem _) hb1
      (by rcases hd with h | h; exact Or.inl (Ne.symm h); exact Or.inr (Ne.symm h)), Mem.readW_writeW_self32]
  have lane1 : lv s10 (gSlot (2 * j + 1)) ((2 * j + 1) % 16) = gIn1 (s.gpr .x3) (s.gpr .x4) c := by
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
  have G10 : ∀ r, r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → s10.gpr r = s.gpr r := by
    intro r ha hb hc'
    rw [g10, u9.other ha, u8.other ha, g7, g6 r ha hb hc']
  have rd10' : s10.rd = s.rd := by rw [rd10, u9.rd, u8.rd, rd7, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]
  have wr10' : s10.wr = s.wr := by rw [wr10, u9.wr, u8.wr, wr7, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]
  have sp10' : s10.sp = s.sp := by rw [sp10, u9.sp, u8.sp, sp7, u6.sp, u5.sp, u4.sp, u3.sp, u2.sp, u1.sp]
  -- the rotation
  by_cases hj2 : j % 2 = 0
  · obtain ⟨s11, e11, u11⟩ := step_x s10 (rorI .x3 .x3 8) .x3 ((s10.gpr .x3).rotateRight 8)
      (by rw [rorI, exec_ror_x (by decide), read_x])
    refine ⟨s11, ?_, by rw [← lane0]; exact u11.lane (by decide) _ _, by rw [← lane1]; exact u11.lane (by decide) _ _,
      fun k hk b hb h0 h1 => by rw [u11.lane (by decide), lanes k hk b hb h0 h1], ?_, ?_,
      fun r ha hb hc' h3 _ => by rw [u11.other h3, G10 r ha hb hc'], by rw [u11.rd, rd10'], by rw [u11.wr, wr10'],
      by rw [u11.sp, sp10'], by rw [u11.mem]; exact frame⟩
    · have : keyRound j = [lsrI .x14 .x3 32, lsrI .x15 .x4 32, addW .x14 .x14 .x15,
          .movz .w .x16 (c.extractLsb' 0 16) 0, .movk .w .x16 (c.extractLsb' 16 16) 1,
          subW .x14 .x14 .x16, stW (gSlot (2 * j)) (2 * j % 16) .x14,
          subW .x14 .x3 .x4, addW .x14 .x14 .x16, stW (gSlot (2 * j + 1)) ((2 * j + 1) % 16) .x14] ++
          [rorI .x3 .x3 8] := by simp only [keyRound, hj2, ite_true]; rfl
      rw [this]
      exact runBlock_trans hrun (by rw [runBlock_cons, e11, runStep_some, runBlock_nil])
    · rw [u11.self, G10 _ (by decide) (by decide) (by decide), ite_eq_left_iff.mpr (fun h => absurd hj2 h)]
    · rw [u11.other (by decide), G10 _ (by decide) (by decide) (by decide),
        ite_eq_left_iff.mpr (fun h => absurd hj2 h)]
  · obtain ⟨s11, e11, u11⟩ := step_x s10 (rorI .x4 .x4 56) .x4 ((s10.gpr .x4).rotateRight 56)
      (by rw [rorI, exec_ror_x (by decide), read_x])
    refine ⟨s11, ?_, by rw [← lane0]; exact u11.lane (by decide) _ _, by rw [← lane1]; exact u11.lane (by decide) _ _,
      fun k hk b hb h0 h1 => by rw [u11.lane (by decide), lanes k hk b hb h0 h1], ?_, ?_,
      fun r ha hb hc' _ h4 => by rw [u11.other h4, G10 r ha hb hc'], by rw [u11.rd, rd10'], by rw [u11.wr, wr10'],
      by rw [u11.sp, sp10'], by rw [u11.mem]; exact frame⟩
    · have : keyRound j = [lsrI .x14 .x3 32, lsrI .x15 .x4 32, addW .x14 .x14 .x15,
          .movz .w .x16 (c.extractLsb' 0 16) 0, .movk .w .x16 (c.extractLsb' 16 16) 1,
          subW .x14 .x14 .x16, stW (gSlot (2 * j)) (2 * j % 16) .x14,
          subW .x14 .x3 .x4, addW .x14 .x14 .x16, stW (gSlot (2 * j + 1)) ((2 * j + 1) % 16) .x14] ++
          [rorI .x4 .x4 56] := by simp only [keyRound, hj2, ite_false]; rfl
      rw [this]
      exact runBlock_trans hrun (by rw [runBlock_cons, e11, runStep_some, runBlock_nil])
    · rw [u11.other (by decide), G10 _ (by decide) (by decide) (by decide),
        ite_eq_right_iff.mpr (fun h => absurd h hj2)]
    · rw [u11.self, G10 _ (by decide) (by decide) (by decide), ite_eq_right_iff.mpr (fun h => absurd h hj2)]

end VG.Proof.Seed.AArch64

end

end

/-! ### `Seed.AArch64.KeyVerified`, which only this module used -/

section

/-! ### `Seed.AArch64.Key`, which only this module used -/

section

/-! ### `Seed.AArch64.KeyBody`, which only this module used -/

section

/-! ### `Seed.AArch64.KeyStore`, which only this module used -/

section

/-!
# Copying `G`'s outputs on AArch64

`keyStore_ok`: `keyStore k` copies the sixteen lanes of `G`'s words to the
schedule's words from `k`; `keyMove_ok`: `keyMove` copies the second sixteen
inputs of `G` to its words.
-/

@[expose] public section

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.AArch64.RegUpd VG.Impl.Seed.AArch64 VG.Proof.Seed

/-- The schedule's words from `k`. -/
def outR (s : State) (k : Nat) : Region := ⟨s.gpr .x1 + BitVec.ofNat 64 (4 * k), 64⟩

theorem keyStore_ok (k : Nat) (hk : k ≤ 16) {s : State} (h : Room s)
    (hw : ∀ w < 16, InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (4 * (k + w))) 4)
    (hsep : (outR s k).Disjoint (scratchR s)) :
    ∀ n ≤ 16, ∃ t, runBlock isa ((List.range n).flatMap fun w =>
        [ldW .x14 (tSlot 0) w, .str .w .x14 .x1 (4 * (k + w))]) s = some t ∧
      (∀ w < n, t.mem.readW (s.gpr .x1 + BitVec.ofNat 64 (4 * (k + w))) 32 = lv s (tSlot 0) w) ∧
      (∀ r, r ≠ .x14 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [outR s k] s.mem t.mem
  | 0, _ => ⟨s, runBlock_nil, fun w hw => by omega, fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
  | n + 1, hn => by
    obtain ⟨t, ht, hv, hg, hrd, hwr, hf⟩ := keyStore_ok k hk h hw hsep n (by omega_using [hn])
    obtain x5 : t.gpr .x5 = s.gpr .x5 := hg _ (by decide)
    obtain x1 : t.gpr .x1 = s.gpr .x1 := hg _ (by decide)
    obtain room : Room t := room_congr h x5 hwr
    obtain hlane : lv t (tSlot 0) n = lv s (tSlot 0) n := by
      simp only [lv, laneA, x5]
      refine hf.readW (r := ⟨s.gpr .x5 + BitVec.ofNat 64 (8 * tSlot 0 + 4 * n), 4⟩) (Region.contains_self _ _) ?_
        (by decide)
      intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      refine (hsep.sub_right ?_).symm
      show Region.Sub ⟨s.gpr .x5 + BitVec.ofNat 64 (8 * tSlot 0 + 4 * n), 4⟩ ⟨s.gpr .x5, 8 * scratchSlots⟩
      exact Offset.sub_base _ (by unfold scratchSlots tSlot; omega_using [hn])
    let t1 := t.write .w .x14 (lv t (tSlot 0) n)
    obtain e1 : exec (ldW .x14 (tSlot 0) n) t = some t1 := exec_ldW_lane room mem_tA (by omega_using [hn]) .x14
    obtain hw1 : InRegions t1.wr (t1.gpr .x1 + BitVec.ofNat 64 (4 * (k + n))) 4 := by
      simp only [t1, wr_write, gpr_write_of_ne _ _ _ (show ¬ Reg.x1 = .x14 by decide), hwr, x1]
      exact hw n (by omega_using [hn])
    let t2 := setMem t1 (t.mem.writeW (s.gpr .x1 + BitVec.ofNat 64 (4 * (k + n))) (lv s (tSlot 0) n))
    obtain e2 : exec (.str .w .x14 .x1 (4 * (k + n))) t1 = some t2 := by
      rw [exec_str_w ⟨by omega_using [], by omega_using [hk, hn]⟩ hw1]
      simp only [t1, t2, gpr_write_self, gpr_write_of_ne _ _ _ (show ¬ Reg.x1 = .x14 by decide), x1,
        mem_write, Size.bits, setWidth_setWidth_32, hlane]
      rfl
    refine ⟨t2, ?_, fun w hw' => ?_, fun r hr => ?_, hrd, hwr, ?_⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      exact runBlock_trans ht (by rw [runBlock_cons, e1, runStep_some, runBlock_cons, e2, runStep_some,
        runBlock_nil])
    · simp only [t2, mem_setMem]
      by_cases hwn : w = n
      · subst hwn; rw [Mem.readW_writeW_self32]
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_using [hwn]) (by omega_using [hk, hn, hw']) (by omega_using [hk, hn])) (by decide)]
        exact hv w (by omega_using [hw', hwn])
    · simp only [t2, gpr_setMem, t1, gpr_write_of_ne _ _ _ hr]; exact hg r hr
    · simp only [t2, mem_setMem]
      exact hf.writeW List.mem_cons_self _ (Offset.contains _ (by omega_using []) (by omega_using [hn]) (by omega_using [hk]))

/-- Moving lane `b` of `uSlot` to `G`'s words. -/
def spMove : LaneSpec := [(tSlot 0, fun x => x uSlot)]

theorem keyMove_ok {s : State} (h : Room s) :
    ∃ s', runBlock isa keyMove s = some s' ∧ Room s' ∧
      (∀ k ∈ arrays, ∀ b < 16, lv s' k b = newVal spMove k (fun k' => lv s k' b)) ∧
      Frame [arraysR s] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .x14 → r ≠ .x15 → s'.gpr r = s.gpr r) := by
  refine lanes16_room (f := fun w => [ldW .x14 uSlot w, stW (tSlot 0) w .x14])
    (by decide) ?_ (fun b hb s h => ?_) h
  · intro kv hkv x y hxy
    simp only [spMove, List.mem_singleton] at hkv; subst hkv
    exact hxy uSlot (by decide)
  · rw [runBlock_cons, exec_ldW_lane h (by decide) hb, runStep_some, runBlock_cons,
      exec_stW_lane ?h1 (by decide) hb, runStep_some, runBlock_nil]
    case h1 => exact room_congr h rfl rfl
    refine ⟨_, rfl, ?_, rfl, rfl, fun r h1 h2 => ?_⟩
    · simp only [laneWrites, spMove, List.foldl_cons, List.foldl_nil, gpr_write_self, Size.bits,
        setWidth_setWidth_32, mem_setMem, mem_write,
        laneA_write _ _ _ (show ¬ Reg.x5 = .x14 by decide)]
    · simp only [gpr_write_of_ne _ _ _ h1, gpr_setMem]

end VG.Proof.Seed.AArch64

end

end

/-! ### `Seed.AArch64.KeyRounds`, which only this module used -/

section

/-!
# The sixteen rounds of the key schedule on AArch64

`keyRounds_ok`: after `n` rounds, `x3` and `x4` hold the key words of
round `n + 1` (`keyWords`), and the lanes of `G`'s first `2 * n` inputs hold
them (`gInput`).
-/

@[expose] public section

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Seed.AArch64 VG.Proof.Seed

theorem hi_append (a b : BitVec 32) : ((a ++ b) >>> 32).setWidth 32 = a := by
  ext i hi
  simp only [BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append]
  simp [show ¬ (32 + i < 32) by omega_using [], hi]

theorem split64 (t : BitVec 64) : t.extractLsb' 32 32 ++ t.setWidth 32 = t := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  split <;> simp_all <;> (congr 1; omega_arith)

theorem ror56 (t : BitVec 64) : t.rotateRight 56 = t.rotateLeft 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_rotateRight, BitVec.getLsbD_rotateLeft]

theorem kcs_eq : ∀ j < 16, kcs.getD j 0 = Spec.Seed.kc.getD j 0 := by decide

/-- The key words `k` as `x3` and `x4` hold them. -/
def kx (k : Quad) : BitVec 64 := k.1 ++ k.2.1
def ky (k : Quad) : BitVec 64 := k.2.2.1 ++ k.2.2.2

/-- After `n` rounds of the key schedule. -/
structure KeyInv (key : Spec.Seed.Block) (s₀ : State) (n : Nat) (s : State) : Prop where
  x3 : s.gpr .x3 = kx (keyWords key n)
  x4 : s.gpr .x4 = ky (keyWords key n)
  lanes : ∀ i < 2 * n, lv s (gSlot i) (i % 16) = gInput key i
  regs : ∀ r, r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x3 → r ≠ .x4 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [arraysR s₀] s₀.mem s.mem

theorem keyRounds_ok (key : Spec.Seed.Block) {s₀ : State} (h : Room s₀)
    (h10 : s₀.gpr .x3 = kx (keyWords key 0)) (h11 : s₀.gpr .x4 = ky (keyWords key 0)) :
    ∀ n ≤ 16, ∃ s, runBlock isa ((List.range n).flatMap keyRound) s₀ = some s ∧ KeyInv key s₀ n s
  | 0, _ => ⟨s₀, runBlock_nil, h10, h11, fun i hi => by omega, fun _ _ _ _ _ _ => rfl, rfl, rfl, rfl,
      Frame.refl _ _⟩
  | n + 1, hn => by
    obtain ⟨s, hs, inv⟩ := keyRounds_ok key h h10 h11 n (by omega_using [hn])
    obtain r9 : s.gpr .x5 = s₀.gpr .x5 := inv.regs _ (by decide) (by decide) (by decide) (by decide) (by decide)
    obtain ⟨s', hs', l0, l1, lk, x3', x4', regs', rd', wr', sp', f'⟩ :=
      keyRound_ok (j := n) (by omega_using [hn]) (room_congr h r9 inv.wr)
    refine ⟨s', ?_, ⟨?_, ?_, fun i hi => ?_, fun r a b c d e => ?_, by rw [sp', inv.sp], by rw [rd', inv.rd],
      by rw [wr', inv.wr], ?_⟩⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      exact runBlock_trans hs hs'
    · rw [x3', inv.x3]
      simp only [keyWords, keyStep]
      split
      · simp only [kx]; exact (split64 _).symm
      · rfl
    · rw [x4', inv.x4]
      simp only [keyWords, keyStep]
      split
      · rfl
      · simp only [ky, ror56]; exact (split64 _).symm
    · have g0 : gInput key (2 * n) = (keyWords key n).1 + (keyWords key n).2.2.1 - Spec.Seed.kc.getD n 0 := by
        simp only [gInput, show 2 * n / 2 = n by omega_using [], show 2 * n % 2 = 0 by omega_using [], ite_true]
      obtain g1 : gInput key (2 * n + 1) =
          (keyWords key n).2.1 - (keyWords key n).2.2.2 + Spec.Seed.kc.getD n 0 := by
        simp only [gInput, show (2 * n + 1) / 2 = n by omega_using [], show (2 * n + 1) % 2 = 1 by omega_using []]
        rfl
      by_cases hi0 : i = 2 * n
      · subst hi0
        rw [l0, g0, gIn0, inv.x3, inv.x4, kx, ky, hi_append, hi_append, kcs_eq n (by omega_using [hn])]
      by_cases hi1 : i = 2 * n + 1
      · subst hi1
        rw [l1, g1, gIn1, inv.x3, inv.x4, kx, ky, BitVec.setWidth_append_eq_right,
          BitVec.setWidth_append_eq_right, kcs_eq n (by omega_using [hn])]
      · rw [lk _ (gSlot_mem i) _ (Nat.mod_lt _ (by decide)) (gIn_apart _ (by omega_using [hn, hi]) _ (by omega_using [hn]) hi0)
          (gIn_apart _ (by omega_using [hn, hi]) _ (by omega_using [hn]) hi1)]
        exact inv.lanes i (by omega_using [hi, hi0, hi1])
    · rw [regs' r a b c d e, inv.regs r a b c d e]
    · have : arraysR s = arraysR s₀ := by simp only [arraysR, r9]
      rw [this] at f'
      exact inv.frame.trans f'

end VG.Proof.Seed.AArch64

end

end


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
  simp [gSlot, show ¬ 16 + w < 16 by omega_arith]

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
    exact Offset.sub_base _ (by unfold scratchSlots; omega_arith))).symm

theorem keyPre_ok (key : Spec.Seed.Block) {s : State} (h : Room s)
    (h3 : s.gpr .x3 = kx (keyWords key 0)) (h4 : s.gpr .x4 = ky (keyWords key 0)) :
    ∃ s', runBlock isa keyPre s = some s' ∧ Room s' ∧
      (∀ w < 16, lv s' (tSlot 0) w = gInput key w) ∧ (∀ w < 16, lv s' uSlot w = gInput key (16 + w)) ∧
      s'.gpr .x3 = BitVec.ofNat 64 2 ∧ (∀ r ∈ [Reg.x5, .x1], s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [arraysR s] s.mem s'.mem := by
  obtain ⟨s1, e1, inv⟩ := keyRounds_ok key h h3 h4 16 (Nat.le_refl _)
  let s2 := s1.write .x .x3 (BitVec.ofNat 64 2)
  obtain e2 : runBlock isa [.movz .x .x3 2 0] s1 = some s2 := by
    rw [runBlock_cons, show exec (.movz .x .x3 2 0) s1 = some s2 by simp [exec, s2]; rfl, runStep_some, runBlock_nil]
  obtain g2 : ∀ r, r ≠ .x3 → s2.gpr r = s1.gpr r := fun r hr => gpr_write_of_ne _ _ _ hr
  obtain x5_1 : s1.gpr .x5 = s.gpr .x5 := inv.regs _ (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain x5_2 : s2.gpr .x5 = s.gpr .x5 := (g2 _ (by decide)).trans x5_1
  obtain lv2 : ∀ k b, lv s2 k b = lv s1 k b := fun k b => by
    simp only [lv, laneA, g2 _ (show Reg.x5 ≠ .x3 by decide)]; rfl
  refine ⟨s2, runBlock_trans e1 e2, room_congr h x5_2 inv.wr, fun w hw => ?_, fun w hw => ?_,
    by simp [s2, gpr_write], fun r hr => ?_, inv.rd, inv.wr, inv.frame⟩
  · rw [lv2, ← inv.lanes w (by omega_arith), gSlot_lo hw, Nat.mod_eq_of_lt hw]
  · rw [lv2, ← inv.lanes (16 + w) (by omega_arith), gSlot_hi hw, show (16 + w) % 16 = w by omega_arith]
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
  obtain scrS : ∀ t : State, t.gpr .x5 = s.gpr .x5 → scratchR t = scratchR s := fun t h => by simp only [scratchR, h]
  obtain workS : ∀ t : State, t.gpr .x5 = s.gpr .x5 → workR t = workR s := fun t h => by simp only [workR, h]
  obtain schedWork : (⟨S, 128⟩ : Region).Disjoint (workR s) :=
    hsep.sub_right (Region.sub_prefix (by unfold scratchSlots; omega_arith))
  -- `G` of the sixteen
  obtain ⟨t2, e2, g2, keep2, room2, rd2, wr2, -, regs2, f2⟩ := g16_lanes hi.room
  obtain x5_2 : t2.gpr .x5 = s.gpr .x5 := (regs2 _ (by decide)).trans hi.x5
  obtain x1_2 : t2.gpr .x1 = S + BitVec.ofNat 64 (64 * c) := (regs2 _ (by decide)).trans hi.x1
  obtain out2 : (outR t2 0).Disjoint (scratchR t2) := by
    rw [scrS t2 x5_2]; simp only [outR, x1_2, Nat.mul_zero]; rw [BitVec.add_zero]
    exact hsep.sub_left (Offset.sub_base _ (by omega_arith))
  -- the copy
  obtain ⟨t3, e3, v3, g3, rd3, wr3, f3⟩ := keyStore_ok 0 (by decide) room2
    (fun w hw => by
      rw [x1_2, wr2, hi.wr, Offset.add_add]
      exact ⟨_, hin, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩) out2 16 (Nat.le_refl _)
  obtain ⟨t4, e4, x1_4', x3_4', g4, m4, rd4, wr4⟩ := halfTail_ok t3
  obtain x5_4 : t4.gpr .x5 = s.gpr .x5 := by rw [g4 _ (by decide) (by decide), g3 _ (by decide), x5_2]
  obtain x3_4 : t4.gpr .x3 = BitVec.ofNat 64 (2 - (c + 1)) := by
    rw [x3_4', g3 _ (by decide), regs2 _ (by decide), hi.x3, Offset.ofNat_sub_ofNat (by omega_arith)]
    congr 1
  obtain x1_4 : t4.gpr .x1 = S + BitVec.ofNat 64 (64 * (c + 1)) := by
    rw [x1_4', g3 _ (by decide), x1_2, Offset.add_add, show 64 * c + 64 = 64 * (c + 1) by omega_arith]
  obtain ev4 : isa.eval (.nonzero .x .x3) t4 = some (decide (c = 0)) := by
    show some (t4.read .x .x3 != 0) = _
    rw [show t4.read .x .x3 = t4.gpr .x3 by simp [State.read], x3_4]
    congr 1
    have : 2 - (c + 1) < 2 ^ 64 := by omega_arith
    rcases (show c = 0 ∨ c = 1 by omega_arith) with rfl | rfl <;> decide
  -- the schedule's words so far
  obtain lvS : ∀ (t t' : State) (rs : List Region), Frame rs t.mem t'.mem →
      ∀ i, (∀ r ∈ rs, (⟨S + BitVec.ofNat 64 (4 * i), 4⟩ : Region).Disjoint r) →
      t'.mem.readW (S + BitVec.ofNat 64 (4 * i)) 32 = t.mem.readW (S + BitVec.ofNat 64 (4 * i)) 32 :=
    fun t t' rs hf i hd => hf.readW (Region.contains_self _ _) hd (by decide)
  obtain done4 : ∀ i < 16 * (c + 1), t4.mem.readW (S + BitVec.ofNat 64 (4 * i)) 32 = Spec.Seed.g (gInput key i) := by
    intro i hi'
    rw [m4]
    by_cases hlo : i < 16 * c
    · rw [lvS t2 t3 _ f3 i (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; simp only [outR, x1_2, Nat.mul_zero]
          rw [BitVec.add_zero]
          exact Offset.disjoint _ (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith)),
        lvS t t2 _ f2 i (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [workS t hi.x5]
          exact schedWork.sub_left (Offset.sub_base _ (by omega_arith))), hi.done i hlo]
    · obtain ⟨w, rfl⟩ : ∃ w, i = 16 * c + w := ⟨i - 16 * c, by omega_arith⟩
      have := v3 w (by omega_arith)
      rw [x1_2, Offset.add_add, show 64 * c + 4 * (0 + w) = 4 * (16 * c + w) by omega_arith] at this
      rw [this, g2 w (by omega_arith), hi.cur w (by omega_arith)]
  obtain frame4 : Frame [workR s, ⟨S, 128⟩] s.mem t4.mem := by
    rw [m4]
    refine (hi.frame.trans (f2.sub ?_)).trans (f3.sub ?_)
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact ⟨workR s, List.mem_cons_self, by rw [workS t hi.x5]; exact fun _ h => h⟩
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
      simp only [outR, x1_2, Nat.mul_zero]; rw [BitVec.add_zero]
      exact Offset.sub_base _ (by omega_arith)
  obtain room4 : Room t4 := room_congr hi.room (x5_4.trans hi.x5.symm) (by rw [wr4, wr3, wr2, hi.wr])
  refine WP.seq (WP.of_runBlock ⟨t4, runBlock_trans (runBlock_trans e2 e3) e4, ?_⟩)
  refine WP.ite (decide (c = 0)) ev4 (fun hb => ?_) (fun hb => ?_)
  · -- the second sixteen inputs
    obtain hc0 : c = 0 := by simpa using hb
    subst hc0
    obtain ⟨t5, e5, room5, v5, f5, rd5, wr5, g5⟩ := keyMove_ok room4
    refine WP.of_runBlock ⟨t5, e5, .inr ⟨?_, 1, by omega_arith, 1, by omega_arith, rfl, ?_⟩⟩
    · show some (t5.read .x .x3 != 0) = some true
      rw [show t5.read .x .x3 = t5.gpr .x3 by simp [State.read], g5 _ (by decide) (by decide), x3_4]
      decide
    obtain x5_5 : t5.gpr .x5 = s.gpr .x5 := (g5 _ (by decide) (by decide)).trans x5_4
    obtain workF : Frame [workR s] t4.mem t5.mem := by
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
        exact schedWork.sub_left (Offset.sub_base _ (by omega_arith)))]
      exact done4 i hi'
  · -- the end
    obtain hc1 : c = 1 := by simp at hb; omega_arith
    subst hc1
    refine WP.block_nil (.inl ⟨?_, hQ t4 done4 x5_4 (by rw [rd4, rd3, rd2, hi.rd])
      (by rw [wr4, wr3, wr2, hi.wr]) frame4⟩)
    show some (t4.read .x .x3 != 0) = some false
    rw [show t4.read .x .x3 = t4.gpr .x3 by simp [State.read], x3_4]
    decide

end VG.Proof.Seed.AArch64

end

end

/-! ### `Seed.AArch64.KeyLoad`, which only this module used -/

section

/-!
# Loading the key on AArch64

`keyLoad2_ok`: `keyLoad2 d k` puts the key's big-endian words `k` and
`k + 4` in `d = Key_k || Key_k+1`.
-/

@[expose] public section

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.AArch64.RegUpd VG.Impl.Seed.AArch64 VG.Impl.Aes.AArch64
  VG.Proof.Seed

theorem keyLoad2_ok {s : State} {d : Reg} (hd : d ≠ .x14) {k : Nat} (hk : k ≤ 8) (hk4 : k % 4 = 0)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 k) 4)
    (hr' : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (k + 4)) 4) :
    ∃ t, runBlock isa (keyLoad2 d k) s = some t ∧
      t.gpr d = Spec.Seed.wordAt (Spec.Seed.blockAt s.mem (s.gpr .x0)) k ++
        Spec.Seed.wordAt (Spec.Seed.blockAt s.mem (s.gpr .x0)) (k + 4) ∧
      (∀ r, r ≠ .x14 → r ≠ d → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp := by
  let W0 := s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 k) 32
  let W1 := s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 (k + 4)) 32
  obtain ⟨s1, e1, u1⟩ := step_w s (.ldr .w .x14 .x0 k) .x14 W0 (exec_ldr_w ⟨hk4, by omega_using [hk]⟩ hr)
  obtain ⟨s2, e2, u2⟩ := step_w s1 (.rev32 .x14 .x14) .x14 (rev32 (s1.read .w .x14)) rfl
  obtain ⟨s3, e3, u3⟩ := step_x s2 (.lsl .x .x14 .x14 32) .x14 (s2.read .x .x14 <<< 32)
    (by simp only [exec, show 32 < Size.x.bits by decide, ite_true])
  obtain x0₃ : s3.gpr .x0 = s.gpr .x0 := by rw [u3.other (by decide), u2.other (by decide), u1.other (by decide)]
  obtain m3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  obtain ⟨s4, e4, u4⟩ := step_w s3 (.ldr .w d .x0 (k + 4)) d W1
    (by rw [exec_ldr_w ⟨by omega_using [hk4], by omega_using [hk]⟩ (by rw [x0₃, u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact hr'), x0₃, m3])
  obtain ⟨s5, e5, u5⟩ := step_w s4 (.rev32 d d) d (rev32 (s4.read .w d)) rfl
  obtain ⟨s6, e6, u6⟩ := step_x s5 (orrR d d .x14) d (s5.gpr d ||| s5.gpr .x14)
    (by simp [orrR, exec, State.read])
  refine ⟨s6, ?_, ?_, fun r ha hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [keyLoad2, runBlock_cons, e1, runStep_some, runBlock_cons, e2, runStep_some, runBlock_cons, e3,
      runStep_some, runBlock_cons, e4, runStep_some, runBlock_cons, e5, runStep_some, runBlock_cons, e6,
      runStep_some, runBlock_nil]
  · rw [u6.self, u5.self, u5.other (Ne.symm hd), u4.other (Ne.symm hd), u3.self]
    simp only [State.read, Size.bits, BitVec.setWidth_eq]
    rw [u4.self, setWidth_setWidth_32, u2.self]
    simp only [State.read, Size.bits]
    rw [u1.self, setWidth_setWidth_32,
      wordAt_blockAt _ _ (by omega_using [hk]), wordAt_blockAt _ _ (by omega_using [hk]), BitVec.or_comm]
    have := BitVec.setWidth_append_eq_shiftLeft_setWidth_or (w'' := 64) (b := byteRev32 W0) (b' := byteRev32 W1)
    rw [BitVec.setWidth_eq] at this
    rw [this]
    rfl
  · rw [u6.other hr, u5.other hr, u4.other hr, u3.other ha, u2.other ha, u1.other ha]
  · rw [u6.mem, u5.mem, u4.mem, m3]
  · rw [u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]
  · rw [u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]
  · rw [u6.sp, u5.sp, u4.sp, u3.sp, u2.sp, u1.sp]

end VG.Proof.Seed.AArch64

end

end


/-!
# Key expansion on AArch64

`expandKey_ok`: after saving the callee-saved registers, `expandKey` loads
the key, computes the schedule (`keyBody_ok`) and restores the registers.
-/

@[expose] public section

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.AArch64.RegUpd VG.Impl.Seed.AArch64 VG.Impl.Aes.AArch64
  VG.Proof.Seed

/-- What key expansion needs: the scratch buffer and the schedule writable,
the key readable, apart from each other. -/
structure KeyPre (s : State) : Prop where
  scratch : (⟨s.gpr .x2, 8 * scratchSlots⟩ : Region) ∈ s.wr
  schedIn : (⟨s.gpr .x1, 128⟩ : Region) ∈ s.wr
  keyIn : (⟨s.gpr .x0, 16⟩ : Region) ∈ s.rd
  keySched : (⟨s.gpr .x0, 16⟩ : Region).Disjoint ⟨s.gpr .x1, 128⟩
  keyBuf : (⟨s.gpr .x0, 16⟩ : Region).Disjoint ⟨s.gpr .x2, 8 * scratchSlots⟩
  schedBuf : (⟨s.gpr .x1, 128⟩ : Region).Disjoint ⟨s.gpr .x2, 8 * scratchSlots⟩

structure KeyPost (s s' : State) : Prop where
  saved : ∀ p ∈ Impl.Seed.AArch64.savedRegs, s'.gpr p.1 = s.gpr p.1
  sched : Spec.Seed.scheduleAt s'.mem (s.gpr .x1) = Spec.Seed.expandKey (Spec.Seed.blockAt s.mem (s.gpr .x0))
  frame : Frame [⟨s.gpr .x2, 8 * scratchSlots⟩, ⟨s.gpr .x1, 128⟩] s.mem s'.mem

theorem expandKey_eq_code : expandKey = .seq (.block (([movR .x5 .x2] ++
    (Impl.Seed.AArch64.savedRegs.map fun p => (p.2, p.1)).map (fun p => stS p.1 p.2)) ++
    (keyLoad2 .x3 0 ++ keyLoad2 .x4 8) ++ keyPre)) (.seq (.loop keyHalf (.nonzero .x .x3)) (.block restore)) := by
  simp only [expandKey, keyPre, Impl.Seed.AArch64.keyLoad, List.append_assoc]
  rfl

theorem expandKey_ok {s : State} (h : KeyPre s) : WP isa expandKey s (KeyPost s) := by
  let key := Spec.Seed.blockAt s.mem (s.gpr .x0)
  rw [expandKey_eq_code]
  -- `x5 := x2`
  let s₁ := s.write .x .x5 (s.gpr .x2)
  obtain e₁ : runBlock isa [movR .x5 .x2] s = some s₁ := by
    rw [runBlock_cons, exec_movR, runStep_some, runBlock_nil]
  obtain r9₁ : s₁.gpr .x5 = s.gpr .x2 := by simp [s₁, gpr_write]
  obtain g₁ : ∀ r, r ≠ .x5 → s₁.gpr r = s.gpr r := fun r hr => gpr_write_of_ne _ _ _ hr
  obtain scr₁ : scratchR s₁ = ⟨s.gpr .x2, 8 * scratchSlots⟩ := by simp only [scratchR, r9₁]
  obtain room₁ : Room s₁ := .of_mem (by rw [scr₁]; exact h.scratch)
  -- the saved registers
  obtain ⟨s₂, e₂, g₂, rd₂, wr₂, -, f₂, set₂, -⟩ := stores_ok room₁
    (Impl.Seed.AArch64.savedRegs.map fun p => (p.2, p.1)) (by decide) (by decide)
  obtain G₂ : ∀ r, r ≠ .x5 → s₂.gpr r = s.gpr r := fun r a => by rw [g₂, g₁ r a]
  obtain r9₂ : s₂.gpr .x5 = s.gpr .x2 := by rw [g₂, r9₁]
  obtain f₂' : Frame [⟨s.gpr .x2, 8 * scratchSlots⟩] s.mem s₂.mem := by rw [← scr₁]; exact f₂
  obtain rd₂' : s₂.rd = s.rd := by rw [rd₂]; rfl
  obtain wr₂' : s₂.wr = s.wr := by rw [wr₂]; rfl
  -- the key
  obtain x0₂ : s₂.gpr .x0 = s.gpr .x0 := G₂ _ (by decide)
  obtain hkey : ∀ k, k + 4 ≤ 16 → InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .x0 + BitVec.ofNat 64 k) 4 := fun k hk => by
    rw [rd₂', wr₂', x0₂]
    exact ⟨_, List.mem_append_left _ h.keyIn, Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])⟩
  obtain ⟨s₃, e₃, v₃, g₃, m₃, rd₃, wr₃, -⟩ := keyLoad2_ok (s := s₂) (d := .x3) (by decide) (k := 0) (by decide)
    (by decide) (hkey 0 (by decide)) (hkey 4 (by decide))
  obtain x0₃ : s₃.gpr .x0 = s.gpr .x0 := by rw [g₃ _ (by decide) (by decide), x0₂]
  obtain ⟨s₄, e₄, v₄, g₄, m₄, rd₄, wr₄, -⟩ := keyLoad2_ok (s := s₃) (d := .x4) (by decide) (k := 8) (by decide)
    (by decide)
    (by rw [rd₃, wr₃, x0₃, ← x0₂]; exact hkey 8 (by decide))
    (by rw [rd₃, wr₃, x0₃, ← x0₂]; exact hkey 12 (by decide))
  obtain key₂ : Spec.Seed.blockAt s₂.mem (s.gpr .x0) = key := blockAt_frame f₂' fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.keyBuf
  obtain G₄ : ∀ r, r ≠ .x14 → r ≠ .x3 → r ≠ .x4 → s₄.gpr r = s₂.gpr r := fun r a b c => by
    rw [g₄ r a c, g₃ r a b]
  obtain h3 : s₄.gpr .x3 = kx (keyWords key 0) := by
    rw [g₄ _ (by decide) (by decide), v₃, x0₂, key₂]; rfl
  obtain h4 : s₄.gpr .x4 = ky (keyWords key 0) := by
    rw [v₄, x0₃, m₃, key₂]; rfl
  obtain r9₄ : s₄.gpr .x5 = s.gpr .x2 := by rw [G₄ _ (by decide) (by decide) (by decide), r9₂]
  obtain rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂']
  obtain wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂']
  obtain mem₄ : s₄.mem = s₂.mem := by rw [m₄, m₃]
  obtain scr₄ : scratchR s₄ = ⟨s.gpr .x2, 8 * scratchSlots⟩ := by simp only [scratchR, r9₄]
  obtain room₄ : Room s₄ := .of_mem (by rw [scr₄, wr₄']; exact h.scratch)
  obtain x1₄ : s₄.gpr .x1 = s.gpr .x1 := by rw [G₄ _ (by decide) (by decide) (by decide), G₂ _ (by decide)]
  -- the rounds, and the count of halves
  obtain ⟨s₅, e₅, room₅, cur₅, next₅, x3₅, g₅, rd₅, wr₅, f₅⟩ := keyPre_ok key room₄ h3 h4
  obtain r9₅ : s₅.gpr .x5 = s₄.gpr .x5 := g₅ _ (by simp)
  obtain x1₅ : s₅.gpr .x1 = s.gpr .x1 := (g₅ _ (by simp)).trans x1₄
  obtain scr₅ : scratchR s₅ = ⟨s.gpr .x2, 8 * scratchSlots⟩ := by simp only [scratchR, r9₅, r9₄]
  obtain h0 : HalfInv key s₅ (s.gpr .x1) 0 s₅ :=
    ⟨room₅, rfl, by rw [x1₅]; exact (BitVec.add_zero _).symm, x3₅,
      fun w hw => by rw [cur₅ w hw, Nat.mul_zero, Nat.zero_add], fun _ => next₅, fun i hi => by omega, rfl, rfl,
      Frame.refl _ _⟩
  refine WP.seq (WP.of_runBlock ⟨s₅, runBlock_trans (runBlock_trans (runBlock_trans e₁ e₂)
    (runBlock_trans e₃ e₄)) e₅, WP.seq (keyHalves_wp key
      (by rw [wr₅, wr₄']; exact h.schedIn) (by rw [scr₅]; exact h.schedBuf) h0
      fun s₆ v₆ r9₆ rd₆ wr₆ f₆ => ?_)⟩)
  obtain room₆ : Room s₆ := room_congr room₅ r9₆ wr₆
  obtain ⟨s', e', m', -, set', -⟩ := loads_ok room₆ Impl.Seed.AArch64.savedRegs
    (fun q hq => ⟨(savedRegs_ok q hq).1, (savedRegs_ok q hq).2.1⟩) (by decide)
  refine WP.of_runBlock ⟨s', by rw [restore_eq]; exact e', ?_⟩
  obtain workR₅ : workR s₅ = ⟨s.gpr .x2, 8 * 112⟩ := by simp only [workR, r9₅, r9₄]
  rw [workR₅] at f₆
  obtain arr₄ : Region.Sub (arraysR s₄) ⟨s.gpr .x2, 8 * 112⟩ := by
    have := arraysR_sub_work s₄; simp only [workR, r9₄] at this; exact this
  obtain f₄₆ : Frame [⟨s.gpr .x2, 8 * 112⟩, ⟨s.gpr .x1, 128⟩] s₄.mem s₆.mem :=
    (f₅.sub fun r hr => ⟨_, List.mem_cons_self, by simp at hr; subst hr; exact arr₄⟩).trans f₆
  obtain frame : Frame [⟨s.gpr .x2, 8 * scratchSlots⟩, ⟨s.gpr .x1, 128⟩] s.mem s'.mem := by
    rw [m']
    refine (f₂'.mono (by simp)).trans ?_
    rw [← mem₄]
    refine f₄₆.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by unfold scratchSlots; omega_using [])⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  refine ⟨fun q hq => ?_, ?_, frame⟩
  · have hq' := savedRegs_ok q hq
    rw [set' q hq]
    obtain e6 : slotW s₆ q.2 = slotW s₄ q.2 := by
      show s₆.mem.readW (Straight.wordAddr (s₆.gpr .x5) q.2) 64 =
        s₄.mem.readW (Straight.wordAddr (s₄.gpr .x5) q.2) 64
      rw [r9₆, r9₅, r9₄]
      refine f₄₆.readW (r := ⟨Straight.wordAddr (s.gpr .x2) q.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint_base _ (by omega) (by unfold scratchSlots at hq'; omega)
      · exact (h.schedBuf.sub_right (Offset.sub_base _ (by unfold scratchSlots at hq' ⊢; omega))).symm
    obtain e4 : slotW s₄ q.2 = slotW s₂ q.2 := by
      show s₄.mem.readW (Straight.wordAddr (s₄.gpr .x5) q.2) 64 =
        s₂.mem.readW (Straight.wordAddr (s₂.gpr .x5) q.2) 64
      rw [mem₄, r9₄, r9₂]
    rw [e6, e4, set₂ (q.2, q.1) (List.mem_map_of_mem hq), g₁ _ hq'.2.1]
  · rw [Proof.Seed.expandKey_eq]
    apply Vector.ext
    intro i hi
    rw [scheduleAt_readW _ _ i hi, m', v₆ i hi, Vector.getElem_ofFn]

end VG.Proof.Seed.AArch64

end

end


/-! # Key expansion meets its contract, with the scratch buffer as an argument -/

@[expose] public section

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64

def keyContract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, 16⟩
    let sched : Region := ⟨s.gpr .x1, 128⟩
    let buf : Region := ⟨s.gpr .x2, 976⟩
    s.rd = [key] ∧ s.wr = [sched, buf] ∧ key.Disjoint sched ∧ key.Disjoint buf ∧ sched.Disjoint buf
  post s s' :=
    Spec.Seed.scheduleAt s'.mem (s.gpr .x1) = Spec.Seed.expandKey (Spec.Seed.blockAt s.mem (s.gpr .x0))
  pub := PublicRegs [.x0, .x1, .x2]

def keySatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 976⟩]

theorem expandKey_wp (s : State) (hs : keyContract.pre s) :
    WP isa Impl.Seed.AArch64.expandKey s fun s' =>
      (∀ p ∈ Impl.Seed.AArch64.savedRegs, s'.gpr p.1 = s.gpr p.1) ∧ keyContract.post s s' := by
  obtain ⟨rd, wr, ks, kb, sb⟩ := hs
  refine WP.mono (expandKey_ok (s := s)
    { scratch := by rw [wr]; exact List.mem_cons_of_mem _ List.mem_cons_self
      schedIn := by rw [wr]; exact List.mem_cons_self
      keyIn := by rw [rd]; exact List.mem_cons_self
      keySched := ks
      keyBuf := kb
      schedBuf := sb }) fun _ hp => ⟨hp.saved, hp.sched⟩

theorem expandKey_correct (s : State) (hs : keyContract.pre s) :
    ∃ t s', Exec isa Impl.Seed.AArch64.expandKey s t s' ∧ abiPreserved s s' ∧ keyContract.post s s' := by
  obtain ⟨t, s', he, ⟨hsv, hp⟩, h30⟩ := WP.gprs (c := Impl.Seed.AArch64.expandKey) (expandKey_wp s hs)
    (rs := [.x30]) (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, abi_of he hsv (h30 _ (by simp)) (by lit_decide), hp⟩

theorem publicRegs_three (s₁ s₂ : State) : PublicRegs [.x0, .x1, .x2] s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 := by
  simp [PublicRegs]

theorem expandKey_verified : Verified target Impl.Seed.AArch64.expandKey
    (Proof.Seed.expandKeyScratchContract abi 122) := by
  refine Verified.of_correct expandKey_correct (expandKey_constantTime _) ?_
  sig_implies [Proof.Seed.expandKeyScratchContract, Proof.Seed.expandKeyScratchSig, Proof.Seed.expandKeyPost,
    abi, argRegs, keyContract, publicRegs_three] [keySatState] using keySatState

end VG.Proof.Seed.AArch64

end

end


/-!
# SEED on AArch64, with its working space on the stack

Key expansion runs its code, proved with the working space as an argument,
in a frame that allocates it and zeroes it after the code
(`Verified.stackScratchWiped`), since it holds the key and the round keys:
the 976 bytes of the working space. The code uses no other stack. ECB does
the same around calls of the blocks functions (`EcbCall.lean`).
-/

@[expose] public section

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64

theorem expandKey_framed :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratchWiped 976 .x2 122 Impl.Seed.AArch64.expandKey)
      (Spec.Seed.expandKeyContract AArch64.abi 976) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Seed.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 122) (post := Proof.Seed.expandKeyPost AArch64.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 976) expandKey_verified (by decide) (by decide) (by decide)
    (Proof.Seed.expandKeyPostOut_local _)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Seed.AArch64
