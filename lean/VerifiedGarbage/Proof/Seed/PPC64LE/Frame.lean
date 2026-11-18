module

public import VerifiedGarbage.Spec.Seed.Contract
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Impl.Seed.PPC64LE.ExpandKey
public import VerifiedGarbage.Impl.Seed.PPC64LE.Modes
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Seed.Scratch
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Seed.PPC64LE.Verified
import VerifiedGarbage.Proof.Seed.ModeBytes
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Seed.PPC64LE.Lit
meta import VerifiedGarbage.Impl.Seed.PPC64LE.Modes
meta import VerifiedGarbage.Proof.Seed.Scratch
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Seed.PPC64LE.Verified
meta import VerifiedGarbage.Proof.Seed.ModeBytes
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Call
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Seed.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.RegSet
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Impl.Seed.PPC64LE.ExpandKey
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Proof.Seed.PPC64LE.Steps
import VerifiedGarbage.Proof.Seed.PPC64LE.Ecb
public import VerifiedGarbage.Proof.Seed.KeySchedule
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Seed.Memory
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Seed.SboxLit
import VerifiedGarbage.Proof.Framework.PPC64LE.Straight
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Seed
meta import VerifiedGarbage.Proof.Seed.PPC64LE.Steps
meta import VerifiedGarbage.Proof.Seed.PPC64LE.Ecb
meta import VerifiedGarbage.Proof.Seed.KeySchedule
meta import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Seed.Memory
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Seed.SboxLit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Straight
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Spec.Seed

/-! ### `Seed.PPC64LE.KeyVerified`, which only this module used -/

section

/-! ### `Seed.PPC64LE.Key`, which only this module used -/

section

/-! ### `Seed.PPC64LE.KeyRound`, which only this module used -/

section

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
    gIn_apart _ (by omega_using [hj]) _ (by omega_using [hj]) (by omega_using [])
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

end

end

/-! ### `Seed.PPC64LE.KeyBody`, which only this module used -/

section

/-! ### `Seed.PPC64LE.KeyStore`, which only this module used -/

section

/-!
# Copying `G`'s outputs on PPC64LE

`keyStore_ok`: `keyStore k` copies the sixteen lanes of `G`'s words to the
schedule's words from `k`; `keyMove_ok`: `keyMove` copies the second sixteen
inputs of `G` to its words.
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.PPC64LE.RegUpd VG.Impl.Seed.PPC64LE VG.Proof.Seed

/-- The schedule's words from `k`. -/
def outR (s : State) (k : Nat) : Region := ⟨s.gpr .r4 + BitVec.ofNat 64 (4 * k), 64⟩

theorem keyStore_ok (k : Nat) (hk : k ≤ 16) {s : State} (h : Room s)
    (hw : ∀ w < 16, InRegions s.wr (s.gpr .r4 + BitVec.ofNat 64 (4 * (k + w))) 4)
    (hsep : (outR s k).Disjoint (scratchR s)) :
    ∀ n ≤ 16, ∃ t, runBlock isa ((List.range n).flatMap fun w =>
        [ldW .r9 (tSlot 0) w, .store .w .r9 .r4 (4 * (k + w))]) s = some t ∧
      (∀ w < n, t.mem.readW (s.gpr .r4 + BitVec.ofNat 64 (4 * (k + w))) 32 = lv s (tSlot 0) w) ∧
      (∀ r, r ≠ .r9 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [outR s k] s.mem t.mem
  | 0, _ => ⟨s, runBlock_nil, fun w hw => by omega, fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
  | n + 1, hn => by
    obtain ⟨t, ht, hv, hg, hrd, hwr, hf⟩ := keyStore_ok k hk h hw hsep n (by omega_using [hn])
    obtain r8 : t.gpr .r8 = s.gpr .r8 := hg _ (by decide)
    obtain r4 : t.gpr .r4 = s.gpr .r4 := hg _ (by decide)
    obtain room : Room t := room_congr h r8 hwr
    obtain hlane : lv t (tSlot 0) n = lv s (tSlot 0) n := by
      simp only [lv, laneA, r8]
      refine hf.readW (r := ⟨s.gpr .r8 + BitVec.ofNat 64 (8 * tSlot 0 + 4 * n), 4⟩) (Region.contains_self _ _) ?_
        (by decide)
      intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      refine (hsep.sub_right ?_).symm
      show Region.Sub ⟨s.gpr .r8 + BitVec.ofNat 64 (8 * tSlot 0 + 4 * n), 4⟩ ⟨s.gpr .r8, 8 * scratchSlots⟩
      exact Offset.sub_base _ (by unfold scratchSlots tSlot; omega_using [hn])
    let t1 := t.write .r9 ((lv t (tSlot 0) n).setWidth 64)
    obtain e1 : exec (ldW .r9 (tSlot 0) n) t = some t1 := exec_ldW_lane room mem_tA (by omega_using [hn]) .r9
    obtain hw1 : InRegions t1.wr (t1.gpr .r4 + BitVec.ofNat 64 (4 * (k + n))) 4 := by
      simp only [t1, wr_write, gpr_write_of_ne _ _ (show ¬ Reg.r4 = .r9 by decide), hwr, r4]
      exact hw n (by omega_using [hn])
    let t2 := setMem t1 (t.mem.writeW (s.gpr .r4 + BitVec.ofNat 64 (4 * (k + n))) (lv s (tSlot 0) n))
    obtain e2 : exec (.store .w .r9 .r4 (4 * (k + n))) t1 = some t2 := by
      rw [exec_store_w (show Reg.r4 ≠ .r0 by decide) (by omega_using [hk, hn]) hw1]
      simp only [t1, t2, gpr_write_self, gpr_write_of_ne _ _ (show ¬ Reg.r4 = .r9 by decide), r4,
        mem_write, setWidth_setWidth_32, hlane]
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
    · simp only [t2, gpr_setMem, t1, gpr_write_of_ne _ _ hr]; exact hg r hr
    · simp only [t2, mem_setMem]
      exact hf.writeW List.mem_cons_self _ (Offset.contains _ (by omega_using []) (by omega_using [hn]) (by omega_using [hk]))

/-- Moving lane `b` of `uSlot` to `G`'s words. -/
def spMove : LaneSpec := [(tSlot 0, fun x => x uSlot)]

theorem keyMove_ok {s : State} (h : Room s) :
    ∃ s', runBlock isa keyMove s = some s' ∧ Room s' ∧
      (∀ k ∈ arrays, ∀ b < 16, lv s' k b = newVal spMove k (fun k' => lv s k' b)) ∧
      Frame [arraysR s] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) := by
  refine lanes16_room (f := fun w => [ldW .r9 uSlot w, stW (tSlot 0) w .r9])
    (by decide) ?_ (fun b hb s h => ?_) h
  · intro kv hkv x y hxy
    simp only [spMove, List.mem_singleton] at hkv; subst hkv
    exact hxy uSlot (by decide)
  · rw [runBlock_cons, exec_ldW_lane h (by decide) hb, runStep_some, runBlock_cons,
      exec_stW_lane ?h1 (by decide) hb, runStep_some, runBlock_nil]
    case h1 => exact room_congr h rfl rfl
    refine ⟨_, rfl, ?_, rfl, rfl, fun r h1 h2 => ?_⟩
    · simp only [laneWrites, spMove, List.foldl_cons, List.foldl_nil, gpr_write_self,
        setWidth_setWidth_32, mem_setMem, mem_write,
        laneA_write _ _ (show ¬ Reg.r8 = .r9 by decide)]
    · simp only [gpr_write_of_ne _ _ h1, gpr_setMem]

end VG.Proof.Seed.PPC64LE

end

end

/-! ### `Seed.PPC64LE.KeyRounds`, which only this module used -/

section

/-!
# The sixteen rounds of the key schedule on PPC64LE

`keyRounds_ok`: after `n` rounds, `r6` and `r7` hold the key words of
round `n + 1` (`keyWords`), and the lanes of `G`'s first `2 * n` inputs hold
them (`gInput`).
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Impl.Seed.PPC64LE VG.Proof.Seed

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

/-- The key words `k` as `r6` and `r7` hold them. -/
def kx (k : Quad) : BitVec 64 := k.1 ++ k.2.1
def ky (k : Quad) : BitVec 64 := k.2.2.1 ++ k.2.2.2

/-- After `n` rounds of the key schedule. -/
structure KeyInv (key : Spec.Seed.Block) (s₀ : State) (n : Nat) (s : State) : Prop where
  r6 : s.gpr .r6 = kx (keyWords key n)
  r7 : s.gpr .r7 = ky (keyWords key n)
  lanes : ∀ i < 2 * n, lv s (gSlot i) (i % 16) = gInput key i
  regs : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r6 → r ≠ .r7 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [arraysR s₀] s₀.mem s.mem

theorem keyRounds_ok (key : Spec.Seed.Block) {s₀ : State} (h : Room s₀)
    (h10 : s₀.gpr .r6 = kx (keyWords key 0)) (h11 : s₀.gpr .r7 = ky (keyWords key 0)) :
    ∀ n ≤ 16, ∃ s, runBlock isa ((List.range n).flatMap keyRound) s₀ = some s ∧ KeyInv key s₀ n s
  | 0, _ => ⟨s₀, runBlock_nil, h10, h11, fun i hi => by omega, fun _ _ _ _ _ _ => rfl, rfl, rfl, rfl,
      Frame.refl _ _⟩
  | n + 1, hn => by
    obtain ⟨s, hs, inv⟩ := keyRounds_ok key h h10 h11 n (by omega_using [hn])
    obtain r9 : s.gpr .r8 = s₀.gpr .r8 := inv.regs _ (by decide) (by decide) (by decide) (by decide) (by decide)
    obtain ⟨s', hs', l0, l1, lk, r6', r7', regs', rd', wr', sp', f'⟩ :=
      keyRound_ok (j := n) (by omega_using [hn]) (room_congr h r9 inv.wr)
    refine ⟨s', ?_, ⟨?_, ?_, fun i hi => ?_, fun r a b c d e => ?_, by rw [sp', inv.sp], by rw [rd', inv.rd],
      by rw [wr', inv.wr], ?_⟩⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      exact runBlock_trans hs hs'
    · rw [r6', inv.r6]
      simp only [keyWords, keyStep]
      split
      · simp only [kx]; exact (split64 _).symm
      · rfl
    · rw [r7', inv.r7]
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
        rw [l0, g0, gIn0, inv.r6, inv.r7, kx, ky, hi_append, hi_append, kcs_eq n (by omega_using [hn])]
      by_cases hi1 : i = 2 * n + 1
      · subst hi1
        rw [l1, g1, gIn1, inv.r6, inv.r7, kx, ky, BitVec.setWidth_append_eq_right,
          BitVec.setWidth_append_eq_right, kcs_eq n (by omega_using [hn])]
      · rw [lk _ (gSlot_mem i) _ (Nat.mod_lt _ (by decide)) (gIn_apart _ (by omega_using [hn, hi]) _ (by omega_using [hn]) hi0)
          (gIn_apart _ (by omega_using [hn, hi]) _ (by omega_using [hn]) hi1)]
        exact inv.lanes i (by omega_using [hi, hi0, hi1])
    · rw [regs' r a b c d e, inv.regs r a b c d e]
    · have : arraysR s = arraysR s₀ := by simp only [arraysR, r9]
      rw [this] at f'
      exact inv.frame.trans f'

end VG.Proof.Seed.PPC64LE

end

end


/-!
# The key schedule's computation on PPC64LE

`keyBody_ok`: from `r6 = Key0 || Key1` and `r7 = Key2 || Key3`, the rounds,
the two `g16`s and the copies write `G` of the 32 inputs (`gInput`) to the
schedule.
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.PPC64LE.RegUpd VG.Impl.Seed.PPC64LE VG.Proof.Seed

/-- The rounds and the count of halves, between loading the key and the loop. -/
def keyPre : List Instr := (List.range 16).flatMap keyRound ++ [.li .r6 2]

theorem gSlot_lo {i : Nat} (hi : i < 16) : gSlot i = tSlot 0 := by simp [gSlot, hi]
theorem gSlot_hi {w : Nat} (hw : w < 16) : gSlot (16 + w) = uSlot := by
  simp [gSlot, show ¬ 16 + w < 16 by omega]

/-- A lane after a frame over regions apart from the scratch buffer. -/
theorem lv_frame {s s' : State} {R : Region} (hx5 : s'.gpr .r8 = s.gpr .r8) (hf : Frame [R] s.mem s'.mem)
    (hd : R.Disjoint (scratchR s)) {k b : Nat} (hk : k ∈ arrays) (hb : b < 16) : lv s' k b = lv s k b := by
  simp only [lv, laneA, hx5]
  refine hf.readW (r := ⟨s.gpr .r8 + BitVec.ofNat 64 (8 * k + 4 * b), 4⟩) (Region.contains_self _ _) ?_
    (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact (hd.sub_right (lane_in hk hb s |> fun _ => by
    have := arrays_bound k hk
    exact Offset.sub_base _ (by unfold scratchSlots; omega_using [hb, this]))).symm

theorem keyPre_ok (key : Spec.Seed.Block) {s : State} (h : Room s)
    (h3 : s.gpr .r6 = kx (keyWords key 0)) (h4 : s.gpr .r7 = ky (keyWords key 0)) :
    ∃ s', runBlock isa keyPre s = some s' ∧ Room s' ∧
      (∀ w < 16, lv s' (tSlot 0) w = gInput key w) ∧ (∀ w < 16, lv s' uSlot w = gInput key (16 + w)) ∧
      s'.gpr .r6 = BitVec.ofNat 64 2 ∧ (∀ r ∈ [Reg.r8, .r4], s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [arraysR s] s.mem s'.mem := by
  obtain ⟨s1, e1, inv⟩ := keyRounds_ok key h h3 h4 16 (Nat.le_refl _)
  let s2 := s1.write .r6 (BitVec.ofNat 64 2)
  obtain e2 : runBlock isa [.li .r6 2] s1 = some s2 := by
    rw [runBlock_cons, exec_li (by decide), runStep_some, runBlock_nil]
  obtain g2 : ∀ r, r ≠ .r6 → s2.gpr r = s1.gpr r := fun r hr => gpr_write_of_ne _ _ hr
  obtain r8_1 : s1.gpr .r8 = s.gpr .r8 := inv.regs _ (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain r8_2 : s2.gpr .r8 = s.gpr .r8 := (g2 _ (by decide)).trans r8_1
  obtain lv2 : ∀ k b, lv s2 k b = lv s1 k b := fun k b => by
    simp only [lv, laneA, g2 _ (show Reg.r8 ≠ .r6 by decide)]; rfl
  refine ⟨s2, runBlock_trans e1 e2, room_congr h r8_2 inv.wr, fun w hw => ?_, fun w hw => ?_,
    by simp [s2, gpr_write], fun r hr => ?_, inv.rd, inv.wr, inv.frame⟩
  · rw [lv2, ← inv.lanes w (by omega_using [hw]), gSlot_lo hw, Nat.mod_eq_of_lt hw]
  · rw [lv2, ← inv.lanes (16 + w) (by omega_using [hw]), gSlot_hi hw, show (16 + w) % 16 = w by omega_using [hw]]
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl <;>
      rw [g2 _ (by decide), inv.regs _ (by decide) (by decide) (by decide) (by decide) (by decide)]

/-- `add r4, r4, 64; sub r6, r6, 1`. -/
theorem halfTail_ok (t : State) :
    ∃ t', runBlock isa [.addi .r4 .r4 64, .subi .r6 .r6 1] t = some t' ∧
      t'.gpr .r4 = t.gpr .r4 + BitVec.ofNat 64 64 ∧ t'.gpr .r6 = t.gpr .r6 - BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .r4 → r ≠ .r6 → t'.gpr r = t.gpr r) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine ⟨_, by
    rw [runBlock_cons, exec_addi' (by decide), runStep_some, runBlock_cons, exec_subi' (by decide),
      runStep_some, runBlock_nil], ?_⟩
  refine ⟨by simp [gpr_write], by simp [gpr_write], fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  simp [gpr_write, h1, h2]

/-- After `c` of the two halves: `r4` at the schedule's word `16 c`, `r6` the
halves left, `G`'s words holding the next sixteen inputs, the schedule's
words before `16 c` done. -/
structure HalfInv (key : Spec.Seed.Block) (s : State) (S : Addr) (c : Nat) (t : State) : Prop where
  room : Room t
  r8 : t.gpr .r8 = s.gpr .r8
  r4 : t.gpr .r4 = S + BitVec.ofNat 64 (64 * c)
  r6 : t.gpr .r6 = BitVec.ofNat 64 (2 - c)
  cur : ∀ w < 16, lv t (tSlot 0) w = gInput key (16 * c + w)
  next : c = 0 → ∀ w < 16, lv t uSlot w = gInput key (16 + w)
  done : ∀ i < 16 * c, t.mem.readW (S + BitVec.ofNat 64 (4 * i)) 32 = Spec.Seed.g (gInput key i)
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [workR s, ⟨S, 128⟩] s.mem t.mem

theorem keyHalves_wp (key : Spec.Seed.Block) {s : State} {S : Addr} (hin : (⟨S, 128⟩ : Region) ∈ s.wr)
    (hsep : (⟨S, 128⟩ : Region).Disjoint (scratchR s)) (h0 : HalfInv key s S 0 s) {Q : State → Prop}
    (hQ : ∀ t, (∀ i < 32, t.mem.readW (S + BitVec.ofNat 64 (4 * i)) 32 = Spec.Seed.g (gInput key i)) →
      t.gpr .r8 = s.gpr .r8 → t.rd = s.rd → t.wr = s.wr → Frame [workR s, ⟨S, 128⟩] s.mem t.mem → Q t) :
    WP isa (.loop keyHalf (.nonzero .d .r6)) s Q := by
  refine WP.loop (M := isa) (fun n t => ∃ c, c < 2 ∧ n = 2 - c ∧ HalfInv key s S c t) (fun n t ht => ?_) 2 s
    ⟨0, by decide, rfl, h0⟩
  obtain ⟨c, hc, rfl, hi⟩ := ht
  obtain scrS : ∀ t : State, t.gpr .r8 = s.gpr .r8 → scratchR t = scratchR s := fun t h => by simp only [scratchR, h]
  obtain workS : ∀ t : State, t.gpr .r8 = s.gpr .r8 → workR t = workR s := fun t h => by simp only [workR, h]
  obtain schedWork : (⟨S, 128⟩ : Region).Disjoint (workR s) :=
    hsep.sub_right (Region.sub_prefix (by unfold scratchSlots; omega_using []))
  -- `G` of the sixteen
  obtain ⟨t2, e2, g2, keep2, room2, rd2, wr2, -, regs2, f2⟩ := g16_lanes hi.room
  obtain r8_2 : t2.gpr .r8 = s.gpr .r8 := (regs2 _ (by decide)).trans hi.r8
  obtain r4_2 : t2.gpr .r4 = S + BitVec.ofNat 64 (64 * c) := (regs2 _ (by decide)).trans hi.r4
  obtain out2 : (outR t2 0).Disjoint (scratchR t2) := by
    rw [scrS t2 r8_2]; simp only [outR, r4_2, Nat.mul_zero]; rw [BitVec.add_zero]
    exact hsep.sub_left (Offset.sub_base _ (by omega_using [hc]))
  -- the copy
  obtain ⟨t3, e3, v3, g3, rd3, wr3, f3⟩ := keyStore_ok 0 (by decide) room2
    (fun w hw => by
      rw [r4_2, wr2, hi.wr, Offset.add_add]
      exact ⟨_, hin, Offset.contains_base _ (by omega_using [hc, hw]) (by omega_using [hc, hw])⟩) out2 16 (Nat.le_refl _)
  obtain ⟨t4, e4, r4_4', r6_4', g4, m4, rd4, wr4⟩ := halfTail_ok t3
  obtain r8_4 : t4.gpr .r8 = s.gpr .r8 := by rw [g4 _ (by decide) (by decide), g3 _ (by decide), r8_2]
  obtain r6_4 : t4.gpr .r6 = BitVec.ofNat 64 (2 - (c + 1)) := by
    rw [r6_4', g3 _ (by decide), regs2 _ (by decide), hi.r6, Offset.ofNat_sub_ofNat (by omega_using [hc])]
    congr 1
  obtain r4_4 : t4.gpr .r4 = S + BitVec.ofNat 64 (64 * (c + 1)) := by
    rw [r4_4', g3 _ (by decide), r4_2, Offset.add_add, show 64 * c + 64 = 64 * (c + 1) by omega_using []]
  obtain ev4 : isa.eval (.nonzero .d .r6) t4 = some (decide (c = 0)) := by
    show some (t4.gpr .r6 != 0) = _
    rw [r6_4]
    congr 1
    have : 2 - (c + 1) < 2 ^ 64 := by omega_using []
    rcases (show c = 0 ∨ c = 1 by omega_using [hc]) with rfl | rfl <;> decide
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
          simp only [List.mem_singleton] at hr; subst hr; simp only [outR, r4_2, Nat.mul_zero]
          rw [BitVec.add_zero]
          exact Offset.disjoint _ (Or.inl (by omega_using [hlo])) (by omega_using [hc, hi']) (by omega_using [hc])),
        lvS t t2 _ f2 i (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [workS t hi.r8]
          exact schedWork.sub_left (Offset.sub_base _ (by omega_using [hc, hi']))), hi.done i hlo]
    · obtain ⟨w, rfl⟩ : ∃ w, i = 16 * c + w := ⟨i - 16 * c, by omega_using [hlo]⟩
      have := v3 w (by omega_using [hi'])
      rw [r4_2, Offset.add_add, show 64 * c + 4 * (0 + w) = 4 * (16 * c + w) by omega_using []] at this
      rw [this, g2 w (by omega_using [hi']), hi.cur w (by omega_using [hi'])]
  obtain frame4 : Frame [workR s, ⟨S, 128⟩] s.mem t4.mem := by
    rw [m4]
    refine (hi.frame.trans (f2.sub ?_)).trans (f3.sub ?_)
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact ⟨workR s, List.mem_cons_self, by rw [workS t hi.r8]; exact fun _ h => h⟩
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
      simp only [outR, r4_2, Nat.mul_zero]; rw [BitVec.add_zero]
      exact Offset.sub_base _ (by omega_using [hc])
  obtain room4 : Room t4 := room_congr hi.room (r8_4.trans hi.r8.symm) (by rw [wr4, wr3, wr2, hi.wr])
  refine WP.seq (WP.of_runBlock ⟨t4, runBlock_trans (runBlock_trans e2 e3) e4, ?_⟩)
  refine WP.ite (decide (c = 0)) ev4 (fun hb => ?_) (fun hb => ?_)
  · -- the second sixteen inputs
    obtain hc0 : c = 0 := by simpa using hb
    subst hc0
    obtain ⟨t5, e5, room5, v5, f5, rd5, wr5, g5⟩ := keyMove_ok room4
    refine WP.of_runBlock ⟨t5, e5, .inr ⟨?_, 1, by omega_using [], 1, by omega_using [], rfl, ?_⟩⟩
    · show some (t5.gpr .r6 != 0) = some true
      rw [g5 _ (by decide) (by decide), r6_4]
      decide
    obtain r8_5 : t5.gpr .r8 = s.gpr .r8 := (g5 _ (by decide) (by decide)).trans r8_4
    obtain workF : Frame [workR s] t4.mem t5.mem := by
      refine f5.sub fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨workR s, List.mem_cons_self, by rw [← workS t4 r8_4]; exact arraysR_sub_work t4⟩
    refine ⟨room5, r8_5, by rw [g5 _ (by decide) (by decide), r4_4], by rw [g5 _ (by decide) (by decide), r6_4],
      fun w hw => ?_, fun h => absurd h (by decide), fun i hi' => ?_, by rw [rd5, rd4, rd3, rd2, hi.rd],
      by rw [wr5, wr4, wr3, wr2, hi.wr],
      frame4.trans (workF.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩)⟩
    · rw [v5 _ (by decide) w hw, show newVal spMove (tSlot 0) (fun k' => lv t4 k' w) = lv t4 uSlot w from rfl,
        show lv t4 uSlot w = lv t3 uSlot w by
          simp only [lv, laneA, m4, g4 _ (show Reg.r8 ≠ .r4 by decide) (show Reg.r8 ≠ .r6 by decide)],
        lv_frame (g3 _ (by decide)) f3 out2 (by decide) hw, keep2 uSlot (by decide) (by decide) w hw,
        hi.next rfl w hw]
    · rw [lvS t4 t5 _ workF i (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact schedWork.sub_left (Offset.sub_base _ (by omega_using [hi'])))]
      exact done4 i hi'
  · -- the end
    obtain hc1 : c = 1 := by simp at hb; omega_using [hc, hb]
    subst hc1
    refine WP.block_nil (.inl ⟨?_, hQ t4 done4 r8_4 (by rw [rd4, rd3, rd2, hi.rd])
      (by rw [wr4, wr3, wr2, hi.wr]) frame4⟩)
    show some (t4.gpr .r6 != 0) = some false
    rw [r6_4]
    decide

end VG.Proof.Seed.PPC64LE

end

end

/-! ### `Seed.PPC64LE.KeyLoad`, which only this module used -/

section

/-!
# Loading the key on PPC64LE

`keyLoad2_ok`: `keyLoad2 d k` puts the key's big-endian words `k` and
`k + 4` in `d = Key_k || Key_k+1`.
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Impl.Seed.PPC64LE VG.Proof.Seed

theorem keyLoad2_ok {s : State} {d : Reg} (hd : d ≠ .r9) (hd3 : d ≠ .r3) {k : Nat} (hk : k ≤ 8) (hk4 : k % 4 = 0)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 k) 4)
    (hr' : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 (k + 4)) 4) :
    ∃ t, runBlock isa (keyLoad2 d k) s = some t ∧
      t.gpr d = Spec.Seed.wordAt (Spec.Seed.blockAt s.mem (s.gpr .r3)) k ++
        Spec.Seed.wordAt (Spec.Seed.blockAt s.mem (s.gpr .r3)) (k + 4) ∧
      (∀ r, r ≠ .r9 → r ≠ d → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp := by
  let W0 := s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 k) 32
  let W1 := s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 (k + 4)) 32
  obtain ⟨s1, e1, u1⟩ := step_x s (.li .r9 k) .r9 (BitVec.ofNat 64 k) (exec_li (by omega))
  obtain ⟨s2, e2, u2⟩ := step_x s1 (.loadRev .w .r9 .r3 .r9) .r9 ((rev32 W0).setWidth 64)
    (by rw [exec_loadRev_w (by decide) (by rw [u1.self, u1.other (by decide), u1.rd, u1.wr]; exact hr),
      u1.self, u1.other (by decide), u1.mem])
  obtain ⟨s3, e3, u3⟩ := step_x s2 (.lsl .r9 .r9 32) .r9 (s2.gpr .r9 <<< 32) (exec_lsl (by decide))
  obtain r3₃ : s3.gpr .r3 = s.gpr .r3 := by rw [u3.other (by decide), u2.other (by decide), u1.other (by decide)]
  obtain m3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  obtain ⟨s4, e4, u4⟩ := step_x s3 (.li d (k + 4)) d (BitVec.ofNat 64 (k + 4)) (exec_li (by omega_using [hk]))
  obtain r3₄ : s4.gpr .r3 = s.gpr .r3 := by rw [u4.other (Ne.symm hd3), r3₃]
  obtain hr4 : InRegions (s4.rd ++ s4.wr) (s4.gpr .r3 + s4.gpr d) 4 := by
    rw [u4.self, r3₄, u4.rd, u4.wr, u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact hr'
  obtain ⟨s5, e5, u5⟩ := step_x s4 (.loadRev .w d .r3 d) d ((rev32 W1).setWidth 64)
    (by rw [exec_loadRev_w (by decide) hr4, u4.self, r3₄, u4.mem, m3])
  obtain ⟨s6, e6, u6⟩ := step_x s5 (.logic .or d d .r9) d (s5.gpr d ||| s5.gpr .r9) exec_logic
  refine ⟨s6, ?_, ?_, fun r ha hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [keyLoad2, runBlock_cons, e1, runStep_some, runBlock_cons, e2, runStep_some, runBlock_cons, e3,
      runStep_some, runBlock_cons, e4, runStep_some, runBlock_cons, e5, runStep_some, runBlock_cons, e6,
      runStep_some, runBlock_nil]
  · rw [u6.self, u5.self, u5.other (Ne.symm hd), u4.other (Ne.symm hd), u3.self, u2.self,
      wordAt_blockAt _ _ (by omega_using [hk]), wordAt_blockAt _ _ (by omega_using [hk]), BitVec.or_comm,
      show rev32 = byteRev32 from rfl]
    have := BitVec.setWidth_append_eq_shiftLeft_setWidth_or (w'' := 64) (b := byteRev32 W0) (b' := byteRev32 W1)
    rw [BitVec.setWidth_eq] at this
    rw [this]
  · rw [u6.other hr, u5.other hr, u4.other hr, u3.other ha, u2.other ha, u1.other ha]
  · rw [u6.mem, u5.mem, u4.mem, m3]
  · rw [u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]
  · rw [u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]
  · rw [u6.sp, u5.sp, u4.sp, u3.sp, u2.sp, u1.sp]

end VG.Proof.Seed.PPC64LE

end

end


/-!
# Key expansion on PPC64LE

`expandKey_ok`: after saving the callee-saved registers, `expandKey` loads
the key, computes the schedule (`keyBody_ok`) and restores the registers.
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.PPC64LE.RegUpd VG.Impl.Seed.PPC64LE VG.Impl.Aes.PPC64LE
  VG.Proof.Seed

/-- What key expansion needs: the scratch buffer and the schedule writable,
the key readable, apart from each other. -/
structure KeyPre (s : State) : Prop where
  scratch : (⟨s.gpr .r5, 8 * scratchSlots⟩ : Region) ∈ s.wr
  schedIn : (⟨s.gpr .r4, 128⟩ : Region) ∈ s.wr
  keyIn : (⟨s.gpr .r3, 16⟩ : Region) ∈ s.rd
  keySched : (⟨s.gpr .r3, 16⟩ : Region).Disjoint ⟨s.gpr .r4, 128⟩
  keyBuf : (⟨s.gpr .r3, 16⟩ : Region).Disjoint ⟨s.gpr .r5, 8 * scratchSlots⟩
  schedBuf : (⟨s.gpr .r4, 128⟩ : Region).Disjoint ⟨s.gpr .r5, 8 * scratchSlots⟩

structure KeyPost (s s' : State) : Prop where
  saved : ∀ p ∈ Impl.Seed.PPC64LE.savedRegs, s'.gpr p.1 = s.gpr p.1
  sched : Spec.Seed.scheduleAt s'.mem (s.gpr .r4) = Spec.Seed.expandKey (Spec.Seed.blockAt s.mem (s.gpr .r3))
  frame : Frame [⟨s.gpr .r5, 8 * scratchSlots⟩, ⟨s.gpr .r4, 128⟩] s.mem s'.mem

theorem expandKey_eq_code : expandKey = .seq (.block (([movR .r8 .r5] ++
    (Impl.Seed.PPC64LE.savedRegs.map fun p => (p.2, p.1)).map (fun p => stS p.1 p.2)) ++
    (keyLoad2 .r6 0 ++ keyLoad2 .r7 8) ++ keyPre)) (.seq (.loop keyHalf (.nonzero .d .r6)) (.block restore)) := by
  simp only [expandKey, keyPre, Impl.Seed.PPC64LE.keyLoad, List.append_assoc]
  rfl

theorem expandKey_ok {s : State} (h : KeyPre s) : WP isa expandKey s (KeyPost s) := by
  let key := Spec.Seed.blockAt s.mem (s.gpr .r3)
  rw [expandKey_eq_code]
  -- `r8 := r5`
  let s₁ := s.write .r8 (s.gpr .r5)
  obtain e₁ : runBlock isa [movR .r8 .r5] s = some s₁ := by
    rw [runBlock_cons, exec_movR, runStep_some, runBlock_nil]
  obtain r9₁ : s₁.gpr .r8 = s.gpr .r5 := by simp [s₁, gpr_write]
  obtain g₁ : ∀ r, r ≠ .r8 → s₁.gpr r = s.gpr r := fun r hr => gpr_write_of_ne _ _ hr
  obtain scr₁ : scratchR s₁ = ⟨s.gpr .r5, 8 * scratchSlots⟩ := by simp only [scratchR, r9₁]
  obtain room₁ : Room s₁ := .of_mem (by rw [scr₁]; exact h.scratch)
  -- the saved registers
  obtain ⟨s₂, e₂, g₂, rd₂, wr₂, -, f₂, set₂, -⟩ := stores_ok room₁
    (Impl.Seed.PPC64LE.savedRegs.map fun p => (p.2, p.1)) (by decide) (by decide)
  obtain G₂ : ∀ r, r ≠ .r8 → s₂.gpr r = s.gpr r := fun r a => by rw [g₂, g₁ r a]
  obtain r9₂ : s₂.gpr .r8 = s.gpr .r5 := by rw [g₂, r9₁]
  obtain f₂' : Frame [⟨s.gpr .r5, 8 * scratchSlots⟩] s.mem s₂.mem := by rw [← scr₁]; exact f₂
  obtain rd₂' : s₂.rd = s.rd := by rw [rd₂]; rfl
  obtain wr₂' : s₂.wr = s.wr := by rw [wr₂]; rfl
  -- the key
  obtain r3₂ : s₂.gpr .r3 = s.gpr .r3 := G₂ _ (by decide)
  obtain hkey : ∀ k, k + 4 ≤ 16 → InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .r3 + BitVec.ofNat 64 k) 4 := fun k hk => by
    rw [rd₂', wr₂', r3₂]
    exact ⟨_, List.mem_append_left _ h.keyIn, Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])⟩
  obtain ⟨s₃, e₃, v₃, g₃, m₃, rd₃, wr₃, -⟩ := keyLoad2_ok (s := s₂) (d := .r6) (by decide) (by decide) (k := 0) (by decide)
    (by decide) (hkey 0 (by decide)) (hkey 4 (by decide))
  obtain r3₃ : s₃.gpr .r3 = s.gpr .r3 := by rw [g₃ _ (by decide) (by decide), r3₂]
  obtain ⟨s₄, e₄, v₄, g₄, m₄, rd₄, wr₄, -⟩ := keyLoad2_ok (s := s₃) (d := .r7) (by decide) (by decide) (k := 8) (by decide)
    (by decide)
    (by rw [rd₃, wr₃, r3₃, ← r3₂]; exact hkey 8 (by decide))
    (by rw [rd₃, wr₃, r3₃, ← r3₂]; exact hkey 12 (by decide))
  obtain key₂ : Spec.Seed.blockAt s₂.mem (s.gpr .r3) = key := blockAt_frame f₂' fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.keyBuf
  obtain G₄ : ∀ r, r ≠ .r9 → r ≠ .r6 → r ≠ .r7 → s₄.gpr r = s₂.gpr r := fun r a b c => by
    rw [g₄ r a c, g₃ r a b]
  obtain h3 : s₄.gpr .r6 = kx (keyWords key 0) := by
    rw [g₄ _ (by decide) (by decide), v₃, r3₂, key₂]; rfl
  obtain h4 : s₄.gpr .r7 = ky (keyWords key 0) := by
    rw [v₄, r3₃, m₃, key₂]; rfl
  obtain r9₄ : s₄.gpr .r8 = s.gpr .r5 := by rw [G₄ _ (by decide) (by decide) (by decide), r9₂]
  obtain rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂']
  obtain wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂']
  obtain mem₄ : s₄.mem = s₂.mem := by rw [m₄, m₃]
  obtain scr₄ : scratchR s₄ = ⟨s.gpr .r5, 8 * scratchSlots⟩ := by simp only [scratchR, r9₄]
  obtain room₄ : Room s₄ := .of_mem (by rw [scr₄, wr₄']; exact h.scratch)
  obtain r4₄ : s₄.gpr .r4 = s.gpr .r4 := by rw [G₄ _ (by decide) (by decide) (by decide), G₂ _ (by decide)]
  -- the rounds, and the count of halves
  obtain ⟨s₅, e₅, room₅, cur₅, next₅, r6₅, g₅, rd₅, wr₅, f₅⟩ := keyPre_ok key room₄ h3 h4
  obtain r9₅ : s₅.gpr .r8 = s₄.gpr .r8 := g₅ _ (by simp)
  obtain r4₅ : s₅.gpr .r4 = s.gpr .r4 := (g₅ _ (by simp)).trans r4₄
  obtain scr₅ : scratchR s₅ = ⟨s.gpr .r5, 8 * scratchSlots⟩ := by simp only [scratchR, r9₅, r9₄]
  obtain h0 : HalfInv key s₅ (s.gpr .r4) 0 s₅ :=
    ⟨room₅, rfl, by rw [r4₅]; exact (BitVec.add_zero _).symm, r6₅,
      fun w hw => by rw [cur₅ w hw, Nat.mul_zero, Nat.zero_add], fun _ => next₅, fun i hi => by omega, rfl, rfl,
      Frame.refl _ _⟩
  refine WP.seq (WP.of_runBlock ⟨s₅, runBlock_trans (runBlock_trans (runBlock_trans e₁ e₂)
    (runBlock_trans e₃ e₄)) e₅, WP.seq (keyHalves_wp key
      (by rw [wr₅, wr₄']; exact h.schedIn) (by rw [scr₅]; exact h.schedBuf) h0
      fun s₆ v₆ r9₆ rd₆ wr₆ f₆ => ?_)⟩)
  obtain room₆ : Room s₆ := room_congr room₅ r9₆ wr₆
  obtain ⟨s', e', m', -, set', -⟩ := loads_ok room₆ Impl.Seed.PPC64LE.savedRegs
    (fun q hq => ⟨(savedRegs_ok q hq).1, (savedRegs_ok q hq).2.1⟩) (by decide)
  refine WP.of_runBlock ⟨s', by rw [restore_eq]; exact e', ?_⟩
  obtain workR₅ : workR s₅ = ⟨s.gpr .r5, 8 * 112⟩ := by simp only [workR, r9₅, r9₄]
  rw [workR₅] at f₆
  obtain arr₄ : Region.Sub (arraysR s₄) ⟨s.gpr .r5, 8 * 112⟩ := by
    have := arraysR_sub_work s₄; simp only [workR, r9₄] at this; exact this
  obtain f₄₆ : Frame [⟨s.gpr .r5, 8 * 112⟩, ⟨s.gpr .r4, 128⟩] s₄.mem s₆.mem :=
    (f₅.sub fun r hr => ⟨_, List.mem_cons_self, by simp at hr; subst hr; exact arr₄⟩).trans f₆
  obtain frame : Frame [⟨s.gpr .r5, 8 * scratchSlots⟩, ⟨s.gpr .r4, 128⟩] s.mem s'.mem := by
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
      show s₆.mem.readW (StraightK.wordAddr (s₆.gpr .r8) q.2) 64 =
        s₄.mem.readW (StraightK.wordAddr (s₄.gpr .r8) q.2) 64
      rw [r9₆, r9₅, r9₄]
      refine f₄₆.readW (r := ⟨StraightK.wordAddr (s.gpr .r5) q.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint_base _ (by omega) (by unfold scratchSlots at hq'; omega)
      · exact (h.schedBuf.sub_right (Offset.sub_base _ (by unfold scratchSlots at hq' ⊢; omega))).symm
    obtain e4 : slotW s₄ q.2 = slotW s₂ q.2 := by
      show s₄.mem.readW (StraightK.wordAddr (s₄.gpr .r8) q.2) 64 =
        s₂.mem.readW (StraightK.wordAddr (s₂.gpr .r8) q.2) 64
      rw [mem₄, r9₄, r9₂]
    rw [e6, e4, set₂ (q.2, q.1) (List.mem_map_of_mem hq), g₁ _ hq'.2.1]
  · rw [Proof.Seed.expandKey_eq]
    apply Vector.ext
    intro i hi
    rw [scheduleAt_readW _ _ i hi, m', v₆ i hi, Vector.getElem_ofFn]

end VG.Proof.Seed.PPC64LE

end

end

/-! # Key expansion meets its contract, with the scratch buffer as an argument -/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE

open VG VG.PPC64LE

def keyContract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, 16⟩
    let sched : Region := ⟨s.gpr .r4, 128⟩
    let buf : Region := ⟨s.gpr .r5, 8 * Impl.Seed.PPC64LE.scratchSlots⟩
    s.rd = [key] ∧ s.wr = [sched, buf] ∧ key.Disjoint sched ∧ key.Disjoint buf ∧ sched.Disjoint buf
  post s s' :=
    Spec.Seed.scheduleAt s'.mem (s.gpr .r4) = Spec.Seed.expandKey (Spec.Seed.blockAt s.mem (s.gpr .r3))
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5

def keySatState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | _ => 0
  sp := 0x4000
  lr := 0
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 1040⟩]

theorem expandKey_wp (s : State) (hs : keyContract.pre s) :
    WP isa Impl.Seed.PPC64LE.expandKey s fun s' =>
      (∀ p ∈ Impl.Seed.PPC64LE.savedRegs, s'.gpr p.1 = s.gpr p.1) ∧ keyContract.post s s' := by
  obtain ⟨rd, wr, ks, kb, sb⟩ := hs
  refine WP.mono (expandKey_ok (s := s)
    { scratch := by rw [wr]; exact List.mem_cons_of_mem _ List.mem_cons_self
      schedIn := by rw [wr]; exact List.mem_cons_self
      keyIn := by rw [rd]; exact List.mem_cons_self
      keySched := ks
      keyBuf := kb
      schedBuf := sb }) fun _ hp => ⟨hp.saved, hp.sched⟩

theorem expandKey_correct (s : State) (hs : keyContract.pre s) :
    ∃ t s', Exec isa Impl.Seed.PPC64LE.expandKey s t s' ∧ abiPreserved s s' ∧ keyContract.post s s' := by
  have hn : Impl.Seed.PPC64LE.expandKey.noCalls = true := by lit_decide
  obtain ⟨t, s', he, hp, hk⟩ := WP.keep ecbWrites (expandKey_wp s hs) (by lit_decide) hn
  exact ⟨t, s', he, abi_of he hp.1 (hk.gpr (by decide)) (Exec.lr he hn (by lit_decide)), hp.2⟩

theorem expandKey_constantTime :
    ConstantTime isa keyContract.pre keyContract.pub Impl.Seed.PPC64LE.expandKey := by
  have hag : ∀ s₁ s₂, keyContract.pre s₁ → keyContract.pre s₂ → keyContract.pub s₁ s₂ →
      taint.Agree (Taint.ofRegs [.r3, .r4, .r5]) s₁ s₂ := by
    intro s₁ s₂ _ _ hp
    obtain ⟨hsp, h3, h4, h5⟩ := hp
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> with_reducible assumption
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5]) hag (by taint_decide)

theorem expandKey_verified : Verified target Impl.Seed.PPC64LE.expandKey
    (Proof.Seed.expandKeyScratchContract abi 130) := by
  refine Verified.of_correct expandKey_correct expandKey_constantTime ?_
  sig_implies [Proof.Seed.expandKeyScratchContract, Proof.Seed.expandKeyScratchSig, Proof.Seed.expandKeyPost,
    abi, argRegs, keyContract, Impl.Seed.PPC64LE.scratchSlots] [keySatState] using keySatState

end VG.Proof.Seed.PPC64LE

end

end

/-! ### `Seed.PPC64LE.EcbCall`, which only this module used -/

section

/-!
# SEED ECB on PPC64LE: calls of the blocks functions

`vg_seed_ecb_encrypt` and `vg_seed_ecb_decrypt` allocate their working
space on the stack (1088 bytes, as `vg_seed_{en,de}crypt_blocks` need) and
call the blocks function of their direction with it (`ecbCall`), the link
register saved in a 48-byte frame. `ecbCall_verified` proves that code from
the blocks functions' code (`ecb_correct`), with the working space as an
argument and 48 bytes of stack; `ecbCall_framed` adds the frame of the
working space.
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE

open VG VG.PPC64LE VG.Impl.Seed.PPC64LE

/-- The ECB contracts with `scratch: *mut [u64; 136]` and `stack = 48`, as
`sig_pre` evaluates them. -/
def ecbCallPPC64LE (d : Spec.Seed.Direction) : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .r3, 128⟩
    let data : Region := ⟨s.gpr .r4, (s.gpr .r5).toNat * 16⟩
    let scr : Region := ⟨s.gpr .r6, 1088⟩
    let stk : Region := ⟨s.sp - BitVec.ofNat 64 48, 48⟩
    48 ≤ s.sp.toNat ∧ s.rd = [sched] ∧ s.wr = [data, scr] ∧ sched.Disjoint data ∧ sched.Disjoint scr ∧
      data.Disjoint scr ∧ stk.Disjoint sched ∧ stk.Disjoint data ∧ stk.Disjoint scr ∧
      (s.gpr .r3).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + (s.gpr .r5).toNat * 16 ≤ 2 ^ 64 ∧
      (s.gpr .r6).toNat + 1088 ≤ 2 ^ 64
  post s s' :=
    Spec.Seed.blocksAt s'.mem (s.gpr .r4) (s.gpr .r5).toNat =
      Spec.Seed.ecb (Spec.Seed.scheduleAt s.mem (s.gpr .r3)) d
        (Spec.Seed.blocksAt s.mem (s.gpr .r4) (s.gpr .r5).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6

theorem fdepth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : c.fdepth = 0 := by
  induction c <;> simp_all [Code.noFrames, Code.fdepth]

theorem pushFrames_of_noFrames {c : Prog isa} (h : c.noFrames = true) : pushFrames c = true := by
  induction c <;> simp_all [Code.noFrames, pushFrames]

/-- The frame's two stores are within its 48 bytes. -/
theorem frame_push (s : State) (v : BitVec 64) :
    Frame [⟨s.sp - BitVec.ofNat 64 48, 48⟩] s.mem
      ((s.mem.write (s.sp - 48) 8 s.sp).write (s.sp - 48 + 32) 8 v) := by
  have e : (48 : BitVec 64) = BitVec.ofNat 64 48 := rfl
  have e32 : (32 : BitVec 64) = BitVec.ofNat 64 32 := rfl
  refine ((Frame.refl _ _).write (List.mem_singleton_self _) _ ?_).write (List.mem_singleton_self _) _ ?_
  · rw [e]; exact contains_prefix (by decide)
  · rw [e, e32]; exact Offset.contains_base _ (by decide) (by decide)

/-- A call, in a frame saving the link register, of ECB's code in the
direction `d`. -/
theorem call_correct (d : Spec.Seed.Direction) (s₀ : State) (hs : (ecbCallPPC64LE d).pre s₀) :
    ∃ t s', Exec isa (ecbCall d) s₀ t s' ∧ abiPreserved s₀ s' ∧ (ecbCallPPC64LE d).post s₀ s' := by
  obtain ⟨hsp, hrd, hwr, dKD, dKS, dDS, sK, sD, sS, fitK, fitD, fitS⟩ := hs
  let s₁ := s₀.write .r0 s₀.lr
  have hw : WP isa (ecbCall d) s₀ fun s' => abiPreserved s₀ s' ∧ (ecbCallPPC64LE d).post s₀ s' := by
    refine WP.seq (WP.cons exec_mflr (WP.block_nil (WP.seq ?_)))
    have hn : (blockCall d).noFrames = true := by cases d <;> lit_decide
    refine WP.frameReg (r := .r0) (s₀ := s₁) hsp (fun R hR => ?_) ?_
      (by rw [fdepth_of_noFrames hn]; decide) (pushFrames_of_noFrames hn)
    · rw [show s₁.wr = s₀.wr from rfl, hwr] at hR
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      have hsub : Region.Sub ⟨s₀.sp - 48 + 32, 16⟩ ⟨s₀.sp - BitVec.ofNat 64 48, 48⟩ := by
        rw [show (48 : BitVec 64) = BitVec.ofNat 64 48 from rfl,
          show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl]
        exact Offset.sub_base _ (by decide)
      rcases hR with rfl | rfl
      · exact sD.sub_left hsub
      · exact sS.sub_left hsub
    -- The call.
    let F := framed .r0 s₁
    have g : ∀ r, r ≠ .r0 → r ∉ linkRegs → F.callEntry.gpr r = s₀.gpr r := fun r h0 hl => by
      rw [State.callEntry_gpr _ hl]
      show (s₀.write .r0 s₀.lr).gpr r = s₀.gpr r
      exact RegUpd.gpr_write_of_ne _ _ h0
    have hc : ∀ (c : Prog isa) (name : String),
        (∀ s, (contract d 1088).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (contract d 1088).post s s') →
        c.noFrames = true →
        WP isa (.call name c) F fun s₂ => ∀ m u, Frame [⟨s₁.sp - 48, 48⟩] s₂.mem m →
          WP isa (.block [.mtlr .r0]) { s₂.write .r0 (s₁.gpr .r0) with sp := s₁.sp, mem := m, unknowns := u }
          fun s' => abiPreserved s₀ s' ∧ (ecbCallPPC64LE d).post s₀ s' := by
      intro c name hv hn'
      refine WP.call (k := contract d 1088) (s := F) hv (rd := s₀.rd) (wr := s₀.wr) ?_
        (fun _ _ h => h) (fun _ _ h => h) (fun s' rd' wr' sp' hf hp _ hpost m u f => ?_) hn'
      · have r3 := g .r3 (by decide) (by decide)
        have r4 := g .r4 (by decide) (by decide)
        have r5 := g .r5 (by decide) (by decide)
        have r6 := g .r6 (by decide) (by decide)
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          simp only [State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, r3, r4, r5, r6]
        · exact hrd
        · rw [hwr, Nat.mul_comm]
        · rw [Nat.mul_comm]; exact dKD
        · exact dKS
        · rw [Nat.mul_comm]; exact dDS
        · rw [Nat.mul_comm]; exact fitD
      · refine WP.cons exec_mtlr (WP.block_nil ⟨⟨fun r hr => ?_, rfl, ?_⟩, ?_⟩)
        · have h0 : r ≠ .r0 := by revert r hr; decide
          show (s'.write .r0 (s₁.gpr .r0)).gpr r = s₀.gpr r
          rw [RegUpd.gpr_write_of_ne _ _ h0, hp r hr]
          exact RegUpd.gpr_write_of_ne _ _ h0
        · show (s'.write .r0 (s₁.gpr .r0)).gpr .r0 = s₀.lr
          rw [RegUpd.gpr_write_self]; rfl
        · have hm : (s'.withRegions s₀.rd s₀.wr).mem = s'.mem := rfl
          have hm₀ : (F.callEntry.withRegions s₀.rd s₀.wr).mem = F.mem := rfl
          have r3 := g .r3 (by decide) (by decide)
          have r4 := g .r4 (by decide) (by decide)
          have r5 := g .r5 (by decide) (by decide)
          simp only [contract, State.withRegions_gpr, hm, hm₀, r3, r4, r5] at hpost
          show Spec.Seed.blocksAt m (s₀.gpr .r4) (s₀.gpr .r5).toNat = _
          -- The pop loses the frame's bytes, which lie apart from the data.
          rw [Proof.Seed.blocksAt_frame f (p := s₀.gpr .r4) (n := (s₀.gpr .r5).toNat) (fun r hr => by
            rw [List.mem_singleton] at hr; subst hr; exact sD.symm) (by omega_using [fitD])]
          have hfr := frame_push s₁ (s₁.gpr .r0)
          have hsch := Proof.Seed.scheduleAt_frame hfr (p := s₀.gpr .r3) fun r hr => by
            rw [List.mem_singleton] at hr; subst hr; exact sK.symm
          have hblk := Proof.Seed.blocksAt_frame hfr (p := s₀.gpr .r4) (n := (s₀.gpr .r5).toNat) (fun r hr => by
            rw [List.mem_singleton] at hr; subst hr; exact sD.symm) (by omega_using [fitD])
          rw [hpost, show F.mem = (s₁.mem.write (s₁.sp - 48) 8 s₁.sp).write (s₁.sp - 48 + 32) 8 (s₁.gpr .r0) from rfl,
            hsch, hblk]
          rfl
    cases d
    · exact hc _ _ (ecb_correct .encrypt (by decide)) (by lit_decide)
    · exact hc _ _ (ecb_correct .decrypt (by decide)) (by lit_decide)
  obtain ⟨t, s', he, h⟩ := hw
  exact ⟨t, s', he, h⟩

theorem ecbCallTaint_agree (d : Spec.Seed.Direction) (s₁ s₂ : State) (_ : (ecbCallPPC64LE d).pre s₁)
    (_ : (ecbCallPPC64LE d).pre s₂) (hp : (ecbCallPPC64LE d).pub s₁ s₂) :
    taint.Agree (Taint.ofRegs [.r3, .r4, .r5, .r6]) s₁ s₂ := by
  obtain ⟨hsp, h3, h4, h5, h6⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem ecbCall_ct (d : Spec.Seed.Direction) :
    ConstantTime isa (ecbCallPPC64LE d).pre (ecbCallPPC64LE d).pub (ecbCall d) := by
  cases d
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6]) (ecbCallTaint_agree .encrypt)
      (by taint_decide)
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6]) (ecbCallTaint_agree .decrypt)
      (by taint_decide)

/-- A state satisfying the precondition with the working space as an
argument: the schedule at `0x1000`, one block at `0x3000`, the working space
at `0x4000`. -/
def ecbCallSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x3000 | .r5 => 1 | .r6 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x3000, 16⟩, ⟨0x4000, 1088⟩]

theorem ecbCall_verified (d : Spec.Seed.Direction) :
    Verified target (ecbCall d) (Proof.Seed.ecbScratchContract abi d 136 48) :=
  Verified.of_correct (call_correct d) (ecbCall_ct d) (by
    sig_implies [Proof.Seed.ecbScratchContract, Proof.Seed.ecbScratchSig, Spec.Seed.ecbPost, ecbCallPPC64LE,
      abi, argRegs] [ecbCallSat] using ecbCallSat)

end VG.Proof.Seed.PPC64LE

end

end

/-!
# SEED on PPC64LE, with its working space on the stack

Key expansion runs its code, and ECB its call of the blocks function
(`EcbCall.lean`), proved with the working space as an argument, in a frame
that allocates it and zeroes it after the code (`Verified.stackScratchWiped`),
since it holds the key, the round keys and the data: for key expansion the
1040 bytes of the working space's 130 words, for ECB the 1088 bytes of the
blocks function's 136, and 32 bytes of the frame.
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE

open VG VG.PPC64LE

def expandKeyFrameSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 128⟩]

theorem expandKeyFrameSat_pre : ∃ s, (Spec.Seed.expandKeyContract abi 1072).pre s := by
  implies_sat [Spec.Seed.expandKeyContract, Spec.Seed.expandKeySig, abi, argRegs]
    [expandKeyFrameSat] using expandKeyFrameSat

/-- Key expansion, with its working space on the stack. -/
theorem expandKey_framed :
    Verified target (Impl.StackScratch.PPC64LE.withStackScratchWiped 1072 .r5 130 Impl.Seed.PPC64LE.expandKey)
      (Spec.Seed.expandKeyContract abi 1072) :=
  Verified.stackScratchWiped (sig := Spec.Seed.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 130) (post := Proof.Seed.expandKeyPost abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 1072) (words := 130) expandKey_verified (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Seed.expandKeyPost_local _)
    (Proof.Seed.expandKeyPostOut_local _) expandKeyFrameSat_pre

def ecbFrameSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x3000 | .r5 => 1 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x3000, 16⟩]

theorem ecbFrameSat_pre (d : Spec.Seed.Direction) : ∃ s, (Spec.Seed.ecbContract abi d 1168).pre s := by
  implies_sat [Spec.Seed.ecbContract, Spec.Seed.ecbSig, Spec.Seed.ecbPost, abi, argRegs]
    [ecbFrameSat] using ecbFrameSat

/-- ECB in the direction `d`, a call of the blocks function with its working
space on the stack: 1168 bytes of stack in all. -/
theorem ecbCall_framed (d : Spec.Seed.Direction) :
    Verified target (Impl.StackScratch.PPC64LE.withStackScratchWiped 1120 .r6 136 (Impl.Seed.PPC64LE.ecbCall d))
      (Spec.Seed.ecbContract abi d 1168) :=
  Verified.stackScratchWiped (sig := Spec.Seed.ecbSig) (nm := "scratch") (e := .u64)
    (n := 136) (post := Spec.Seed.ecbPost d abi.ptrBits) (wa := true) (stack := 48)
    (bytes := 1120) (words := 136) (ecbCall_verified d) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Seed.ecbPost_local _ _)
    (Proof.Seed.ecbPostOut_local _ _) (ecbFrameSat_pre _)

end VG.Proof.Seed.PPC64LE
