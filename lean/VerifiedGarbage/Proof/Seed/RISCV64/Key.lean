module

public import VerifiedGarbage.Impl.Seed.RISCV64.ExpandKey
public import VerifiedGarbage.Proof.Seed.RISCV64.Lanes
public import VerifiedGarbage.Proof.Seed.RISCV64.Round
import VerifiedGarbage.Proof.Seed.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Seed.KeySchedule
import VerifiedGarbage.Proof.Seed.RISCV64.Batch
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Seed.RISCV64.Setup
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
import VerifiedGarbage.Proof.Seed.RISCV64.Ecb
import VerifiedGarbage.Proof.Seed.Memory
public import VerifiedGarbage.Impl.Seed.RISCV64.Ecb
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Target

/-! ### `Seed.RISCV64.KeyBody`, which only this module used -/

section

/-! ### `Seed.RISCV64.KeyStore`, which only this module used -/

section

/-!
# Copying `G`'s outputs on RISC-V

As on PPC64LE (`Proof/Seed/PPC64LE/KeyStore.lean`): `keyStore_ok`:
`keyStore k` copies the sixteen lanes of `G`'s words to the schedule's words
from `k`, a byte at a time (`storeLE32`); `keyMove_ok`: `keyMove` copies the
second sixteen inputs of `G` to its words.
-/

@[expose] public section

namespace VG.Proof.Seed.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Impl.Seed.RISCV64 VG.Proof.Seed
open VG.Impl.Aes.RISCV64 (sb)

/-- The schedule's words from `k`. -/
def outR (s : State) (k : Nat) : Region := ⟨s.gpr .a1 + BitVec.ofNat 64 (4 * k), 64⟩

theorem keyStore_ok (k : Nat) (hk : k ≤ 16) {s : State} (h : Room s)
    (hw : ∀ w < 16, InRegions s.wr (s.gpr .a1 + BitVec.ofNat 64 (4 * (k + w))) 4)
    (hsep : (outR s k).Disjoint (scratchR s)) :
    ∀ n ≤ 16, ∃ t, runBlock isa ((List.range n).flatMap fun w =>
        ldW .t0 (tSlot 0) w :: Impl.Words.RISCV64.storeLE32 .t0 .t1 .a1 (4 * (k + w))) s = some t ∧
      (∀ w < n, t.mem.readW (s.gpr .a1 + BitVec.ofNat 64 (4 * (k + w))) 32 = lv s (tSlot 0) w) ∧
      (∀ r, r ≠ .t0 → r ≠ .t1 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Frame [outR s k] s.mem t.mem
  | 0, _ => ⟨s, runBlock_nil, fun w hw => by omega, fun _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | n + 1, hn => by
    obtain ⟨t, ht, hv, hg, hrd, hwr, hsp, hf⟩ := keyStore_ok k hk h hw hsep n (by omega_using [hn])
    obtain sbt : t.gpr sb = s.gpr sb := hg _ (by decide) (by decide)
    obtain a1t : t.gpr .a1 = s.gpr .a1 := hg _ (by decide) (by decide)
    obtain room : Room t := room_congr h sbt hwr
    obtain hlane : lv t (tSlot 0) n = lv s (tSlot 0) n := by
      simp only [lv, laneA, sbt]
      refine hf.readW (r := ⟨s.gpr sb + BitVec.ofNat 64 (8 * tSlot 0 + 4 * n), 4⟩) (Region.contains_self _ _) ?_
        (by decide)
      intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      refine (hsep.sub_right ?_).symm
      show Region.Sub ⟨s.gpr sb + BitVec.ofNat 64 (8 * tSlot 0 + 4 * n), 4⟩ ⟨s.gpr sb, 8 * scratchSlots⟩
      exact Offset.sub_base _ (by unfold scratchSlots tSlot; omega_using [hn])
    let t1 := t.write .t0 ((lv t (tSlot 0) n).setWidth 64)
    obtain e1 : exec (ldW .t0 (tSlot 0) n) t = some t1 := exec_ldW_lane room mem_tA (by omega_using [hn]) .t0
    obtain hw1 : InRegions t1.wr (t1.gpr .a1 + BitVec.ofNat 64 (4 * (k + n))) 4 := by
      simp only [t1, wr_write, gpr_write_of_ne _ _ (show ¬ Reg.a1 = .t0 by decide), hwr, a1t]
      exact hw n (by omega_using [hn])
    obtain ⟨t2, e2, h2⟩ := run_of_wp (ByteLoad.storeLE32_ok (s := t1) (v := .t0) (tmp := .t1) (n := .a1)
      (off := 4 * (k + n)) (by decide) (by decide) (by omega_using [hk, hn]) hw1)
    obtain m2 : t2.mem = t.mem.writeW (s.gpr .a1 + BitVec.ofNat 64 (4 * (k + n))) (lv s (tSlot 0) n) := by
      rw [h2, mem_write]
      show t1.mem.writeW _ _ = _
      simp only [t1, gpr_write_self, gpr_write_of_ne _ _ (show ¬ Reg.a1 = .t0 by decide), a1t,
        mem_write, lo32_ext, hlane]
    refine ⟨t2, ?_, fun w hw' => ?_, fun r h1 h2' => ?_, by rw [h2]; exact hrd, by rw [h2]; exact hwr,
      by rw [h2]; exact hsp, ?_⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      exact runBlock_trans ht (by rw [runBlock_cons, e1, runStep_some]; exact e2)
    · rw [m2]
      by_cases hwn : w = n
      · subst hwn; rw [Mem.readW_writeW_self32]
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_using [hwn]) (by omega_using [hk, hn, hw']) (by omega_using [hk, hn])) (by decide)]
        exact hv w (by omega_using [hw', hwn])
    · rw [h2, gpr_write_of_ne _ _ h2']
      show t1.gpr r = s.gpr r
      simp only [t1, gpr_write_of_ne _ _ h1]; exact hg r h1 h2'
    · rw [m2]
      exact hf.writeW List.mem_cons_self _ (Offset.contains _ (by omega_using []) (by omega_using [hn]) (by omega_using [hk]))

/-- Moving lane `b` of `uSlot` to `G`'s words. -/
def spMove : LaneSpec := [(tSlot 0, fun x => x uSlot)]

theorem keyMove_ok {s : State} (h : Room s) :
    ∃ s', runBlock isa keyMove s = some s' ∧ Room s' ∧
      (∀ k ∈ arrays, ∀ b < 16, lv s' k b = newVal spMove k (fun k' => lv s k' b)) ∧
      Frame [arraysR s] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ (∀ r, r ≠ .t0 → r ≠ .t1 → s'.gpr r = s.gpr r) := by
  refine lanes16_room (f := fun w => [ldW .t0 uSlot w, stW (tSlot 0) w .t0])
    (by decide) ?_ (fun b hb s h => ?_) h
  · intro kv hkv x y hxy
    simp only [spMove, List.mem_singleton] at hkv; subst hkv
    exact hxy uSlot (by decide)
  · rw [runBlock_cons, exec_ldW_lane h (by decide) hb, runStep_some, runBlock_cons,
      exec_stW_lane ?h1 (by decide) hb, runStep_some, runBlock_nil]
    case h1 => exact room_congr h rfl rfl
    refine ⟨_, rfl, ?_, rfl, rfl, rfl, fun r h1 h2 => ?_⟩
    · simp only [laneWrites, spMove, List.foldl_cons, List.foldl_nil, gpr_write_self,
        setWidth_setWidth_32, mem_setMem, mem_write,
        laneA_write _ _ (show ¬ sb = .t0 by decide)]
    · simp only [gpr_write_of_ne _ _ h1, gpr_setMem]

end VG.Proof.Seed.RISCV64

end

end

/-! ### `Seed.RISCV64.KeyRounds`, which only this module used -/

section

/-! ### `Seed.RISCV64.KeyRound`, which only this module used -/

section

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
    (exec_shl _ _ _ _ (by omega_using [hr]))
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
  obtain hb0 : 2 * j % 16 < 16 := Nat.mod_lt _ (by decide)
  obtain hb1 : (2 * j + 1) % 16 < 16 := Nat.mod_lt _ (by decide)
  obtain hd : gSlot (2 * j + 1) ≠ gSlot (2 * j) ∨ (2 * j + 1) % 16 ≠ 2 * j % 16 :=
    gIn_apart _ (by omega_using [hj]) _ (by omega_using [hj]) (by omega_using [])
  let c := kcs.getD j 0
  obtain ⟨s1, e1, u1⟩ := step_x s (shrI .t0 .t5 32) .t0 (s.gpr .t5 >>> 32) (exec_shr _ _ _ _ (by decide))
  obtain ⟨s2, e2, u2⟩ := step_x s1 (shrI .t1 .t6 32) .t1 (s1.gpr .t6 >>> 32) (exec_shr _ _ _ _ (by decide))
  obtain ⟨s3, e3, u3⟩ := step_x s2 (addW .t0 .t0 .t1) .t0 (s2.gpr .t0 + s2.gpr .t1) rfl
  obtain ⟨s4, e4, u4⟩ := li32_run s3 .t2 c
  obtain ⟨s6, e6, u6⟩ := step_x s4 (.sub .t0 .t0 .t2) .t0 (s4.gpr .t0 - s4.gpr .t2) rfl
  obtain g6 : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → s6.gpr r = s.gpr r := fun r a b c' => by
    rw [u6.other a, u4.other c', u3.other a, u2.other b, u1.other a]
  obtain room6 : Room s6 := room_congr h (g6 _ (by decide) (by decide) (by decide))
    (by rw [u6.wr, u4.wr, u3.wr, u2.wr, u1.wr])
  obtain ⟨s7, e7, g7, rd7, wr7, sp7, m7⟩ := step_store_lane room6 (gSlot_mem (2 * j)) hb0
  obtain ⟨s8, e8, u8⟩ := step_x s7 (.sub .t0 .t5 .t6) .t0 (s7.gpr .t5 - s7.gpr .t6) rfl
  obtain ⟨s9, e9, u9⟩ := step_x s8 (addW .t0 .t0 .t2) .t0 (s8.gpr .t0 + s8.gpr .t2) rfl
  obtain room9 : Room s9 := room_congr room6 (by rw [u9.other (by decide), u8.other (by decide), g7])
    (by rw [u9.wr, u8.wr, wr7])
  obtain ⟨s10, e10, g10, rd10, wr10, sp10, m10⟩ := step_store_lane room9 (gSlot_mem (2 * j + 1)) hb1
  obtain sb_6 : s6.gpr sb = s.gpr sb := g6 _ (by decide) (by decide) (by decide)
  obtain sb_9 : s9.gpr sb = s.gpr sb := by rw [u9.other (by decide), u8.other (by decide), g7, sb_6]
  obtain lA6 : ∀ k b, laneA s6 k b = laneA s k b := fun k b => by simp only [laneA, sb_6]
  obtain lA9 : ∀ k b, laneA s9 k b = laneA s k b := fun k b => by simp only [laneA, sb_9]
  -- the values
  obtain hc : (s4.gpr .t2).setWidth 32 = c := by rw [u4.self, lo32_sext]
  obtain v6 : (s6.gpr .t0).setWidth 32 = gIn0 (s.gpr .t5) (s.gpr .t6) c := by
    rw [u6.self, lo32_sub, hc, u4.other (by decide), u3.self, lo32_add,
      u2.other (by decide), u2.self, u1.self, u1.other (by decide)]
    rfl
  obtain v9 : (s9.gpr .t0).setWidth 32 = gIn1 (s.gpr .t5) (s.gpr .t6) c := by
    rw [u9.self, lo32_add, u8.self, lo32_sub, u8.other (show Reg.t2 ≠ .t0 by decide), g7,
      u6.other (show Reg.t2 ≠ .t0 by decide), hc, g6 .t5 (by decide) (by decide) (by decide),
      g6 .t6 (by decide) (by decide) (by decide)]
    rfl
  obtain mem9 : s9.mem = s7.mem := by rw [u9.mem, u8.mem]
  obtain mem6 : s6.mem = s.mem := by rw [u6.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  obtain hrun : runBlock isa (([shrI .t0 .t5 32, shrI .t1 .t6 32, addW .t0 .t0 .t1] : List Instr) ++
      Impl.Words.RISCV64.li32 .t2 c ++
      ([.sub .t0 .t0 .t2, stW (gSlot (2 * j)) (2 * j % 16) .t0, .sub .t0 .t5 .t6, addW .t0 .t0 .t2,
        stW (gSlot (2 * j + 1)) ((2 * j + 1) % 16) .t0] : List Instr)) s = some s10 := by
    refine runBlock_trans (runBlock_trans ?_ e4) ?_
    · rw [runBlock_cons, e1, runStep_some, runBlock_cons, e2, runStep_some, runBlock_cons, e3, runStep_some,
        runBlock_nil]
    · rw [runBlock_cons, e6, runStep_some, runBlock_cons, e7, runStep_some, runBlock_cons, e8, runStep_some,
        runBlock_cons, e9, runStep_some, runBlock_cons, e10, runStep_some, runBlock_nil]
  -- the lanes after both stores
  obtain lv10 : ∀ k ∈ arrays, ∀ b < 16, lv s10 k b =
      ((s.mem.writeW (laneA s (gSlot (2 * j)) (2 * j % 16)) (gIn0 (s.gpr .t5) (s.gpr .t6) c)).writeW
        (laneA s (gSlot (2 * j + 1)) ((2 * j + 1) % 16)) (gIn1 (s.gpr .t5) (s.gpr .t6) c)).readW
        (laneA s k b) 32 := by
    intro k _ b _
    simp only [lv, laneA, g10, u9.other (show sb ≠ .t0 by decide), u8.other (show sb ≠ .t0 by decide),
      g7]
    rw [m10, mem9, m7, lA9, lA6, v6, v9, mem6]
    simp only [laneA, sb_6]
  obtain lane0 : lv s10 (gSlot (2 * j)) (2 * j % 16) = gIn0 (s.gpr .t5) (s.gpr .t6) c := by
    rw [lv10 _ (gSlot_mem _) _ hb0, readW_writeW_lane (gSlot_mem _) hb0 (gSlot_mem _) hb1
      (by rcases hd with h | h; exact Or.inl (Ne.symm h); exact Or.inr (Ne.symm h)), Mem.readW_writeW_self32]
  obtain lane1 : lv s10 (gSlot (2 * j + 1)) ((2 * j + 1) % 16) = gIn1 (s.gpr .t5) (s.gpr .t6) c := by
    rw [lv10 _ (gSlot_mem _) _ hb1, Mem.readW_writeW_self32]
  obtain lanes : ∀ k ∈ arrays, ∀ b < 16, (k ≠ gSlot (2 * j) ∨ b ≠ 2 * j % 16) →
      (k ≠ gSlot (2 * j + 1) ∨ b ≠ (2 * j + 1) % 16) → lv s10 k b = lv s k b := by
    intro k hk b hb h0 h1
    rw [lv10 k hk b hb, readW_writeW_lane hk hb (gSlot_mem _) hb1 h1,
      readW_writeW_lane hk hb (gSlot_mem _) hb0 h0]
    rfl
  obtain frame : Frame [arraysR s] s.mem s10.mem := by
    rw [m10, mem9, m7, lA9, lA6, mem6]
    exact ((Frame.refl _ _).writeW List.mem_cons_self _ (lane_inArrays (gSlot_mem _) hb0 s)).writeW
      List.mem_cons_self _ (lane_inArrays (gSlot_mem _) hb1 s)
  obtain G10 : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → s10.gpr r = s.gpr r := by
    intro r ha hb hc'
    rw [g10, u9.other ha, u8.other ha, g7, g6 r ha hb hc']
  obtain rd10' : s10.rd = s.rd := by rw [rd10, u9.rd, u8.rd, rd7, u6.rd, u4.rd, u3.rd, u2.rd, u1.rd]
  obtain wr10' : s10.wr = s.wr := by rw [wr10, u9.wr, u8.wr, wr7, u6.wr, u4.wr, u3.wr, u2.wr, u1.wr]
  obtain sp10' : s10.sp = s.sp := by rw [sp10, u9.sp, u8.sp, sp7, u6.sp, u4.sp, u3.sp, u2.sp, u1.sp]
  obtain sb10 : s10.gpr sb = s.gpr sb := G10 _ (by decide) (by decide) (by decide)
  obtain lvR : ∀ {t : State}, t.gpr sb = s10.gpr sb → t.mem = s10.mem → ∀ k b, lv t k b = lv s10 k b :=
    fun ht hm k b => by simp only [lv, laneA, ht, hm]
  -- the rotation
  by_cases hj2 : j % 2 = 0
  · obtain ⟨s11, e11, r11, o11, m11, rd11, wr11, sp11⟩ := rot_run s10 .t5 (by decide) 8 (by decide) (by decide)
    obtain sb11 : s11.gpr sb = s10.gpr sb := o11 _ (by decide) (by decide)
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
    obtain sb11 : s11.gpr sb = s10.gpr sb := o11 _ (by decide) (by decide)
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

end

end


/-!
# The sixteen rounds of the key schedule on RISC-V

As on PPC64LE (`Proof/Seed/PPC64LE/KeyRounds.lean`): `keyRounds_ok`: after
`n` rounds, `t5` and `t6` hold the key words of round `n + 1` (`keyWords`),
and the lanes of `G`'s first `2 * n` inputs hold them (`gInput`).
-/

@[expose] public section

namespace VG.Proof.Seed.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Impl.Seed.RISCV64 VG.Proof.Seed
open VG.Impl.Aes.RISCV64 (sb)

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

/-- The key words `k` as `t5` and `t6` hold them. -/
def kx (k : Quad) : BitVec 64 := k.1 ++ k.2.1
def ky (k : Quad) : BitVec 64 := k.2.2.1 ++ k.2.2.2

/-- After `n` rounds of the key schedule. -/
structure KeyInv (key : Spec.Seed.Block) (s₀ : State) (n : Nat) (s : State) : Prop where
  t5 : s.gpr .t5 = kx (keyWords key n)
  t6 : s.gpr .t6 = ky (keyWords key n)
  lanes : ∀ i < 2 * n, lv s (gSlot i) (i % 16) = gInput key i
  regs : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → r ≠ .t5 → r ≠ .t6 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [arraysR s₀] s₀.mem s.mem

theorem keyRounds_ok (key : Spec.Seed.Block) {s₀ : State} (h : Room s₀)
    (h10 : s₀.gpr .t5 = kx (keyWords key 0)) (h11 : s₀.gpr .t6 = ky (keyWords key 0)) :
    ∀ n ≤ 16, ∃ s, runBlock isa ((List.range n).flatMap keyRound) s₀ = some s ∧ KeyInv key s₀ n s
  | 0, _ => ⟨s₀, runBlock_nil, h10, h11, fun i hi => by omega, fun _ _ _ _ _ _ => rfl, rfl, rfl, rfl,
      Frame.refl _ _⟩
  | n + 1, hn => by
    obtain ⟨s, hs, inv⟩ := keyRounds_ok key h h10 h11 n (by omega_using [hn])
    obtain r9 : s.gpr sb = s₀.gpr sb := inv.regs _ (by decide) (by decide) (by decide) (by decide) (by decide)
    obtain ⟨s', hs', l0, l1, lk, r6', r7', regs', rd', wr', sp', f'⟩ :=
      keyRound_ok (j := n) (by omega_using [hn]) (room_congr h r9 inv.wr)
    refine ⟨s', ?_, ⟨?_, ?_, fun i hi => ?_, fun r a b c d e => ?_, by rw [sp', inv.sp], by rw [rd', inv.rd],
      by rw [wr', inv.wr], ?_⟩⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      exact runBlock_trans hs hs'
    · rw [r6', inv.t5]
      simp only [keyWords, keyStep]
      split
      · simp only [kx]; exact (split64 _).symm
      · rfl
    · rw [r7', inv.t6]
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
        rw [l0, g0, gIn0, inv.t5, inv.t6, kx, ky, hi_append, hi_append, kcs_eq n (by omega_using [hn])]
      by_cases hi1 : i = 2 * n + 1
      · subst hi1
        rw [l1, g1, gIn1, inv.t5, inv.t6, kx, ky, BitVec.setWidth_append_eq_right,
          BitVec.setWidth_append_eq_right, kcs_eq n (by omega_using [hn])]
      · rw [lk _ (gSlot_mem i) _ (Nat.mod_lt _ (by decide)) (gIn_apart _ (by omega_using [hn, hi]) _ (by omega_using [hn]) hi0)
          (gIn_apart _ (by omega_using [hn, hi]) _ (by omega_using [hn]) hi1)]
        exact inv.lanes i (by omega_using [hi, hi0, hi1])
    · rw [regs' r a b c d e, inv.regs r a b c d e]
    · have : arraysR s = arraysR s₀ := by simp only [arraysR, r9]
      rw [this] at f'
      exact inv.frame.trans f'

end VG.Proof.Seed.RISCV64

end

end


/-!
# The key schedule's computation on RISC-V

As on PPC64LE (`Proof/Seed/PPC64LE/KeyBody.lean`): from `t5 = Key0 || Key1`
and `t6 = Key2 || Key3`, the rounds (`keyPre_ok`), the two `g16`s and the
copies (`keyHalves_wp`) write `G` of the 32 inputs (`gInput`) to the
schedule.
-/

@[expose] public section

namespace VG.Proof.Seed.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Impl.Seed.RISCV64 VG.Proof.Seed
open VG.Impl.Aes.RISCV64 (sb)

/-- The rounds and the count of halves, between loading the key and the loop. -/
def keyPre : List Instr := (List.range 16).flatMap keyRound ++ [.li .a4 2]

theorem gSlot_lo {i : Nat} (hi : i < 16) : gSlot i = tSlot 0 := by simp [gSlot, hi]
theorem gSlot_hi {w : Nat} (hw : w < 16) : gSlot (16 + w) = uSlot := by
  simp [gSlot, show ¬ 16 + w < 16 by omega]

/-- A lane after a frame over regions apart from the scratch buffer. -/
theorem lv_frame {s s' : State} {R : Region} (hx5 : s'.gpr sb = s.gpr sb) (hf : Frame [R] s.mem s'.mem)
    (hd : R.Disjoint (scratchR s)) {k b : Nat} (hk : k ∈ arrays) (hb : b < 16) : lv s' k b = lv s k b := by
  simp only [lv, laneA, hx5]
  refine hf.readW (r := ⟨s.gpr sb + BitVec.ofNat 64 (8 * k + 4 * b), 4⟩) (Region.contains_self _ _) ?_
    (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact (hd.sub_right (lane_in hk hb s |> fun _ => by
    have := arrays_bound k hk
    exact Offset.sub_base _ (by unfold scratchSlots; omega_using [hb, this]))).symm

theorem keyPre_ok (key : Spec.Seed.Block) {s : State} (h : Room s)
    (h3 : s.gpr .t5 = kx (keyWords key 0)) (h4 : s.gpr .t6 = ky (keyWords key 0)) :
    ∃ s', runBlock isa keyPre s = some s' ∧ Room s' ∧
      (∀ w < 16, lv s' (tSlot 0) w = gInput key w) ∧ (∀ w < 16, lv s' uSlot w = gInput key (16 + w)) ∧
      s'.gpr .a4 = BitVec.ofNat 64 2 ∧
      (∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → r ≠ .t5 → r ≠ .t6 → r ≠ .a4 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [arraysR s] s.mem s'.mem := by
  obtain ⟨s1, e1, inv⟩ := keyRounds_ok key h h3 h4 16 (Nat.le_refl _)
  let s2 := s1.write .a4 (BitVec.ofNat 64 2)
  obtain e2 : runBlock isa [.li .a4 2] s1 = some s2 := by
    rw [runBlock_cons, exec_li (by decide), runStep_some, runBlock_nil]; rfl
  obtain g2 : ∀ r, r ≠ .a4 → s2.gpr r = s1.gpr r := fun r hr => gpr_write_of_ne _ _ hr
  obtain sb_1 : s1.gpr sb = s.gpr sb := inv.regs _ (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain sb_2 : s2.gpr sb = s.gpr sb := (g2 _ (by decide)).trans sb_1
  obtain lv2 : ∀ k b, lv s2 k b = lv s1 k b := fun k b => by
    simp only [lv, laneA, g2 _ (show sb ≠ .a4 by decide)]; rfl
  refine ⟨s2, runBlock_trans e1 e2, room_congr h sb_2 inv.wr, fun w hw => ?_, fun w hw => ?_,
    by simp [s2, gpr_write], fun r a b c d e f => ?_, inv.rd, inv.wr, inv.sp, inv.frame⟩
  · rw [lv2, ← inv.lanes w (by omega_using [hw]), gSlot_lo hw, Nat.mod_eq_of_lt hw]
  · rw [lv2, ← inv.lanes (16 + w) (by omega_using [hw]), gSlot_hi hw, show (16 + w) % 16 = w by omega_using [hw]]
  · rw [g2 _ f, inv.regs _ a b c d e]

/-- `addi a1, a1, 64; addi a4, a4, -1`. -/
theorem halfTail_ok (t : State) :
    ∃ t', runBlock isa [.addi .a1 .a1 64, .addi .a4 .a4 (-1)] t = some t' ∧
      t'.gpr .a1 = t.gpr .a1 + BitVec.ofNat 64 64 ∧ t'.gpr .a4 = t.gpr .a4 - BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .a1 → r ≠ .a4 → t'.gpr r = t.gpr r) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      t'.sp = t.sp := by
  refine ⟨_, by
    rw [runBlock_cons, exec_addi (by decide), runStep_some, runBlock_cons, exec_dec _ .a4,
      runStep_some, runBlock_nil], ?_⟩
  refine ⟨by simp [gpr_write], by simp [gpr_write], fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  simp [gpr_write, h1, h2]

/-- After `c` of the two halves: `a1` at the schedule's word `16 c`, `a4` the
halves left, `G`'s words holding the next sixteen inputs, the schedule's
words before `16 c` done. -/
structure HalfInv (key : Spec.Seed.Block) (s : State) (S : Addr) (c : Nat) (t : State) : Prop where
  room : Room t
  masks : Masks t
  sb : t.gpr sb = s.gpr sb
  a1 : t.gpr .a1 = S + BitVec.ofNat 64 (64 * c)
  a4 : t.gpr .a4 = BitVec.ofNat 64 (2 - c)
  regs : ∀ r ∈ [Reg.ra, .a0, .a2, .a3, .a5], t.gpr r = s.gpr r
  cur : ∀ w < 16, lv t (tSlot 0) w = gInput key (16 * c + w)
  next : c = 0 → ∀ w < 16, lv t uSlot w = gInput key (16 + w)
  done : ∀ i < 16 * c, t.mem.readW (S + BitVec.ofNat 64 (4 * i)) 32 = Spec.Seed.g (gInput key i)
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame [workR s, ⟨S, 128⟩] s.mem t.mem

theorem keyHalves_wp (key : Spec.Seed.Block) {s : State} {S : Addr} (hin : (⟨S, 128⟩ : Region) ∈ s.wr)
    (hsep : (⟨S, 128⟩ : Region).Disjoint (scratchR s)) (h0 : HalfInv key s S 0 s) {Q : State → Prop}
    (hQ : ∀ t, (∀ i < 32, t.mem.readW (S + BitVec.ofNat 64 (4 * i)) 32 = Spec.Seed.g (gInput key i)) →
      (∀ r ∈ [Reg.ra, .a0, .a2, .a3, .a5], t.gpr r = s.gpr r) → t.rd = s.rd → t.wr = s.wr →
      t.sp = s.sp → Frame [workR s, ⟨S, 128⟩] s.mem t.mem → Q t) :
    WP isa (.loop keyHalf (.nonzero .a4)) s Q := by
  refine WP.loop (M := isa) (fun n t => ∃ c, c < 2 ∧ n = 2 - c ∧ HalfInv key s S c t) (fun n t ht => ?_) 2 s
    ⟨0, by decide, rfl, h0⟩
  obtain ⟨c, hc, rfl, hi⟩ := ht
  obtain scrS : ∀ t : State, t.gpr sb = s.gpr sb → scratchR t = scratchR s := fun t h => by simp only [scratchR, h]
  obtain workS : ∀ t : State, t.gpr sb = s.gpr sb → workR t = workR s := fun t h => by simp only [workR, h]
  obtain schedWork : (⟨S, 128⟩ : Region).Disjoint (workR s) :=
    hsep.sub_right (Region.sub_prefix (by unfold scratchSlots; omega_using []))
  -- `G` of the sixteen
  obtain ⟨t2, e2, g2, keep2, room2, masks2, rd2, wr2, sp2, regs2, f2⟩ := g16_lanes hi.room hi.masks
  obtain sb_2 : t2.gpr sb = s.gpr sb := (regs2 _ (by decide)).trans hi.sb
  obtain a1_2 : t2.gpr .a1 = S + BitVec.ofNat 64 (64 * c) := (regs2 _ (by decide)).trans hi.a1
  obtain out2 : (outR t2 0).Disjoint (scratchR t2) := by
    rw [scrS t2 sb_2]; simp only [outR, a1_2, Nat.mul_zero]; rw [BitVec.add_zero]
    exact hsep.sub_left (Offset.sub_base _ (by omega_using [hc]))
  -- the copy
  obtain ⟨t3, e3, v3, g3, rd3, wr3, sp3, f3⟩ := keyStore_ok 0 (by decide) room2
    (fun w hw => by
      rw [a1_2, wr2, hi.wr, Offset.add_add]
      exact ⟨_, hin, Offset.contains_base _ (by omega_using [hc, hw]) (by omega_using [hc, hw])⟩) out2 16 (Nat.le_refl _)
  obtain ⟨t4, e4, a1_4', a4_4', g4, m4, rd4, wr4, sp4⟩ := halfTail_ok t3
  obtain G4 : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .a1 → r ≠ .a4 → t4.gpr r = t2.gpr r := fun r a b c' d =>
    by rw [g4 r c' d, g3 r a b]
  obtain sb_4 : t4.gpr sb = s.gpr sb := by rw [G4 _ (by decide) (by decide) (by decide) (by decide), sb_2]
  obtain a4_4 : t4.gpr .a4 = BitVec.ofNat 64 (2 - (c + 1)) := by
    rw [a4_4', g3 _ (by decide) (by decide), regs2 _ (by decide), hi.a4, Offset.ofNat_sub_ofNat (by omega_using [hc])]
    congr 1
  obtain a1_4 : t4.gpr .a1 = S + BitVec.ofNat 64 (64 * (c + 1)) := by
    rw [a1_4', g3 _ (by decide) (by decide), a1_2, Offset.add_add, show 64 * c + 64 = 64 * (c + 1) by omega_using []]
  obtain ev4 : isa.eval (.nonzero .a4) t4 = some (decide (c = 0)) := by
    rw [RISCV64.Steps.eval_nonzero, a4_4]
    congr 1
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
          simp only [List.mem_singleton] at hr; subst hr; simp only [outR, a1_2, Nat.mul_zero]
          rw [BitVec.add_zero]
          exact Offset.disjoint _ (Or.inl (by omega_using [hlo])) (by omega_using [hc, hi']) (by omega_using [hc])),
        lvS t t2 _ f2 i (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [workS t hi.sb]
          exact schedWork.sub_left (Offset.sub_base _ (by omega_using [hc, hi']))), hi.done i hlo]
    · obtain ⟨w, rfl⟩ : ∃ w, i = 16 * c + w := ⟨i - 16 * c, by omega_using [hlo]⟩
      have := v3 w (by omega_using [hi'])
      rw [a1_2, Offset.add_add, show 64 * c + 4 * (0 + w) = 4 * (16 * c + w) by omega_using []] at this
      rw [this, g2 w (by omega_using [hi']), hi.cur w (by omega_using [hi'])]
  obtain frame4 : Frame [workR s, ⟨S, 128⟩] s.mem t4.mem := by
    rw [m4]
    refine (hi.frame.trans (f2.sub ?_)).trans (f3.sub ?_)
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact ⟨workR s, List.mem_cons_self, by rw [workS t hi.sb]; exact fun _ h => h⟩
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
      simp only [outR, a1_2, Nat.mul_zero]; rw [BitVec.add_zero]
      exact Offset.sub_base _ (by omega_using [hc])
  obtain room4 : Room t4 := room_congr hi.room (sb_4.trans hi.sb.symm) (by rw [wr4, wr3, wr2, hi.wr])
  obtain masks4 : Masks t4 := by
    refine masks2.frame' (by rw [G4 _ (by decide) (by decide) (by decide) (by decide)])
      (G4 _ (by decide) (by decide) (by decide) (by decide)) (by rw [m4]; exact f3) fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact (out2.sub_right (masksR_sub t2)).symm
  obtain regs4 : ∀ r ∈ [Reg.ra, .a0, .a2, .a3, .a5], t4.gpr r = s.gpr r := by
    intro r hr
    obtain hn : r ≠ .t0 ∧ r ≠ .t1 ∧ r ≠ .a1 ∧ r ≠ .a4 ∧ r ∉ g16Writes := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [G4 r hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1, regs2 r hn.2.2.2.2, hi.regs r hr]
  refine WP.seq (WP.of_runBlock ⟨t4, runBlock_trans (runBlock_trans e2 e3) e4, ?_⟩)
  refine WP.ite (decide (c = 0)) ev4 (fun hb => ?_) (fun hb => ?_)
  · -- the second sixteen inputs
    obtain hc0 : c = 0 := by simpa using hb
    subst hc0
    obtain ⟨t5, e5, room5, v5, f5, rd5, wr5, sp5, g5⟩ := keyMove_ok room4
    refine WP.of_runBlock ⟨t5, e5, .inr ⟨?_, 1, by omega_using [], 1, by omega_using [], rfl, ?_⟩⟩
    · rw [RISCV64.Steps.eval_nonzero, g5 _ (by decide) (by decide), a4_4]
      decide
    obtain sb_5 : t5.gpr sb = s.gpr sb := (g5 _ (by decide) (by decide)).trans sb_4
    obtain workF : Frame [workR s] t4.mem t5.mem := by
      refine f5.sub fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨workR s, List.mem_cons_self, by rw [← workS t4 sb_4]; exact arraysR_sub_work t4⟩
    refine ⟨room5, masks4.frame (g5 _ (by decide) (by decide)) (g5 _ (by decide) (by decide))
        (by rw [workS t4 sb_4]; exact workF), sb_5,
      by rw [g5 _ (by decide) (by decide), a1_4], by rw [g5 _ (by decide) (by decide), a4_4],
      fun r hr => by
        rw [g5 r (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
                     rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
          (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
              rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide), regs4 r hr],
      fun w hw => ?_, fun h => absurd h (by decide), fun i hi' => ?_, by rw [rd5, rd4, rd3, rd2, hi.rd],
      by rw [wr5, wr4, wr3, wr2, hi.wr], by rw [sp5, sp4, sp3, sp2, hi.sp],
      frame4.trans (workF.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩)⟩
    · rw [v5 _ (by decide) w hw, show newVal spMove (tSlot 0) (fun k' => lv t4 k' w) = lv t4 uSlot w from rfl,
        show lv t4 uSlot w = lv t3 uSlot w by
          simp only [lv, laneA, m4, g4 _ (show sb ≠ .a1 by decide) (show sb ≠ .a4 by decide)],
        lv_frame (g3 _ (by decide) (by decide)) f3 out2 (by decide) hw, keep2 uSlot (by decide) (by decide) w hw,
        hi.next rfl w hw]
    · rw [lvS t4 t5 _ workF i (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact schedWork.sub_left (Offset.sub_base _ (by omega_using [hi'])))]
      exact done4 i hi'
  · -- the end
    obtain hc1 : c = 1 := by simp at hb; omega_using [hc, hb]
    subst hc1
    refine WP.block_nil (.inl ⟨?_, hQ t4 done4 regs4 (by rw [rd4, rd3, rd2, hi.rd])
      (by rw [wr4, wr3, wr2, hi.wr]) (by rw [sp4, sp3, sp2, hi.sp]) frame4⟩)
    rw [RISCV64.Steps.eval_nonzero, a4_4]
    decide

end VG.Proof.Seed.RISCV64

end

end


/-!
# Key expansion on RISC-V

As on PPC64LE (`Proof/Seed/PPC64LE/Key.lean`): `expandKey_ok`: after the
prologue (`Setup.lean`), `expandKey` loads the key (`keyLoad_ok`: its two
big-endian doublewords are `Key0 || Key1` and `Key2 || Key3`), computes the
schedule (`keyPre_ok`, `keyHalves_wp`) and restores the registers.
-/

@[expose] public section

namespace VG.Proof.Seed.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Impl.Seed.RISCV64 VG.Proof.Seed
open VG.Impl.Aes.RISCV64 (sb)

theorem be64_bytes (b0 b1 b2 b3 b4 b5 b6 b7 : Byte) :
    (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7 : BitVec 64) =
      ((b0 ++ b1 ++ b2 ++ b3 : BitVec 32) ++ (b4 ++ b5 ++ b6 ++ b7 : BitVec 32)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append]
  (repeat' split) <;> first | rfl | omega | (congr 1; omega)

/-- The big-endian doubleword of a block's bytes `off … off + 7`: two of its words. -/
theorem be64_key (m : Mem) (p : Addr) {off : Nat} (ho : off ≤ 8) :
    ByteLoad.be64 m p off =
      Spec.Seed.wordAt (Spec.Seed.blockAt m p) off ++ Spec.Seed.wordAt (Spec.Seed.blockAt m p) (off + 4) := by
  obtain hg : ∀ i < 16, (Spec.Seed.blockAt m p).getD i 0 = m (p + BitVec.ofNat 64 i) := fun i hi => by
    rw [vector_getD _ _ hi]; simp only [Spec.Seed.blockAt, Vector.getElem_ofFn]
  simp only [ByteLoad.be64, Spec.Seed.wordAt, hg off (by omega_using [ho]), hg (off + 1) (by omega_using [ho]),
    hg (off + 2) (by omega_using [ho]), hg (off + 3) (by omega_using [ho]), hg (off + 4) (by omega_using [ho]),
    hg (off + 4 + 1) (by omega_using [ho]), hg (off + 4 + 2) (by omega_using [ho]), hg (off + 4 + 3) (by omega_using [ho])]
  rw [be64_bytes]

/-- What key expansion needs: the scratch buffer and the schedule writable,
the key readable, apart from each other. -/
structure KeyPre (s : State) : Prop where
  scrAl : (s.gpr .a2).toNat % 8 = 0
  scratch : (⟨s.gpr .a2, 8 * scratchSlots⟩ : Region) ∈ s.wr
  schedIn : (⟨s.gpr .a1, 128⟩ : Region) ∈ s.wr
  keyIn : (⟨s.gpr .a0, 16⟩ : Region) ∈ s.rd
  keySched : (⟨s.gpr .a0, 16⟩ : Region).Disjoint ⟨s.gpr .a1, 128⟩
  keyBuf : (⟨s.gpr .a0, 16⟩ : Region).Disjoint ⟨s.gpr .a2, 8 * scratchSlots⟩
  schedBuf : (⟨s.gpr .a1, 128⟩ : Region).Disjoint ⟨s.gpr .a2, 8 * scratchSlots⟩

structure KeyPost (s s' : State) : Prop where
  saved : ∀ r ∈ RISCV64.preserved, s'.gpr r = s.gpr r
  ra : s'.gpr .ra = s.gpr .ra
  sched : Spec.Seed.scheduleAt s'.mem (s.gpr .a1) = Spec.Seed.expandKey (Spec.Seed.blockAt s.mem (s.gpr .a0))
  frame : Frame [⟨s.gpr .a2, 8 * scratchSlots⟩, ⟨s.gpr .a1, 128⟩] s.mem s'.mem

theorem expandKey_eq_code : expandKey = .seq (.block (prologue .a2 ++
    (Impl.Words.RISCV64.loadBE64 keyA .t0 .a0 0 ++ Impl.Words.RISCV64.loadBE64 keyB .t0 .a0 8) ++ keyPre))
    (.seq (.loop keyHalf (.nonzero .a4)) (.block seedRestore)) := by
  simp only [expandKey, keyPre, keyLoad, List.append_assoc]
  rfl

theorem expandKey_ok {s : State} (h : KeyPre s) : WP isa expandKey s (KeyPost s) := by
  let key := Spec.Seed.blockAt s.mem (s.gpr .a0)
  let X := s.gpr .a2
  rw [expandKey_eq_code]
  apply WP.seq
  rw [WP.block_append_iff (M := isa), WP.block_append_iff (M := isa)]
  refine WP.mono (prologue_ok h.scrAl ⟨_, h.scratch, Region.contains_self _ _⟩) fun s₁ P => ?_
  -- the key
  have G₁ : ∀ r, r ≠ sb → r ≠ kb → r ≠ .t0 → r ≠ .t1 → s₁.gpr r = s.gpr r := P.regs
  obtain a0₁ : s₁.gpr .a0 = s.gpr .a0 := G₁ _ (by decide) (by decide) (by decide) (by decide)
  obtain hkey : ∀ k, k + 8 ≤ 16 → InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .a0 + BitVec.ofNat 64 k) 8 := fun k hk => by
    rw [P.rd, P.wr, a0₁]
    exact ⟨_, List.mem_append_left _ h.keyIn, Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])⟩
  obtain key₁ : ∀ off, off ≤ 8 → ByteLoad.be64 s₁.mem (s₁.gpr .a0) off =
      Spec.Seed.wordAt key off ++ Spec.Seed.wordAt key (off + 4) := fun off ho => by
    rw [be64_key _ _ ho, a0₁]
    have : Spec.Seed.blockAt s₁.mem (s.gpr .a0) = key := blockAt_frame P.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.keyBuf
    rw [this]
  rw [WP.block_append_iff (M := isa)]
  refine WP.mono (ByteLoad.loadBE64_ok (s := s₁) (d := keyA) (tmp := .t0) (n := .a0) (off := 0)
    (by decide) (by decide) (by decide) (by decide) (hkey 0 (by decide))) fun s₂ e₂ => ?_
  obtain a0₂ : s₂.gpr .a0 = s.gpr .a0 := by
    rw [e₂, gpr_write_of_ne _ _ (show ¬ Reg.a0 = keyA by decide), gpr_write_of_ne _ _ (by decide), a0₁]
  obtain rw₂ : s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by rw [e₂]; exact ⟨rfl, rfl⟩
  refine WP.mono (ByteLoad.loadBE64_ok (s := s₂) (d := keyB) (tmp := .t0) (n := .a0) (off := 8)
    (by decide) (by decide) (by decide) (by decide)
    (by rw [rw₂.1, rw₂.2, a0₂, ← a0₁]; exact hkey 8 (by decide))) fun s₃ e₃ => ?_
  obtain m₃ : s₃.mem = s₁.mem := by rw [e₃, e₂]; rfl
  obtain G₃ : ∀ r, r ≠ .t0 → r ≠ .t5 → r ≠ .t6 → s₃.gpr r = s₁.gpr r := fun r a b c => by
    rw [e₃, gpr_write_of_ne _ _ (show ¬ r = keyB from c), gpr_write_of_ne _ _ a, e₂,
      gpr_write_of_ne _ _ (show ¬ r = keyA from b), gpr_write_of_ne _ _ a]
  obtain h3 : s₃.gpr .t5 = kx (keyWords key 0) := by
    rw [e₃, gpr_write_of_ne _ _ (show ¬ Reg.t5 = keyB by decide), gpr_write_of_ne _ _ (by decide), e₂,
      show Reg.t5 = keyA from rfl, gpr_write_self, key₁ 0 (by decide)]
    rfl
  obtain h4 : s₃.gpr .t6 = ky (keyWords key 0) := by
    rw [e₃, show Reg.t6 = keyB from rfl, gpr_write_self, a0₂, ← a0₁,
      show s₂.mem = s₁.mem by rw [e₂]; rfl, key₁ 8 (by decide)]
    rfl
  obtain sb₃ : s₃.gpr sb = X := by rw [G₃ _ (by decide) (by decide) (by decide), P.base]
  obtain rd₃ : s₃.rd = s.rd := by rw [e₃, e₂]; exact P.rd
  obtain wr₃ : s₃.wr = s.wr := by rw [e₃, e₂]; exact P.wr
  obtain sp₃ : s₃.sp = s.sp := by rw [e₃, e₂]; exact P.sp
  obtain room₃ : Room s₃ := room_congr P.room (by rw [G₃ _ (by decide) (by decide) (by decide)])
    (by rw [wr₃, P.wr])
  obtain masks₃ : Masks s₃ := P.masks.frame (G₃ _ (by decide) (by decide) (by decide))
    (G₃ _ (by decide) (by decide) (by decide)) (by rw [m₃]; exact Frame.refl _ _)
  -- the rounds, and the count of halves
  refine WP.of_runBlock ?_
  obtain ⟨s₅, e₅, room₅, cur₅, next₅, a4₅, g₅, rd₅, wr₅, sp₅, f₅⟩ := keyPre_ok key room₃ h3 h4
  refine ⟨s₅, e₅, ?_⟩
  obtain G₅ : ∀ r ∈ [Reg.ra, .a0, .a1, .a2, .a3, .a5], s₅.gpr r = s₃.gpr r := fun r hr => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain sb₅ : s₅.gpr sb = X := (G₅ _ (by simp [sb])).trans sb₃
  obtain scr₅ : scratchR s₅ = ⟨X, 8 * scratchSlots⟩ := by simp only [scratchR, sb₅]
  obtain masks₅ : Masks s₅ := masks₃.frame (G₅ _ (by simp [sb])) (G₅ _ (by simp [kb]))
    (scratch_of_arrays f₅)
  obtain a1₅ : s₅.gpr .a1 = s.gpr .a1 := by
    rw [G₅ _ (by simp), G₃ _ (by decide) (by decide) (by decide), G₁ _ (by decide) (by decide) (by decide)
      (by decide)]
  obtain h0 : HalfInv key s₅ (s.gpr .a1) 0 s₅ :=
    ⟨room₅, masks₅, rfl, by rw [a1₅]; exact (BitVec.add_zero _).symm, a4₅, fun _ _ => rfl,
      fun w hw => by rw [cur₅ w hw, Nat.mul_zero, Nat.zero_add], fun _ => next₅, fun i hi => by omega,
      rfl, rfl, rfl, Frame.refl _ _⟩
  refine WP.seq (keyHalves_wp key (by rw [wr₅, wr₃]; exact h.schedIn) (by rw [scr₅]; exact h.schedBuf) h0
    fun s₆ v₆ regs₆ rd₆ wr₆ sp₆ f₆ => ?_)
  obtain sb₆ : s₆.gpr sb = X := (regs₆ _ (by simp [sb])).trans sb₅
  obtain room₆ : Room s₆ := room_congr room₅ (regs₆ _ (by simp [sb])) wr₆
  obtain workR₅ : workR s₅ = ⟨X, 8 * 104⟩ := by simp only [workR, sb₅]
  rw [workR₅] at f₆
  obtain arr₃ : Region.Sub (arraysR s₃) ⟨X, 8 * 104⟩ := by
    have := arraysR_sub_work s₃; simp only [workR, sb₃] at this; exact this
  obtain f₃₆ : Frame [⟨X, 8 * 104⟩, ⟨s.gpr .a1, 128⟩] s₃.mem s₆.mem :=
    (f₅.sub fun r hr => ⟨_, List.mem_cons_self, by simp at hr; subst hr; exact arr₃⟩).trans f₆
  obtain sv₆ : Spill.Saved X s.gpr savedOffs s₆.mem := by
    obtain sv₃ : Spill.Saved X s.gpr savedOffs s₃.mem := by rw [m₃]; exact P.saved
    refine sv₃.frame_in savedOffs_range f₃₆ fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint_base _ (by omega_using []) (by omega_using [])
    · exact (h.schedBuf.sub_right (Offset.sub_base _ (by unfold scratchSlots; omega_using []))).symm
  rw [seedRestore_eq]
  refine WP.mono (Spill.restore_wp (B := X) (by rw [← sb₆]; exact room₆.1) sb₆ savedOffs_ho
    savedOffs_restorable (fun q hq => room₆.rw ?_) sv₆) fun s' R => ?_
  · rw [← sb₆]
    have := savedOffs_range q hq
    exact Offset.contains_base _ (by unfold scratchSlots; omega_using [this]) (by omega_using [this])
  obtain frame : Frame [⟨X, 8 * scratchSlots⟩, ⟨s.gpr .a1, 128⟩] s.mem s'.mem := by
    rw [R.mem]
    refine (P.frame.mono (by simp [X])).trans ?_
    rw [← m₃]
    refine f₃₆.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by unfold scratchSlots; omega_using [])⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  refine ⟨fun r hr => ?_, ?_, ?_, frame⟩
  · rw [← savedOffs_regs] at hr
    exact R.gpr_of (Or.inl hr)
  · rw [R.other _ (by decide), regs₆ _ (by simp), G₅ _ (by simp), G₃ _ (by decide) (by decide) (by decide),
      G₁ _ (by decide) (by decide) (by decide) (by decide)]
  · rw [Proof.Seed.expandKey_eq]
    apply Vector.ext
    intro i hi
    rw [scheduleAt_readW _ _ i hi, R.mem, v₆ i hi, Vector.getElem_ofFn]

end VG.Proof.Seed.RISCV64
