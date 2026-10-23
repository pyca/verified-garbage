module
public import VerifiedGarbage.Proof.Seed.PPC64LE.Lanes

import VerifiedGarbage.Proof.Seed.PPC64LE.Rounds
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Copying blocks into the arrays and back

As on x86-64: `copyIn_loop`: the loop of `copyInBody` copies `m` blocks from
`p` into lanes `0 … m - 1` of the arrays, each word byte-reversed (`bw`, a
block's big-endian word). `copyOut_loop`: the loop of `copyOutBody` copies
them back, `R` first.
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.PPC64LE.RegUpd VG.Impl.Seed.PPC64LE

-- The copies share one set of rewrites, not all of which each uses.
set_option linter.unusedSimpArgs false

/-- Word `w` of block `b` from `p`, big-endian. -/
def bw (m : Mem) (p : Addr) (b w : Nat) : BitVec 32 :=
  rev32 (m.readW (p + BitVec.ofNat 64 (16 * b + 4 * w)) 32)

theorem mem_arrA_of {w : Nat} (hw : w < 4) : arrSlot w ∈ arrays := by
  rcases (show w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 by omega) with rfl | rfl | rfl | rfl <;> decide

/-- What the copy into the arrays needs. -/
structure CopyPre (s : State) (p : Addr) (m : Nat) : Prop where
  room : Room s
  le : 1 ≤ m ∧ m ≤ 16
  read : ∀ b < m, ∀ w < 4, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (16 * b + 4 * w)) 4
  sep : Region.Disjoint ⟨p, 16 * m⟩ (arraysR s)

/-- After `j` blocks of the copy in. -/
structure CopyInInv (s₀ : State) (p : Addr) (m j : Nat) (s : State) : Prop where
  le : j ≤ m
  r6 : s.gpr .r6 = p + BitVec.ofNat 64 (16 * j)
  r7 : s.gpr .r7 = s₀.gpr .r8 + BitVec.ofNat 64 (4 * j)
  r10 : s.gpr .r10 = BitVec.ofNat 64 (m - j)
  lanes : ∀ w < 4, ∀ b < j, lv s (arrSlot w) b = bw s₀.mem p b w
  frame : Frame [arraysR s₀] s₀.mem s.mem
  regs : ∀ r, r ≠ .r9 → r ≠ .r7 → r ≠ .r10 → r ≠ .r6 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem writeW32_byte (m : Mem) (a : Addr) (v : BitVec 32) {j : Nat} (hj : j < 4) :
    (m.writeW a v) (a + BitVec.ofNat 64 j) = v.extractLsb' (8 * j) 8 := by
  simp only [Mem.writeW, Mem.write, Mem.sub_ofNat_toNat a (show j < 2 ^ 64 by omega),
    show j < 32 / 8 by omega, ite_true, BitVec.setWidth_eq]

/-- The copy of word `w` of a block. -/
def inWord (w : Nat) : List Instr :=
  [.li .r9 (4 * w), .loadRev .w .r9 .r6 .r9, .store .w .r9 .r7 (8 * arrSlot w)]

theorem copyInBody_eq : copyInBody = inWord 0 ++ (inWord 1 ++ (inWord 2 ++ (inWord 3 ++
    ([.addi .r6 .r6 16, .addi .r7 .r7 4, .subi .r10 .r10 1] : List Instr)))) := rfl

theorem arr_off (w j : Nat) (b : Addr) :
    b + BitVec.ofNat 64 (4 * j) + BitVec.ofNat 64 (8 * arrSlot w) = b + BitVec.ofNat 64 (8 * arrSlot w + 4 * j) := by
  rw [Offset.add_add, Nat.add_comm]

theorem arr_ok {w : Nat} (hw : w < 4) : 8 * arrSlot w % 4 = 0 ∧ 8 * arrSlot w < 16384 := by
  unfold arrSlot; omega

/-- One word of a block into its lane. -/
theorem copyInWord_ok {w j : Nat} (hw : w < 4) (hj : j < 16) (s : State) (h : Room s)
    (hrb : s.gpr .r7 = s.gpr .r8 + BitVec.ofNat 64 (4 * j))
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .r6 + BitVec.ofNat 64 (4 * w)) 4) :
    ∃ s', runBlock isa (inWord w) s = some s' ∧
      s'.mem = s.mem.writeW (laneA s (arrSlot w) j)
        (rev32 (s.mem.readW (s.gpr .r6 + BitVec.ofNat 64 (4 * w)) 32)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ≠ .r9 → s'.gpr r = s.gpr r) := by
  have hL : arrSlot w ∈ arrays := mem_arrA_of hw
  have hla : s.gpr .r7 + BitVec.ofNat 64 (8 * arrSlot w) = laneA s (arrSlot w) j := by
    rw [hrb, arr_off _ _]; rfl
  unfold inWord
  let v := s.mem.readW (s.gpr .r6 + BitVec.ofNat 64 (4 * w)) 32
  let s1 := s.write .r9 (BitVec.ofNat 64 (4 * w))
  let s2 := s1.write .r9 ((rev32 v).setWidth 64)
  have h6 : s1.gpr .r6 = s.gpr .r6 := gpr_write_of_ne _ _ (by decide)
  have h9 : s1.gpr .r9 = BitVec.ofNat 64 (4 * w) := gpr_write_self _ _ _
  have e1 : exec (.li .r9 (4 * w)) s = some s1 := exec_li (by omega)
  have e2 : exec (.loadRev .w .r9 .r6 .r9) s1 = some s2 := by
    rw [exec_loadRev_w (by decide) (by rw [h6, h9]; exact hr), h6, h9]; rfl
  have h4 : s2.gpr .r7 = s.gpr .r7 := by simp [s2, s1, gpr_write]
  have e3 := exec_store_w (s := s2) (t := .r9) (n := .r7) (off := 8 * arrSlot w) (by decide)
    (by have := arr_ok hw; omega) (by rw [h4, hla]; simp only [s2, s1, wr_write]; exact lane_wr h hL hj)
  rw [runBlock_cons, e1, runStep_some, runBlock_cons, e2, runStep_some, runBlock_cons, e3, runStep_some,
    runBlock_nil]
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, fun r hr => ?_⟩
  · show s2.mem.writeW _ _ = _
    rw [h4, hla]
    simp [s2, s1, gpr_write, mem_write, setWidth_setWidth_32, v]
  · simp [s2, s1, gpr_write, hr]

/-- The copy of one block into lane `j`, as writes of the block's words. -/
def inSpec (m : Mem) (q : Addr) : LaneSpec :=
  (List.range 4).map fun w => (arrSlot w, fun _ => rev32 (m.readW (q + BitVec.ofNat 64 (4 * w)) 32))

theorem inSpec_dests (m : Mem) (q : Addr) : ∀ kv ∈ inSpec m q, kv.1 ∈ arrays := by
  intro kv hkv
  simp only [inSpec, List.mem_map, List.mem_range] at hkv
  obtain ⟨w, hw, rfl⟩ := hkv
  exact mem_arrA_of hw

theorem copyInBody_ok {j : Nat} (hj : j < 16) (s : State) (h : Room s)
    (hrb : s.gpr .r7 = s.gpr .r8 + BitVec.ofNat 64 (4 * j))
    (hr : ∀ w < 4, InRegions (s.rd ++ s.wr) (s.gpr .r6 + BitVec.ofNat 64 (4 * w)) 4)
    (hsep : ∀ w < 4, Region.Disjoint ⟨s.gpr .r6 + BitVec.ofNat 64 (4 * w), 4⟩ (arraysR s)) :
    ∃ s', runBlock isa copyInBody s = some s' ∧
      s'.mem = laneWrites s (inSpec s.mem (s.gpr .r6)) j ∧
      s'.gpr .r6 = s.gpr .r6 + 16 ∧ s'.gpr .r7 = s.gpr .r7 + 4 ∧
      s'.gpr .r10 = s.gpr .r10 - 1 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .r9 → r ≠ .r7 → r ≠ .r10 → r ≠ .r6 → s'.gpr r = s.gpr r) := by
  -- The block's words keep their values while the lanes are written.
  have hkeep : ∀ (t : State), Frame [arraysR s] s.mem t.mem → ∀ w < 4,
      t.mem.readW (s.gpr .r6 + BitVec.ofNat 64 (4 * w)) 32 =
        s.mem.readW (s.gpr .r6 + BitVec.ofNat 64 (4 * w)) 32 := by
    intro t ht w hw
    refine ht.readW (Region.contains_self _ _) ?_ (by decide)
    intro r hr'; simp only [List.mem_singleton] at hr'; subst hr'; exact hsep w hw
  obtain ⟨s1, e1, m1, rd1, wr1, sp1, g1⟩ := copyInWord_ok (w := 0) (by decide) hj s h hrb (hr 0 (by decide))
  have h1 : Room s1 := room_congr h (g1 _ (by decide)) wr1
  obtain ⟨s2, e2, m2, rd2, wr2, sp2, g2⟩ := copyInWord_ok (w := 1) (by decide) hj s1 h1
    (by rw [g1 _ (by decide), g1 _ (by decide), hrb]) (by rw [rd1, wr1, g1 _ (by decide)]; exact hr 1 (by decide))
  have h2 : Room s2 := room_congr h1 (g2 _ (by decide)) wr2
  obtain ⟨s3, e3, m3, rd3, wr3, sp3, g3⟩ := copyInWord_ok (w := 2) (by decide) hj s2 h2
    (by rw [g2 _ (by decide), g2 _ (by decide), g1 _ (by decide), g1 _ (by decide), hrb])
    (by rw [rd2, wr2, rd1, wr1, g2 _ (by decide), g1 _ (by decide)]; exact hr 2 (by decide))
  have h3 : Room s3 := room_congr h2 (g3 _ (by decide)) wr3
  obtain ⟨s4, e4, m4, rd4, wr4, sp4, g4⟩ := copyInWord_ok (w := 3) (by decide) hj s3 h3
    (by rw [g3 _ (by decide), g3 _ (by decide), g2 _ (by decide), g2 _ (by decide), g1 _ (by decide),
      g1 _ (by decide), hrb])
    (by rw [rd3, wr3, rd2, wr2, rd1, wr1, g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)];
        exact hr 3 (by decide))
  let s5 := s4.write .r6 (s4.gpr .r6 + BitVec.ofNat _ 16)
  let s6 := s5.write .r7 (s5.gpr .r7 + BitVec.ofNat _ 4)
  let s7 := s6.write .r10 (s6.gpr .r10 - BitVec.ofNat _ 1)
  have hrun : runBlock isa copyInBody s = some s7 := by
    rw [copyInBody_eq]
    rw [runBlock_append, e1, Option.bind_some, runBlock_append, e2, Option.bind_some, runBlock_append, e3,
      Option.bind_some, runBlock_append, e4, Option.bind_some, runBlock_cons, exec_addi' (n := .r6) (by decide),
      runStep_some, runBlock_cons, exec_addi' (n := .r7) (by decide), runStep_some, runBlock_cons,
      exec_subi' (n := .r10) (by decide), runStep_some, runBlock_nil]
  -- Registers through the words.
  have r9s : ∀ t ∈ [s1, s2, s3, s4], t.gpr .r8 = s.gpr .r8 := by
    intro t ht
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact g1 _ (by decide)
    · rw [g2 _ (by decide), g1 _ (by decide)]
    · rw [g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
    · rw [g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
  have r10s : ∀ t ∈ [s1, s2, s3, s4], t.gpr .r6 = s.gpr .r6 := by
    intro t ht
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact g1 _ (by decide)
    · rw [g2 _ (by decide), g1 _ (by decide)]
    · rw [g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
    · rw [g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
  have lA : ∀ t ∈ [s1, s2, s3, s4], ∀ k, laneA t k j = laneA s k j := by
    intro t ht k; simp only [laneA, r9s t ht]
  -- Memory.
  let v (w : Nat) := rev32 (s.mem.readW (s.gpr .r6 + BitVec.ofNat 64 (4 * w)) 32)
  have f1 : Frame [arraysR s] s.mem s1.mem := by
    rw [m1]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (lane_inArrays (mem_arrA_of (by decide)) hj s)
  have f2 : Frame [arraysR s] s.mem s2.mem := by
    rw [m2, lA s1 (by simp)]; exact f1.writeW List.mem_cons_self _ (lane_inArrays (mem_arrA_of (by decide)) hj s)
  have f3 : Frame [arraysR s] s.mem s3.mem := by
    rw [m3, lA s2 (by simp)]; exact f2.writeW List.mem_cons_self _ (lane_inArrays (mem_arrA_of (by decide)) hj s)
  have mm : s4.mem = (((s.mem.writeW (laneA s (arrSlot 0) j) (v 0)).writeW (laneA s (arrSlot 1) j) (v 1)).writeW
      (laneA s (arrSlot 2) j) (v 2)).writeW (laneA s (arrSlot 3) j) (v 3) := by
    rw [m4, lA s3 (by simp), r10s s3 (by simp), hkeep s3 f3 3 (by decide), m3, lA s2 (by simp),
      r10s s2 (by simp), hkeep s2 f2 2 (by decide), m2, lA s1 (by simp), r10s s1 (by simp),
      hkeep s1 f1 1 (by decide), m1]
  have r10_4 := r10s s4 (by simp)
  have rbx_4 : s4.gpr .r7 = s.gpr .r7 := by
    rw [g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
  have rcx_4 : s4.gpr .r10 = s.gpr .r10 := by
    rw [g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
  refine ⟨s7, hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_⟩
  · simp only [s7, s6, s5, mem_write]
    rw [mm]
    simp only [laneWrites, inSpec, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.foldl_cons, List.foldl_nil, List.singleton_append, List.cons_append,
      List.map_cons]
    rfl
  · simp [s7, s6, s5, gpr_write, r10_4]
  · simp [s7, s6, s5, gpr_write, rbx_4]
  · simp [s7, s6, s5, gpr_write, rcx_4]
  · simp only [s7, s6, s5, rd_write, rd4, rd3, rd2, rd1]
  · simp only [s7, s6, s5, wr_write, wr4, wr3, wr2, wr1]
  · simp only [s7, s6, s5, sp_write, sp4, sp3, sp2, sp1]
  · simp only [s7, s6, s5, gpr_write, h3, h2, h4, ↓reduceIte]
    rw [g4 _ h1, g3 _ h1, g2 _ h1, g1 _ h1]

theorem cnt_ne_zero {k : Nat} (h1 : 2 ≤ k) (h2 : k ≤ 16) :
    (BitVec.ofNat 64 k - 1 != 0) = true := by
  simp only [bne_iff_ne, ne_eq]
  intro h0
  have := congrArg BitVec.toNat h0
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl,
    show (0 : BitVec 64).toNat = 0 from rfl, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)] at this
  omega

theorem cnt_sub1 {k : Nat} (h1 : 1 ≤ k) (h2 : k ≤ 16) : BitVec.ofNat 64 k - 1 = BitVec.ofNat 64 (k - 1) :=
  r7_sub k h1 h2

theorem copyIn_loop {s₀ : State} {p : Addr} {m : Nat} (hpre : CopyPre s₀ p m) :
    ∀ k s, CopyInInv s₀ p m (m - k) s → 1 ≤ k → k ≤ m →
      WP isa (.loop (.block copyInBody) (.nonzero .d .r10)) s (fun s' => CopyInInv s₀ p m m s') := by
  intro k s hs hk1 hkm
  refine WP.loop (M := isa) (fun k t => CopyInInv s₀ p m (m - k) t ∧ 1 ≤ k ∧ k ≤ m) ?_ k s ⟨hs, hk1, hkm⟩
  intro k t ⟨inv, hk1, hkm⟩
  have hm16 := hpre.le.2
  let j := m - k
  have hj : j < 16 := by omega
  have hr9 : t.gpr .r8 = s₀.gpr .r8 := inv.regs _ (by decide) (by decide) (by decide) (by decide)
  have hroom : Room t := room_congr hpre.room hr9 inv.wr
  have hrb : t.gpr .r7 = t.gpr .r8 + BitVec.ofNat 64 (4 * j) := by rw [inv.r7, hr9]
  have hdata : ∀ w < 4, t.gpr .r6 + BitVec.ofNat 64 (4 * w) = p + BitVec.ofNat 64 (16 * j + 4 * w) := by
    intro w _; rw [inv.r6, Offset.add_add]
  have hr : ∀ w < 4, InRegions (t.rd ++ t.wr) (t.gpr .r6 + BitVec.ofNat 64 (4 * w)) 4 := by
    intro w hw; rw [hdata w hw, inv.rd, inv.wr]; exact hpre.read j (by omega) w hw
  have harr : arraysR t = arraysR s₀ := by simp [arraysR, hr9]
  have hsep : ∀ w < 4, Region.Disjoint ⟨t.gpr .r6 + BitVec.ofNat 64 (4 * w), 4⟩ (arraysR t) := by
    intro w hw
    rw [hdata w hw, harr]
    exact hpre.sep.sub_left (Offset.sub_base p (by omega))
  obtain ⟨t', ht', hmem, hr10, hrbx, hrcx, hrd, hwr, hsp, hregs⟩ := copyInBody_ok hj t hroom hrb hr hsep
  refine WP.of_runBlock ⟨t', ht', ?_⟩
  have hr9' : t'.gpr .r8 = t.gpr .r8 := hregs _ (by decide) (by decide) (by decide) (by decide)
  have inv' : CopyInInv s₀ p m (j + 1) t' := by
    refine ⟨by omega, ?_, ?_, ?_, fun w hw b hb => ?_, ?_, fun r h1 h2 h3 h4 => ?_, by rw [hsp, inv.sp],
      by rw [hrd, inv.rd], by rw [hwr, inv.wr]⟩
    · rw [hr10, inv.r6, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, Offset.add_add]; congr 2
    · rw [hrbx, inv.r7, show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_add]; congr 2
    · rw [hrcx, inv.r10, show m - j = k by omega, cnt_sub1 hk1 (by omega)]; congr 1; omega
    · have hl : lv t' (arrSlot w) b = (laneWrites t (inSpec t.mem (t.gpr .r6)) j).readW (laneA t (arrSlot w) b) 32 := by
        rw [← hmem]; simp only [lv, laneA, hr9']
      rw [hl, lv_laneWrites (inSpec_dests _ _) t (mem_arrA_of hw) (by omega) hj]
      by_cases hbj : b = j
      · subst hbj
        simp only [ite_true, newVal, inSpec, List.range_succ, List.range_zero, List.nil_append,
          List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, List.singleton_append,
          List.cons_append]
        rw [bw, ← hdata w hw]
        have hkeep : t.mem.readW (t.gpr .r6 + BitVec.ofNat 64 (4 * w)) 32 =
            s₀.mem.readW (t.gpr .r6 + BitVec.ofNat 64 (4 * w)) 32 := by
          refine inv.frame.readW (Region.contains_self _ _) ?_ (by decide)
          intro r hr'; simp only [List.mem_singleton] at hr'; subst hr'; rw [← harr]; exact hsep w hw
        rw [← hkeep]
        rcases (show w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 by omega) with rfl | rfl | rfl | rfl <;> simp [arrSlot]
      · rw [ite_eq_right hbj]; exact inv.lanes w hw b (by omega)
    · refine inv.frame.trans ?_
      have := laneWrites_frame (inSpec_dests t.mem (t.gpr .r6)) t (b := j) hj
      rw [← hmem, harr] at this; exact this
    · rw [hregs r h1 h2 h3 h4]; exact inv.regs r h1 h2 h3 h4
  by_cases hk : k = 1
  · subst hk
    left
    have hjm : j + 1 = m := by omega
    refine ⟨?_, hjm ▸ inv'⟩
    show some (t'.read .d .r10 != 0) = some false
    rw [show t'.read .d .r10 = t'.gpr .r10 from BitVec.setWidth_eq _, hrcx, inv.r10, show m - (m - 1) = 1 by omega]; rfl
  · right
    refine ⟨?_, k - 1, by omega, ⟨by simpa [show j + 1 = m - (k - 1) by omega] using inv', by omega, by omega⟩⟩
    show some (t'.read .d .r10 != 0) = some true
    rw [show t'.read .d .r10 = t'.gpr .r10 from BitVec.setWidth_eq _, hrcx, inv.r10, show m - (m - k) = k by omega, cnt_ne_zero (by omega) (by omega)]

/-! ## Copying out -/

/-- Byte `j` (in memory order) of a byte-swapped word is byte `3 - j` of the word. -/
theorem rev32_byte (x : BitVec 32) {j : Nat} (hj : j < 4) :
    (rev32 x).extractLsb' (8 * j) 8 = (x >>> (8 * (3 - j))).setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h4 := Proof.Seed.getLsbD_append4 (x.extractLsb' 0 8) (x.extractLsb' 8 8) (x.extractLsb' 16 8)
    (x.extractLsb' 24 8) hi
  have e : ((rev32 x).extractLsb' (8 * j) 8).getLsbD i = (rev32 x).getLsbD (8 * j + i) := by
    simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  rw [e]
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  unfold rev32
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
  · rw [h4.1]; simp [BitVec.getLsbD_extractLsb', hi]
  · rw [h4.2.1]; simp [BitVec.getLsbD_extractLsb', hi]
  · rw [h4.2.2.1]; simp [BitVec.getLsbD_extractLsb', hi]
  · rw [h4.2.2.2]; simp [BitVec.getLsbD_extractLsb', hi]

/-- A byte of the 4 bytes a 32-bit write writes. -/
theorem writeW32_at (m : Mem) (a : Addr) (v : BitVec 32) {d i : Nat} (h1 : d ≤ i) (h2 : i < d + 4)
    (hi : i < 2 ^ 64) :
    (m.writeW (a + BitVec.ofNat 64 d) v) (a + BitVec.ofNat 64 i) = v.extractLsb' (8 * (i - d)) 8 := by
  simp only [Mem.writeW, Mem.write, Offset.sub_toNat a h1 hi, show i - d < 32 / 8 by omega, ite_true,
    BitVec.setWidth_eq]

/-- A byte outside the 4 bytes a 32-bit write writes. -/
theorem writeW32_off (m : Mem) (a : Addr) (v : BitVec 32) {d i : Nat} (h : i < d ∨ d + 4 ≤ i)
    (hd : d + 4 ≤ 2 ^ 64) (hi : i < 2 ^ 64) :
    (m.writeW (a + BitVec.ofNat 64 d) v) (a + BitVec.ofNat 64 i) = m (a + BitVec.ofNat 64 i) := by
  apply Mem.write_apply
  have := Offset.sep a (d := i) (n := 1) (e := d) (k := 4) (by omega) (by omega) hd
  exact this _ (by simp)

/-- The four byte-swapped words `y` written from `a` are the block of their big-endian bytes. -/
theorem block_writes (m : Mem) (a : Addr) (y : Nat → BitVec 32) {i : Nat} (hi : i < 16) :
    ((((m.writeW (a + BitVec.ofNat 64 0) (rev32 (y 0))).writeW (a + BitVec.ofNat 64 4) (rev32 (y 1))).writeW
      (a + BitVec.ofNat 64 8) (rev32 (y 2))).writeW (a + BitVec.ofNat 64 12) (rev32 (y 3)))
      (a + BitVec.ofNat 64 i) = (y (i / 4) >>> (8 * (3 - i % 4))).setWidth 8 := by
  rcases (show i / 4 = 0 ∨ i / 4 = 1 ∨ i / 4 = 2 ∨ i / 4 = 3 by omega) with h | h | h | h
  · rw [writeW32_off _ _ _ (by omega) (by omega) (by omega), writeW32_off _ _ _ (by omega) (by omega) (by omega),
      writeW32_off _ _ _ (by omega) (by omega) (by omega), writeW32_at _ _ _ (by omega) (by omega) (by omega),
      rev32_byte _ (by omega), h]
    congr 3; omega
  · rw [writeW32_off _ _ _ (by omega) (by omega) (by omega), writeW32_off _ _ _ (by omega) (by omega) (by omega),
      writeW32_at _ _ _ (by omega) (by omega) (by omega), rev32_byte _ (by omega), h]
    congr 3; omega
  · rw [writeW32_off _ _ _ (by omega) (by omega) (by omega), writeW32_at _ _ _ (by omega) (by omega) (by omega),
      rev32_byte _ (by omega), h]
    congr 3; omega
  · rw [writeW32_at _ _ _ (by omega) (by omega) (by omega), rev32_byte _ (by omega), h]
    congr 3; omega

/-- The copy of word `w` of a block out: the lane loaded byte-reversed, and
stored. -/
def outWord (w : Nat) : List Instr :=
  [.li .r9 (8 * arrSlot ((w + 2) % 4)), .loadRev .w .r9 .r7 .r9, .store .w .r9 .r6 (4 * w)]

theorem copyOutBody_eq : copyOutBody = outWord 0 ++ (outWord 1 ++ (outWord 2 ++ (outWord 3 ++
    ([.addi .r6 .r6 16, .addi .r7 .r7 4, .subi .r10 .r10 1] : List Instr)))) := rfl

theorem copyOutWord_ok {w j : Nat} (hw : w < 4) (hj : j < 16) (s : State) (h : Room s)
    (hrb : s.gpr .r7 = s.gpr .r8 + BitVec.ofNat 64 (4 * j))
    (hwr : InRegions s.wr (s.gpr .r6 + BitVec.ofNat 64 (4 * w)) 4) :
    ∃ s', runBlock isa (outWord w) s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .r6 + BitVec.ofNat 64 (4 * w))
        (rev32 (lv s (arrSlot ((w + 2) % 4)) j)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ≠ .r9 → s'.gpr r = s.gpr r) := by
  have hw' : (w + 2) % 4 < 4 := Nat.mod_lt _ (by decide)
  have hL : arrSlot ((w + 2) % 4) ∈ arrays := mem_arrA_of hw'
  have hla : s.gpr .r7 + BitVec.ofNat 64 (8 * arrSlot ((w + 2) % 4)) = laneA s (arrSlot ((w + 2) % 4)) j := by
    rw [hrb, arr_off _ _]; rfl
  unfold outWord
  let s1 := s.write .r9 (BitVec.ofNat 64 (8 * arrSlot ((w + 2) % 4)))
  let s2 := s1.write .r9 ((rev32 (lv s (arrSlot ((w + 2) % 4)) j)).setWidth 64)
  have h7 : s1.gpr .r7 = s.gpr .r7 := gpr_write_of_ne _ _ (by decide)
  have h9 : s1.gpr .r9 = BitVec.ofNat 64 (8 * arrSlot ((w + 2) % 4)) := gpr_write_self _ _ _
  have e1 : exec (.li .r9 (8 * arrSlot ((w + 2) % 4))) s = some s1 :=
    exec_li (by have := arr_ok hw'; omega)
  have e2 : exec (.loadRev .w .r9 .r7 .r9) s1 = some s2 := by
    rw [exec_loadRev_w (by decide) (by rw [h7, h9, hla]; exact lane_rw h hL hj), h7, h9, hla]; rfl
  have h3 : s2.gpr .r6 = s.gpr .r6 := by simp [s2, s1, gpr_write]
  have e3 := exec_store_w (s := s2) (t := .r9) (n := .r6) (off := 4 * w) (by decide) (by omega)
    (by rw [h3]; simp only [s2, s1, wr_write]; exact hwr)
  rw [runBlock_cons, e1, runStep_some, runBlock_cons, e2, runStep_some, runBlock_cons, e3, runStep_some,
    runBlock_nil]
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, fun r hr => ?_⟩
  · show s2.mem.writeW _ _ = _
    rw [h3]
    simp [s2, s1, gpr_write, mem_write, setWidth_setWidth_32]
  · simp [s2, s1, gpr_write, hr]

/-- The four words `y` of a block, byte-swapped, from `q`. -/
def outWrites (m : Mem) (q : Addr) (y : Nat → BitVec 32) : Mem :=
  (((m.writeW (q + BitVec.ofNat 64 0) (rev32 (y 0))).writeW (q + BitVec.ofNat 64 4) (rev32 (y 1))).writeW
    (q + BitVec.ofNat 64 8) (rev32 (y 2))).writeW (q + BitVec.ofNat 64 12) (rev32 (y 3))

theorem copyOutBody_ok {j : Nat} (hj : j < 16) (s : State) (h : Room s)
    (hrb : s.gpr .r7 = s.gpr .r8 + BitVec.ofNat 64 (4 * j))
    (hwr : ∀ w < 4, InRegions s.wr (s.gpr .r6 + BitVec.ofNat 64 (4 * w)) 4)
    (hsep : Region.Disjoint ⟨s.gpr .r6, 16⟩ (arraysR s)) :
    ∃ s', runBlock isa copyOutBody s = some s' ∧
      s'.mem = outWrites s.mem (s.gpr .r6) (fun w => lv s (arrSlot ((w + 2) % 4)) j) ∧
      s'.gpr .r6 = s.gpr .r6 + 16 ∧ s'.gpr .r7 = s.gpr .r7 + 4 ∧
      s'.gpr .r10 = s.gpr .r10 - 1 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .r9 → r ≠ .r7 → r ≠ .r10 → r ≠ .r6 → s'.gpr r = s.gpr r) := by
  -- The lanes keep their values while the block is written.
  have hkeep : ∀ (t : State), t.gpr .r8 = s.gpr .r8 → Frame [⟨s.gpr .r6, 16⟩] s.mem t.mem → ∀ w < 4,
      lv t (arrSlot ((w + 2) % 4)) j = lv s (arrSlot ((w + 2) % 4)) j := by
    intro t ht hf w hw
    simp only [lv, laneA, ht]
    refine hf.readW (Region.contains_self _ _) ?_ (by decide)
    intro r hr'; simp only [List.mem_singleton] at hr'; subst hr'
    exact fun x h1 h2 => hsep x h2 (lane_inArrays (mem_arrA_of (Nat.mod_lt _ (by decide))) hj s
      |>.byte h1)
  obtain ⟨s1, e1, m1, rd1, wr1, sp1, g1⟩ := copyOutWord_ok (w := 0) (by decide) hj s h hrb (hwr 0 (by decide))
  have r9_1 : s1.gpr .r8 = s.gpr .r8 := g1 _ (by decide)
  have h1 : Room s1 := room_congr h r9_1 wr1
  have hin : ∀ w < 4, (⟨s.gpr .r6, 16⟩ : Region).Contains (s.gpr .r6 + BitVec.ofNat 64 (4 * w)) (32 / 8) :=
    fun w hw => Offset.contains_base _ (by omega) (by omega)
  have f1 : Frame [⟨s.gpr .r6, 16⟩] s.mem s1.mem := by
    rw [m1]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (hin 0 (by decide))
  obtain ⟨s2, e2, m2, rd2, wr2, sp2, g2⟩ := copyOutWord_ok (w := 1) (by decide) hj s1 h1
    (by rw [g1 _ (by decide), r9_1, hrb]) (by rw [wr1, g1 _ (by decide)]; exact hwr 1 (by decide))
  have r9_2 : s2.gpr .r8 = s.gpr .r8 := by rw [g2 _ (by decide), r9_1]
  have h2 : Room s2 := room_congr h r9_2 (by rw [wr2, wr1])
  have r10_1 : s1.gpr .r6 = s.gpr .r6 := g1 _ (by decide)
  have f2 : Frame [⟨s.gpr .r6, 16⟩] s.mem s2.mem := by
    rw [m2, r10_1]; exact f1.writeW List.mem_cons_self _ (hin 1 (by decide))
  obtain ⟨s3, e3, m3, rd3, wr3, sp3, g3⟩ := copyOutWord_ok (w := 2) (by decide) hj s2 h2
    (by rw [g2 _ (by decide), g1 _ (by decide), r9_2, hrb])
    (by rw [wr2, wr1, g2 _ (by decide), r10_1]; exact hwr 2 (by decide))
  have r9_3 : s3.gpr .r8 = s.gpr .r8 := by rw [g3 _ (by decide), r9_2]
  have h3 : Room s3 := room_congr h r9_3 (by rw [wr3, wr2, wr1])
  have r10_2 : s2.gpr .r6 = s.gpr .r6 := by rw [g2 _ (by decide), r10_1]
  have f3 : Frame [⟨s.gpr .r6, 16⟩] s.mem s3.mem := by
    rw [m3, r10_2]; exact f2.writeW List.mem_cons_self _ (hin 2 (by decide))
  obtain ⟨s4, e4, m4, rd4, wr4, sp4, g4⟩ := copyOutWord_ok (w := 3) (by decide) hj s3 h3
    (by rw [g3 _ (by decide), g2 _ (by decide), g1 _ (by decide), r9_3, hrb])
    (by rw [wr3, wr2, wr1, g3 _ (by decide), r10_2]; exact hwr 3 (by decide))
  have r10_3 : s3.gpr .r6 = s.gpr .r6 := by rw [g3 _ (by decide), r10_2]
  let s5 := s4.write .r6 (s4.gpr .r6 + BitVec.ofNat _ 16)
  let s6 := s5.write .r7 (s5.gpr .r7 + BitVec.ofNat _ 4)
  let s7 := s6.write .r10 (s6.gpr .r10 - BitVec.ofNat _ 1)
  have hrun : runBlock isa copyOutBody s = some s7 := by
    rw [copyOutBody_eq, runBlock_append, e1, Option.bind_some, runBlock_append, e2, Option.bind_some,
      runBlock_append, e3, Option.bind_some, runBlock_append, e4, Option.bind_some, runBlock_cons,
      exec_addi' (n := .r6) (by decide), runStep_some, runBlock_cons, exec_addi' (n := .r7) (by decide), runStep_some,
      runBlock_cons, exec_subi' (n := .r10) (by decide), runStep_some, runBlock_nil]
  have rbx_4 : s4.gpr .r7 = s.gpr .r7 := by
    rw [g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
  have rcx_4 : s4.gpr .r10 = s.gpr .r10 := by
    rw [g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
  have r10_4 : s4.gpr .r6 = s.gpr .r6 := by rw [g4 _ (by decide), r10_3]
  refine ⟨s7, hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_⟩
  · simp only [s7, s6, s5, mem_write]
    rw [m4, r10_3, hkeep s3 r9_3 f3 3 (by decide), m3, r10_2,
      hkeep s2 r9_2 f2 2 (by decide), m2, r10_1, hkeep s1 r9_1 f1 1 (by decide), m1, outWrites]
  · simp [s7, s6, s5, gpr_write, r10_4]
  · simp [s7, s6, s5, gpr_write, rbx_4]
  · simp [s7, s6, s5, gpr_write, rcx_4]
  · simp only [s7, s6, s5, rd_write, rd4, rd3, rd2, rd1]
  · simp only [s7, s6, s5, wr_write, wr4, wr3, wr2, wr1]
  · simp only [s7, s6, s5, sp_write, sp4, sp3, sp2, sp1]
  · simp only [s7, s6, s5, gpr_write, h3, h2, h4, ↓reduceIte]
    rw [g4 _ h1, g3 _ h1, g2 _ h1, g1 _ h1]

theorem outWrites_off (m : Mem) (q : Addr) (y : Nat → BitVec 32) {x : Addr}
    (h : ¬ (x - q).toNat < 16) : outWrites m q y x = m x := by
  have hx : x = q + BitVec.ofNat 64 (x - q).toNat := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  have hlt := (x - q).isLt
  have hoff : ∀ c : Nat, c ≤ 12 → ¬ (x - (q + BitVec.ofNat 64 c)).toNat < 32 / 8 := by
    intro c hc
    have := Offset.sep q (d := (x - q).toNat) (n := 1) (e := c) (k := 4) (by omega) (by omega) (by omega)
    refine this x ?_
    rw [← hx, BitVec.sub_self]; decide
  simp only [outWrites, Mem.writeW]
  rw [Mem.write_apply (hoff 12 (by decide)), Mem.write_apply (hoff 8 (by decide)),
    Mem.write_apply (hoff 4 (by decide)), Mem.write_apply (hoff 0 (by decide))]

theorem outWrites_frame {m₀ m : Mem} {p : Addr} {n j : Nat} (h : Frame [⟨p, n⟩] m₀ m) (hj : 16 * j + 16 ≤ n)
    (hn : n < 2 ^ 64) (y : Nat → BitVec 32) :
    Frame [⟨p, n⟩] m₀ (outWrites m (p + BitVec.ofNat 64 (16 * j)) y) := by
  have hc : ∀ c, c ≤ 12 → (⟨p, n⟩ : Region).Contains (p + BitVec.ofNat 64 (16 * j) + BitVec.ofNat 64 c) (32 / 8) := by
    intro c hc; rw [Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)
  exact (((h.writeW List.mem_cons_self _ (hc 0 (by decide))).writeW List.mem_cons_self _ (hc 4 (by decide))).writeW
    List.mem_cons_self _ (hc 8 (by decide))).writeW List.mem_cons_self _ (hc 12 (by decide))

/-- Byte `i` of block `b` copied out: byte `3 - i % 4` of word `(i / 4 + 2) % 4` of lane `b`. -/
def outByte (s : State) (b i : Nat) : Byte := (lv s (arrSlot ((i / 4 + 2) % 4)) b >>> (8 * (3 - i % 4))).setWidth 8

/-- What the copy out of the arrays needs. -/
structure CopyOutPre (s : State) (p : Addr) (m : Nat) : Prop where
  room : Room s
  le : 1 ≤ m ∧ m ≤ 16
  write : ∀ b < m, ∀ w < 4, InRegions s.wr (p + BitVec.ofNat 64 (16 * b + 4 * w)) 4
  sep : Region.Disjoint ⟨p, 16 * m⟩ (arraysR s)

/-- After `j` blocks of the copy out. -/
structure CopyOutInv (s₀ : State) (p : Addr) (m j : Nat) (s : State) : Prop where
  le : j ≤ m
  r6 : s.gpr .r6 = p + BitVec.ofNat 64 (16 * j)
  r7 : s.gpr .r7 = s₀.gpr .r8 + BitVec.ofNat 64 (4 * j)
  r10 : s.gpr .r10 = BitVec.ofNat 64 (m - j)
  done : ∀ b < j, ∀ i < 16, s.mem (p + BitVec.ofNat 64 (16 * b + i)) = outByte s₀ b i
  frame : Frame [⟨p, 16 * m⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .r9 → r ≠ .r7 → r ≠ .r10 → r ≠ .r6 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem copyOut_loop {s₀ : State} {p : Addr} {m : Nat} (hpre : CopyOutPre s₀ p m) :
    ∀ k s, CopyOutInv s₀ p m (m - k) s → 1 ≤ k → k ≤ m →
      WP isa (.loop (.block copyOutBody) (.nonzero .d .r10)) s (fun s' => CopyOutInv s₀ p m m s') := by
  intro k s hs hk1 hkm
  refine WP.loop (M := isa) (fun k t => CopyOutInv s₀ p m (m - k) t ∧ 1 ≤ k ∧ k ≤ m) ?_ k s ⟨hs, hk1, hkm⟩
  intro k t ⟨inv, hk1, hkm⟩
  have hm16 := hpre.le.2
  let j := m - k
  have hj : j < 16 := by omega
  have hr9 : t.gpr .r8 = s₀.gpr .r8 := inv.regs _ (by decide) (by decide) (by decide) (by decide)
  have hroom : Room t := room_congr hpre.room hr9 inv.wr
  have hrb : t.gpr .r7 = t.gpr .r8 + BitVec.ofNat 64 (4 * j) := by rw [inv.r7, hr9]
  have hwr : ∀ w < 4, InRegions t.wr (t.gpr .r6 + BitVec.ofNat 64 (4 * w)) 4 := by
    intro w hw; rw [inv.r6, Offset.add_add, inv.wr]; exact hpre.write j (by omega) w hw
  have harr : arraysR t = arraysR s₀ := by simp [arraysR, hr9]
  have hsep : Region.Disjoint ⟨t.gpr .r6, 16⟩ (arraysR t) := by
    rw [inv.r6, harr]; exact hpre.sep.sub_left (Offset.sub_base p (by omega))
  obtain ⟨t', ht', hmem, hr10, hrbx, hrcx, hrd, hwr', hsp, hregs⟩ := copyOutBody_ok hj t hroom hrb hwr hsep
  refine WP.of_runBlock ⟨t', ht', ?_⟩
  -- The lanes, as they were.
  have hlanes : ∀ w < 4, lv t (arrSlot ((w + 2) % 4)) j = lv s₀ (arrSlot ((w + 2) % 4)) j := by
    intro w hw
    simp only [lv, laneA, hr9]
    refine inv.frame.readW (Region.contains_self _ _) ?_ (by decide)
    intro r hr'; simp only [List.mem_singleton] at hr'; subst hr'
    exact fun x h1 h2 => hpre.sep x h2 (lane_inArrays (mem_arrA_of (Nat.mod_lt _ (by decide))) hj s₀ |>.byte h1)
  have inv' : CopyOutInv s₀ p m (j + 1) t' := by
    refine ⟨by omega, ?_, ?_, ?_, fun b hb i hi => ?_, ?_, fun r h1 h2 h3 h4 => ?_, by rw [hsp, inv.sp],
      by rw [hrd, inv.rd], by rw [hwr', inv.wr]⟩
    · rw [hr10, inv.r6, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, Offset.add_add]; congr 2
    · rw [hrbx, inv.r7, show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_add]; congr 2
    · rw [hrcx, inv.r10, show m - j = k by omega, cnt_sub1 hk1 (by omega)]; congr 1; omega
    · rw [hmem]
      by_cases hbj : b = j
      · subst hbj
        rw [show p + BitVec.ofNat 64 (16 * (m - k) + i) = t.gpr .r6 + BitVec.ofNat 64 i by
          rw [inv.r6, Offset.add_add]]
        unfold outWrites
        rw [block_writes _ _ (fun w => lv t (arrSlot ((w + 2) % 4)) j) hi, outByte, hlanes _ (by omega)]
      · rw [outWrites_off _ _ _ ?_]
        · exact inv.done b (by omega) i hi
        · rw [inv.r6, Offset.sub_toNat' p (by omega) (by omega)]
          split <;> omega
    · rw [hmem, inv.r6]
      exact outWrites_frame inv.frame (by omega) (by omega) _
    · rw [hregs r h1 h2 h3 h4]; exact inv.regs r h1 h2 h3 h4
  by_cases hk : k = 1
  · subst hk
    left
    have hjm : j + 1 = m := by omega
    refine ⟨?_, hjm ▸ inv'⟩
    show some (t'.read .d .r10 != 0) = some false
    rw [show t'.read .d .r10 = t'.gpr .r10 from BitVec.setWidth_eq _, hrcx, inv.r10, show m - (m - 1) = 1 by omega]; rfl
  · right
    refine ⟨?_, k - 1, by omega, ⟨by simpa [show j + 1 = m - (k - 1) by omega] using inv', by omega, by omega⟩⟩
    show some (t'.read .d .r10 != 0) = some true
    rw [show t'.read .d .r10 = t'.gpr .r10 from BitVec.setWidth_eq _, hrcx, inv.r10, show m - (m - k) = k by omega, cnt_ne_zero (by omega) (by omega)]

end VG.Proof.Seed.PPC64LE
