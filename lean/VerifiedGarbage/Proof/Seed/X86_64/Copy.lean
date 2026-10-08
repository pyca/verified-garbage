import VerifiedGarbage.Proof.Seed.X86_64.Rounds
import VerifiedGarbage.Proof.Framework.X86_64.Bswap

/-!
# Copying blocks into the arrays and back

`copyIn_ok`: the loop of `copyInBody` copies `m` blocks from `p` into lanes
`0 … m - 1` of the arrays, each word byte-swapped (`bw`, a block's big-endian
word). `copyOut_ok`: the loop of `copyOutBody` copies them back, `R` first.
-/

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Seed.X86_64

-- The copies share one set of rewrites, not all of which each uses.
set_option linter.unusedSimpArgs false

/-- Word `w` of block `b` from `p`, big-endian. -/
def bw (m : Mem) (p : Addr) (b w : Nat) : BitVec 32 :=
  bswap32 (m.readW (p + BitVec.ofNat 64 (16 * b + 4 * w)) 32)

theorem ea_off (s : State) (r : Reg) (k : Nat) :
    s.ea { base := r, disp := ((k : Nat) : Int) } = s.gpr r + BitVec.ofNat 64 k := by
  show s.gpr r + BitVec.ofInt 64 ((k : Nat) : Int) = _
  rw [BitVec.ofInt_natCast]

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
  r10 : s.gpr .r10 = p + BitVec.ofNat 64 (16 * j)
  rbx : s.gpr .rbx = s₀.gpr .r9 + BitVec.ofNat 64 (4 * j)
  rcx : s.gpr .rcx = BitVec.ofNat 64 (m - j)
  lanes : ∀ w < 4, ∀ b < j, lv s (arrSlot w) b = bw s₀.mem p b w
  frame : Frame [arraysR s₀] s₀.mem s.mem
  regs : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .r10 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem writeW32_byte (m : Mem) (a : Addr) (v : BitVec 32) {j : Nat} (hj : j < 4) :
    (m.writeW a v) (a + BitVec.ofNat 64 j) = v.extractLsb' (8 * j) 8 := by
  simp only [Mem.writeW, Mem.write, Mem.sub_ofNat_toNat a (show j < 2 ^ 64 by omega),
    show j < 32 / 8 by omega, ite_true, BitVec.setWidth_eq]

/-- The copy of word `w` of a block. -/
def inWord (w : Nat) : List Instr :=
  [.mov32 .rax (.mem { base := .r10, disp := ((4 * w : Nat) : Int) }), .bswap32 .rax,
   .store32 (lane .rbx (arrSlot w) 0) .rax]

theorem copyInBody_eq : copyInBody = inWord 0 ++ (inWord 1 ++ (inWord 2 ++ (inWord 3 ++
    ([.alu .add .r10 (.imm 16), .alu .add .rbx (.imm 4), .alu .sub .rcx (.imm 1)] : List Instr)))) := rfl

/-- One word of a block into its lane. -/
theorem copyInWord_ok {w j : Nat} (hw : w < 4) (hj : j < 16) (s : State) (h : Room s)
    (hrb : s.gpr .rbx = s.gpr .r9 + BitVec.ofNat 64 (4 * j))
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .r10 + BitVec.ofNat 64 (4 * w)) 4) :
    ∃ s', runBlock isa (inWord w) s = some s' ∧
      s'.mem = s.mem.writeW (laneA s (arrSlot w) j)
        (bswap32 (s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (4 * w)) 32)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) := by
  have hL : arrSlot w ∈ arrays := mem_arrA_of hw
  unfold inWord
  have hea : ∀ t : State, t.gpr .rbx = s.gpr .rbx → t.ea (lane .rbx (arrSlot w) 0) = laneA s (arrSlot w) j := by
    intro t ht
    rw [ea_lane, ht, hrb, laneA, Nat.mul_zero, Nat.add_zero, Offset.add_add, Nat.add_comm]
  rw [runBlock_cons, exec_mov32_mem (by rw [ea_off]; exact hr), ea_off, runStep_some, runBlock_cons]
  rw [show exec (.bswap32 .rax) (s.setReg32 .rax (s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (4 * w)) 32)) =
    some ((s.setReg32 .rax (s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (4 * w)) 32)).setReg32 .rax
      (bswap32 (((s.setReg32 .rax (s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (4 * w)) 32)).gpr .rax).setWidth 32)))
    from rfl, runStep_some, runBlock_cons]
  rw [exec_store32 (by rw [hea _ (by simp [State.setReg32, gpr_setReg])]; exact lane_wr h hL hj),
    hea _ (by simp [State.setReg32, gpr_setReg]), runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, rfl, rfl, fun r hr => ?_⟩
  · simp [State.setReg32, gpr_setReg, mem_setReg, setWidth_setWidth_32]
  · simp [State.setReg32, gpr_setReg, hr]

/-- The copy of one block into lane `j`, as writes of the block's words. -/
def inSpec (m : Mem) (q : Addr) : LaneSpec :=
  (List.range 4).map fun w => (arrSlot w, fun _ => bswap32 (m.readW (q + BitVec.ofNat 64 (4 * w)) 32))

theorem inSpec_dests (m : Mem) (q : Addr) : ∀ kv ∈ inSpec m q, kv.1 ∈ arrays := by
  intro kv hkv
  simp only [inSpec, List.mem_map, List.mem_range] at hkv
  obtain ⟨w, hw, rfl⟩ := hkv
  exact mem_arrA_of hw

theorem copyInBody_ok {j : Nat} (hj : j < 16) (s : State) (h : Room s)
    (hrb : s.gpr .rbx = s.gpr .r9 + BitVec.ofNat 64 (4 * j))
    (hr : ∀ w < 4, InRegions (s.rd ++ s.wr) (s.gpr .r10 + BitVec.ofNat 64 (4 * w)) 4)
    (hsep : ∀ w < 4, Region.Disjoint ⟨s.gpr .r10 + BitVec.ofNat 64 (4 * w), 4⟩ (arraysR s)) :
    ∃ s', runBlock isa copyInBody s = some s' ∧
      s'.mem = laneWrites s (inSpec s.mem (s.gpr .r10)) j ∧
      s'.gpr .r10 = s.gpr .r10 + 16 ∧ s'.gpr .rbx = s.gpr .rbx + 4 ∧
      s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .r10 → s'.gpr r = s.gpr r) := by
  -- The block's words keep their values while the lanes are written.
  have hkeep : ∀ (t : State), Frame [arraysR s] s.mem t.mem → ∀ w < 4,
      t.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (4 * w)) 32 =
        s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (4 * w)) 32 := by
    intro t ht w hw
    refine ht.readW (Region.contains_self _ _) ?_ (by decide)
    intro r hr'; simp only [List.mem_singleton] at hr'; subst hr'; exact hsep w hw
  obtain ⟨s1, e1, m1, rd1, wr1, g1⟩ := copyInWord_ok (w := 0) (by decide) hj s h hrb (hr 0 (by decide))
  have h1 : Room s1 := room_congr h (g1 _ (by decide)) wr1
  obtain ⟨s2, e2, m2, rd2, wr2, g2⟩ := copyInWord_ok (w := 1) (by decide) hj s1 h1
    (by rw [g1 _ (by decide), g1 _ (by decide), hrb]) (by rw [rd1, wr1, g1 _ (by decide)]; exact hr 1 (by decide))
  have h2 : Room s2 := room_congr h1 (g2 _ (by decide)) wr2
  obtain ⟨s3, e3, m3, rd3, wr3, g3⟩ := copyInWord_ok (w := 2) (by decide) hj s2 h2
    (by rw [g2 _ (by decide), g2 _ (by decide), g1 _ (by decide), g1 _ (by decide), hrb])
    (by rw [rd2, wr2, rd1, wr1, g2 _ (by decide), g1 _ (by decide)]; exact hr 2 (by decide))
  have h3 : Room s3 := room_congr h2 (g3 _ (by decide)) wr3
  obtain ⟨s4, e4, m4, rd4, wr4, g4⟩ := copyInWord_ok (w := 3) (by decide) hj s3 h3
    (by rw [g3 _ (by decide), g3 _ (by decide), g2 _ (by decide), g2 _ (by decide), g1 _ (by decide),
      g1 _ (by decide), hrb])
    (by rw [rd3, wr3, rd2, wr2, rd1, wr1, g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)];
        exact hr 3 (by decide))
  obtain ⟨s5, e5, r5, g5, mem5, rd5, wr5⟩ := exec_add_imm s4 .r10 16
  obtain ⟨s6, e6, r6, g6, mem6, rd6, wr6⟩ := exec_add_imm s5 .rbx 4
  obtain ⟨s7, e7, r7, z7, g7, mem7, rd7, wr7⟩ := exec_sub_imm s6 .rcx 1
  have hrun : runBlock isa copyInBody s = some s7 := by
    rw [copyInBody_eq]
    rw [runBlock_append, e1, Option.bind_some, runBlock_append, e2, Option.bind_some, runBlock_append, e3,
      Option.bind_some, runBlock_append, e4, Option.bind_some, runBlock_cons, e5, runStep_some, runBlock_cons,
      e6, runStep_some, runBlock_cons, e7, runStep_some, runBlock_nil]
  -- Registers through the words.
  have r9s : ∀ t ∈ [s1, s2, s3, s4], t.gpr .r9 = s.gpr .r9 := by
    intro t ht
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact g1 _ (by decide)
    · rw [g2 _ (by decide), g1 _ (by decide)]
    · rw [g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
    · rw [g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
  have r10s : ∀ t ∈ [s1, s2, s3, s4], t.gpr .r10 = s.gpr .r10 := by
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
  let v (w : Nat) := bswap32 (s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (4 * w)) 32)
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
  have rbx_4 : s4.gpr .rbx = s.gpr .rbx := by
    rw [g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
  have rcx_4 : s4.gpr .rcx = s.gpr .rcx := by
    rw [g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
  refine ⟨s7, hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_⟩
  · rw [mem7, mem6, mem5, mm]
    simp only [laneWrites, inSpec, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.foldl_cons, List.foldl_nil, List.singleton_append, List.cons_append,
      List.map_cons]
    rfl
  · rw [g7 _ (by decide), g6 _ (by decide), r5, r10_4]; rfl
  · rw [g7 _ (by decide), r6, g5 _ (by decide), rbx_4]; rfl
  · rw [r7, g6 _ (by decide), g5 _ (by decide), rcx_4]; rfl
  · rw [z7, g6 _ (by decide), g5 _ (by decide), rcx_4]; rfl
  · rw [rd7, rd6, rd5, rd4, rd3, rd2, rd1]
  · rw [wr7, wr6, wr5, wr4, wr3, wr2, wr1]
  · rw [g7 _ h3, g6 _ h2, g5 _ h4, g4 _ h1, g3 _ h1, g2 _ h1, g1 _ h1]

theorem cnt_ne_zero {k : Nat} (h1 : 2 ≤ k) (h2 : k ≤ 16) :
    (BitVec.ofNat 64 k - 1 == 0) = false := by
  simp only [beq_eq_false_iff_ne, ne_eq]
  intro h0
  have := congrArg BitVec.toNat h0
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl,
    show (0 : BitVec 64).toNat = 0 from rfl, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)] at this
  omega

theorem cnt_sub1 {k : Nat} (h1 : 1 ≤ k) (h2 : k ≤ 16) : BitVec.ofNat 64 k - 1 = BitVec.ofNat 64 (k - 1) := by
  have := r8_sub k h1 h2
  rwa [show (1 : BitVec 32).signExtend 64 = 1 from rfl] at this

theorem copyIn_loop {s₀ : State} {p : Addr} {m : Nat} (hpre : CopyPre s₀ p m) :
    ∀ k s, CopyInInv s₀ p m (m - k) s → 1 ≤ k → k ≤ m →
      WP isa (.loop (.block copyInBody) .ne) s (fun s' => CopyInInv s₀ p m m s') := by
  intro k s hs hk1 hkm
  refine WP.loop (M := isa) (fun k t => CopyInInv s₀ p m (m - k) t ∧ 1 ≤ k ∧ k ≤ m) ?_ k s ⟨hs, hk1, hkm⟩
  intro k t ⟨inv, hk1, hkm⟩
  have hm16 := hpre.le.2
  let j := m - k
  have hj : j < 16 := by omega
  have hr9 : t.gpr .r9 = s₀.gpr .r9 := inv.regs _ (by decide) (by decide) (by decide) (by decide)
  have hroom : Room t := room_congr hpre.room hr9 inv.wr
  have hrb : t.gpr .rbx = t.gpr .r9 + BitVec.ofNat 64 (4 * j) := by rw [inv.rbx, hr9]
  have hdata : ∀ w < 4, t.gpr .r10 + BitVec.ofNat 64 (4 * w) = p + BitVec.ofNat 64 (16 * j + 4 * w) := by
    intro w _; rw [inv.r10, Offset.add_add]
  have hr : ∀ w < 4, InRegions (t.rd ++ t.wr) (t.gpr .r10 + BitVec.ofNat 64 (4 * w)) 4 := by
    intro w hw; rw [hdata w hw, inv.rd, inv.wr]; exact hpre.read j (by omega) w hw
  have harr : arraysR t = arraysR s₀ := by simp [arraysR, hr9]
  have hsep : ∀ w < 4, Region.Disjoint ⟨t.gpr .r10 + BitVec.ofNat 64 (4 * w), 4⟩ (arraysR t) := by
    intro w hw
    rw [hdata w hw, harr]
    exact hpre.sep.sub_left (Offset.sub_base p (by omega))
  obtain ⟨t', ht', hmem, hr10, hrbx, hrcx, hzf, hrd, hwr, hregs⟩ := copyInBody_ok hj t hroom hrb hr hsep
  refine WP.of_runBlock ⟨t', ht', ?_⟩
  have hr9' : t'.gpr .r9 = t.gpr .r9 := hregs _ (by decide) (by decide) (by decide) (by decide)
  have inv' : CopyInInv s₀ p m (j + 1) t' := by
    refine ⟨by omega, ?_, ?_, ?_, fun w hw b hb => ?_, ?_, fun r h1 h2 h3 h4 => ?_, by rw [hrd, inv.rd],
      by rw [hwr, inv.wr]⟩
    · rw [hr10, inv.r10, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, Offset.add_add]; congr 2
    · rw [hrbx, inv.rbx, show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_add]; congr 2
    · rw [hrcx, inv.rcx, show m - j = k by omega, cnt_sub1 hk1 (by omega)]; congr 1; omega
    · have hl : lv t' (arrSlot w) b = (laneWrites t (inSpec t.mem (t.gpr .r10)) j).readW (laneA t (arrSlot w) b) 32 := by
        rw [← hmem]; simp only [lv, laneA, hr9']
      rw [hl, lv_laneWrites (inSpec_dests _ _) t (mem_arrA_of hw) (by omega) hj]
      by_cases hbj : b = j
      · subst hbj
        simp only [ite_true, newVal, inSpec, List.range_succ, List.range_zero, List.nil_append,
          List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, List.singleton_append,
          List.cons_append]
        rw [bw, ← hdata w hw]
        have hkeep : t.mem.readW (t.gpr .r10 + BitVec.ofNat 64 (4 * w)) 32 =
            s₀.mem.readW (t.gpr .r10 + BitVec.ofNat 64 (4 * w)) 32 := by
          refine inv.frame.readW (Region.contains_self _ _) ?_ (by decide)
          intro r hr'; simp only [List.mem_singleton] at hr'; subst hr'; rw [← harr]; exact hsep w hw
        rw [← hkeep]
        rcases (show w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 by omega) with rfl | rfl | rfl | rfl <;> simp [arrSlot]
      · rw [ite_eq_right hbj]; exact inv.lanes w hw b (by omega)
    · refine inv.frame.trans ?_
      have := laneWrites_frame (inSpec_dests t.mem (t.gpr .r10)) t (b := j) hj
      rw [← hmem, harr] at this; exact this
    · rw [hregs r h1 h2 h3 h4]; exact inv.regs r h1 h2 h3 h4
  by_cases hk : k = 1
  · subst hk
    left
    have hjm : j + 1 = m := by omega
    refine ⟨?_, hjm ▸ inv'⟩
    show t'.zf.map (!·) = some false
    rw [hzf, inv.rcx, show m - (m - 1) = 1 by omega]; rfl
  · right
    refine ⟨?_, k - 1, by omega, ⟨by simpa [show j + 1 = m - (k - 1) by omega] using inv', by omega, by omega⟩⟩
    show t'.zf.map (!·) = some true
    rw [hzf, inv.rcx, show m - (m - k) = k by omega, cnt_ne_zero (by omega) (by omega)]; rfl

/-! ## Copying out -/

/-- Byte `j` (in memory order) of a byte-swapped word is byte `3 - j` of the word. -/
theorem bswap32_byte (x : BitVec 32) {j : Nat} (hj : j < 4) :
    (bswap32 x).extractLsb' (8 * j) 8 = (x >>> (8 * (3 - j))).setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h4 := Proof.Seed.getLsbD_append4 (x.extractLsb' 0 8) (x.extractLsb' 8 8) (x.extractLsb' 16 8)
    (x.extractLsb' 24 8) hi
  have e : ((bswap32 x).extractLsb' (8 * j) 8).getLsbD i = (bswap32 x).getLsbD (8 * j + i) := by
    simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  rw [e]
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  unfold bswap32
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
    ((((m.writeW (a + BitVec.ofNat 64 0) (bswap32 (y 0))).writeW (a + BitVec.ofNat 64 4) (bswap32 (y 1))).writeW
      (a + BitVec.ofNat 64 8) (bswap32 (y 2))).writeW (a + BitVec.ofNat 64 12) (bswap32 (y 3)))
      (a + BitVec.ofNat 64 i) = (y (i / 4) >>> (8 * (3 - i % 4))).setWidth 8 := by
  rcases (show i / 4 = 0 ∨ i / 4 = 1 ∨ i / 4 = 2 ∨ i / 4 = 3 by omega) with h | h | h | h
  · rw [writeW32_off _ _ _ (by omega) (by omega) (by omega), writeW32_off _ _ _ (by omega) (by omega) (by omega),
      writeW32_off _ _ _ (by omega) (by omega) (by omega), writeW32_at _ _ _ (by omega) (by omega) (by omega),
      bswap32_byte _ (by omega), h]
    congr 3; omega
  · rw [writeW32_off _ _ _ (by omega) (by omega) (by omega), writeW32_off _ _ _ (by omega) (by omega) (by omega),
      writeW32_at _ _ _ (by omega) (by omega) (by omega), bswap32_byte _ (by omega), h]
    congr 3; omega
  · rw [writeW32_off _ _ _ (by omega) (by omega) (by omega), writeW32_at _ _ _ (by omega) (by omega) (by omega),
      bswap32_byte _ (by omega), h]
    congr 3; omega
  · rw [writeW32_at _ _ _ (by omega) (by omega) (by omega), bswap32_byte _ (by omega), h]
    congr 3; omega

/-- The copy of word `w` of a block out. -/
def outWord (w : Nat) : List Instr :=
  [.mov32 .rax (.mem (lane .rbx (arrSlot ((w + 2) % 4)) 0)), .bswap32 .rax,
   .store32 { base := .r10, disp := ((4 * w : Nat) : Int) } .rax]

theorem copyOutBody_eq : copyOutBody = outWord 0 ++ (outWord 1 ++ (outWord 2 ++ (outWord 3 ++
    ([.alu .add .r10 (.imm 16), .alu .add .rbx (.imm 4), .alu .sub .rcx (.imm 1)] : List Instr)))) := rfl

theorem copyOutWord_ok {w j : Nat} (hj : j < 16) (s : State) (h : Room s)
    (hrb : s.gpr .rbx = s.gpr .r9 + BitVec.ofNat 64 (4 * j))
    (hwr : InRegions s.wr (s.gpr .r10 + BitVec.ofNat 64 (4 * w)) 4) :
    ∃ s', runBlock isa (outWord w) s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .r10 + BitVec.ofNat 64 (4 * w))
        (bswap32 (lv s (arrSlot ((w + 2) % 4)) j)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) := by
  have hL : arrSlot ((w + 2) % 4) ∈ arrays := mem_arrA_of (Nat.mod_lt _ (by decide))
  have hea : s.ea (lane .rbx (arrSlot ((w + 2) % 4)) 0) = laneA s (arrSlot ((w + 2) % 4)) j := by
    rw [ea_lane, hrb, laneA, Nat.mul_zero, Nat.add_zero, Offset.add_add, Nat.add_comm]
  unfold outWord
  rw [runBlock_cons, exec_mov32_mem (by rw [hea]; exact lane_rw h hL hj), hea, lv_eq, runStep_some,
    runBlock_cons]
  rw [show exec (.bswap32 .rax) (s.setReg32 .rax (lv s (arrSlot ((w + 2) % 4)) j)) =
    some ((s.setReg32 .rax (lv s (arrSlot ((w + 2) % 4)) j)).setReg32 .rax
      (bswap32 (((s.setReg32 .rax (lv s (arrSlot ((w + 2) % 4)) j)).gpr .rax).setWidth 32))) from rfl,
    runStep_some, runBlock_cons]
  have hea2 : ∀ t : State, t.gpr .r10 = s.gpr .r10 →
      t.ea { base := .r10, disp := ((4 * w : Nat) : Int) } = s.gpr .r10 + BitVec.ofNat 64 (4 * w) := by
    intro t ht; rw [ea_off, ht]
  rw [exec_store32 (by rw [hea2 _ (by simp [State.setReg32, gpr_setReg])]; exact hwr),
    hea2 _ (by simp [State.setReg32, gpr_setReg]), runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, rfl, rfl, fun r hr => ?_⟩
  · simp [State.setReg32, gpr_setReg, mem_setReg, setWidth_setWidth_32]
  · simp [State.setReg32, gpr_setReg, hr]

/-- The four words `y` of a block, byte-swapped, from `q`. -/
def outWrites (m : Mem) (q : Addr) (y : Nat → BitVec 32) : Mem :=
  (((m.writeW (q + BitVec.ofNat 64 0) (bswap32 (y 0))).writeW (q + BitVec.ofNat 64 4) (bswap32 (y 1))).writeW
    (q + BitVec.ofNat 64 8) (bswap32 (y 2))).writeW (q + BitVec.ofNat 64 12) (bswap32 (y 3))

theorem copyOutBody_ok {j : Nat} (hj : j < 16) (s : State) (h : Room s)
    (hrb : s.gpr .rbx = s.gpr .r9 + BitVec.ofNat 64 (4 * j))
    (hwr : ∀ w < 4, InRegions s.wr (s.gpr .r10 + BitVec.ofNat 64 (4 * w)) 4)
    (hsep : Region.Disjoint ⟨s.gpr .r10, 16⟩ (arraysR s)) :
    ∃ s', runBlock isa copyOutBody s = some s' ∧
      s'.mem = outWrites s.mem (s.gpr .r10) (fun w => lv s (arrSlot ((w + 2) % 4)) j) ∧
      s'.gpr .r10 = s.gpr .r10 + 16 ∧ s'.gpr .rbx = s.gpr .rbx + 4 ∧
      s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .r10 → s'.gpr r = s.gpr r) := by
  -- The lanes keep their values while the block is written.
  have hkeep : ∀ (t : State), t.gpr .r9 = s.gpr .r9 → Frame [⟨s.gpr .r10, 16⟩] s.mem t.mem → ∀ w < 4,
      lv t (arrSlot ((w + 2) % 4)) j = lv s (arrSlot ((w + 2) % 4)) j := by
    intro t ht hf w hw
    simp only [lv, laneA, ht]
    refine hf.readW (Region.contains_self _ _) ?_ (by decide)
    intro r hr'; simp only [List.mem_singleton] at hr'; subst hr'
    exact fun x h1 h2 => hsep x h2 (lane_inArrays (mem_arrA_of (Nat.mod_lt _ (by decide))) hj s
      |>.byte h1)
  obtain ⟨s1, e1, m1, rd1, wr1, g1⟩ := copyOutWord_ok (w := 0) hj s h hrb (hwr 0 (by decide))
  have r9_1 : s1.gpr .r9 = s.gpr .r9 := g1 _ (by decide)
  have h1 : Room s1 := room_congr h r9_1 wr1
  have hin : ∀ w < 4, (⟨s.gpr .r10, 16⟩ : Region).Contains (s.gpr .r10 + BitVec.ofNat 64 (4 * w)) (32 / 8) :=
    fun w hw => Offset.contains_base _ (by omega) (by omega)
  have f1 : Frame [⟨s.gpr .r10, 16⟩] s.mem s1.mem := by
    rw [m1]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (hin 0 (by decide))
  obtain ⟨s2, e2, m2, rd2, wr2, g2⟩ := copyOutWord_ok (w := 1) hj s1 h1
    (by rw [g1 _ (by decide), r9_1, hrb]) (by rw [wr1, g1 _ (by decide)]; exact hwr 1 (by decide))
  have r9_2 : s2.gpr .r9 = s.gpr .r9 := by rw [g2 _ (by decide), r9_1]
  have h2 : Room s2 := room_congr h r9_2 (by rw [wr2, wr1])
  have r10_1 : s1.gpr .r10 = s.gpr .r10 := g1 _ (by decide)
  have f2 : Frame [⟨s.gpr .r10, 16⟩] s.mem s2.mem := by
    rw [m2, r10_1]; exact f1.writeW List.mem_cons_self _ (hin 1 (by decide))
  obtain ⟨s3, e3, m3, rd3, wr3, g3⟩ := copyOutWord_ok (w := 2) hj s2 h2
    (by rw [g2 _ (by decide), g1 _ (by decide), r9_2, hrb])
    (by rw [wr2, wr1, g2 _ (by decide), r10_1]; exact hwr 2 (by decide))
  have r9_3 : s3.gpr .r9 = s.gpr .r9 := by rw [g3 _ (by decide), r9_2]
  have h3 : Room s3 := room_congr h r9_3 (by rw [wr3, wr2, wr1])
  have r10_2 : s2.gpr .r10 = s.gpr .r10 := by rw [g2 _ (by decide), r10_1]
  have f3 : Frame [⟨s.gpr .r10, 16⟩] s.mem s3.mem := by
    rw [m3, r10_2]; exact f2.writeW List.mem_cons_self _ (hin 2 (by decide))
  obtain ⟨s4, e4, m4, rd4, wr4, g4⟩ := copyOutWord_ok (w := 3) hj s3 h3
    (by rw [g3 _ (by decide), g2 _ (by decide), g1 _ (by decide), r9_3, hrb])
    (by rw [wr3, wr2, wr1, g3 _ (by decide), r10_2]; exact hwr 3 (by decide))
  have r10_3 : s3.gpr .r10 = s.gpr .r10 := by rw [g3 _ (by decide), r10_2]
  obtain ⟨s5, e5, r5, g5, mem5, rd5, wr5⟩ := exec_add_imm s4 .r10 16
  obtain ⟨s6, e6, r6, g6, mem6, rd6, wr6⟩ := exec_add_imm s5 .rbx 4
  obtain ⟨s7, e7, r7, z7, g7, mem7, rd7, wr7⟩ := exec_sub_imm s6 .rcx 1
  have hrun : runBlock isa copyOutBody s = some s7 := by
    rw [copyOutBody_eq, runBlock_append, e1, Option.bind_some, runBlock_append, e2, Option.bind_some,
      runBlock_append, e3, Option.bind_some, runBlock_append, e4, Option.bind_some, runBlock_cons, e5,
      runStep_some, runBlock_cons, e6, runStep_some, runBlock_cons, e7, runStep_some, runBlock_nil]
  have rbx_4 : s4.gpr .rbx = s.gpr .rbx := by
    rw [g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
  have rcx_4 : s4.gpr .rcx = s.gpr .rcx := by
    rw [g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
  have r10_4 : s4.gpr .r10 = s.gpr .r10 := by rw [g4 _ (by decide), r10_3]
  refine ⟨s7, hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_⟩
  · rw [mem7, mem6, mem5, m4, r10_3, hkeep s3 r9_3 f3 3 (by decide), m3, r10_2,
      hkeep s2 r9_2 f2 2 (by decide), m2, r10_1, hkeep s1 r9_1 f1 1 (by decide), m1, outWrites]
  · rw [g7 _ (by decide), g6 _ (by decide), r5, r10_4]; rfl
  · rw [g7 _ (by decide), r6, g5 _ (by decide), rbx_4]; rfl
  · rw [r7, g6 _ (by decide), g5 _ (by decide), rcx_4]; rfl
  · rw [z7, g6 _ (by decide), g5 _ (by decide), rcx_4]; rfl
  · rw [rd7, rd6, rd5, rd4, rd3, rd2, rd1]
  · rw [wr7, wr6, wr5, wr4, wr3, wr2, wr1]
  · rw [g7 _ h3, g6 _ h2, g5 _ h4, g4 _ h1, g3 _ h1, g2 _ h1, g1 _ h1]

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
  r10 : s.gpr .r10 = p + BitVec.ofNat 64 (16 * j)
  rbx : s.gpr .rbx = s₀.gpr .r9 + BitVec.ofNat 64 (4 * j)
  rcx : s.gpr .rcx = BitVec.ofNat 64 (m - j)
  done : ∀ b < j, ∀ i < 16, s.mem (p + BitVec.ofNat 64 (16 * b + i)) = outByte s₀ b i
  frame : Frame [⟨p, 16 * m⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .r10 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem copyOut_loop {s₀ : State} {p : Addr} {m : Nat} (hpre : CopyOutPre s₀ p m) :
    ∀ k s, CopyOutInv s₀ p m (m - k) s → 1 ≤ k → k ≤ m →
      WP isa (.loop (.block copyOutBody) .ne) s (fun s' => CopyOutInv s₀ p m m s') := by
  intro k s hs hk1 hkm
  refine WP.loop (M := isa) (fun k t => CopyOutInv s₀ p m (m - k) t ∧ 1 ≤ k ∧ k ≤ m) ?_ k s ⟨hs, hk1, hkm⟩
  intro k t ⟨inv, hk1, hkm⟩
  have hm16 := hpre.le.2
  let j := m - k
  have hj : j < 16 := by omega
  have hr9 : t.gpr .r9 = s₀.gpr .r9 := inv.regs _ (by decide) (by decide) (by decide) (by decide)
  have hroom : Room t := room_congr hpre.room hr9 inv.wr
  have hrb : t.gpr .rbx = t.gpr .r9 + BitVec.ofNat 64 (4 * j) := by rw [inv.rbx, hr9]
  have hwr : ∀ w < 4, InRegions t.wr (t.gpr .r10 + BitVec.ofNat 64 (4 * w)) 4 := by
    intro w hw; rw [inv.r10, Offset.add_add, inv.wr]; exact hpre.write j (by omega) w hw
  have harr : arraysR t = arraysR s₀ := by simp [arraysR, hr9]
  have hsep : Region.Disjoint ⟨t.gpr .r10, 16⟩ (arraysR t) := by
    rw [inv.r10, harr]; exact hpre.sep.sub_left (Offset.sub_base p (by omega))
  obtain ⟨t', ht', hmem, hr10, hrbx, hrcx, hzf, hrd, hwr', hregs⟩ := copyOutBody_ok hj t hroom hrb hwr hsep
  refine WP.of_runBlock ⟨t', ht', ?_⟩
  -- The lanes, as they were.
  have hlanes : ∀ w < 4, lv t (arrSlot ((w + 2) % 4)) j = lv s₀ (arrSlot ((w + 2) % 4)) j := by
    intro w hw
    simp only [lv, laneA, hr9]
    refine inv.frame.readW (Region.contains_self _ _) ?_ (by decide)
    intro r hr'; simp only [List.mem_singleton] at hr'; subst hr'
    exact fun x h1 h2 => hpre.sep x h2 (lane_inArrays (mem_arrA_of (Nat.mod_lt _ (by decide))) hj s₀ |>.byte h1)
  have inv' : CopyOutInv s₀ p m (j + 1) t' := by
    refine ⟨by omega, ?_, ?_, ?_, fun b hb i hi => ?_, ?_, fun r h1 h2 h3 h4 => ?_, by rw [hrd, inv.rd],
      by rw [hwr', inv.wr]⟩
    · rw [hr10, inv.r10, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, Offset.add_add]; congr 2
    · rw [hrbx, inv.rbx, show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_add]; congr 2
    · rw [hrcx, inv.rcx, show m - j = k by omega, cnt_sub1 hk1 (by omega)]; congr 1; omega
    · rw [hmem]
      by_cases hbj : b = j
      · subst hbj
        rw [show p + BitVec.ofNat 64 (16 * (m - k) + i) = t.gpr .r10 + BitVec.ofNat 64 i by
          rw [inv.r10, Offset.add_add]]
        unfold outWrites
        rw [block_writes _ _ (fun w => lv t (arrSlot ((w + 2) % 4)) j) hi, outByte, hlanes _ (by omega)]
      · rw [outWrites_off _ _ _ ?_]
        · exact inv.done b (by omega) i hi
        · rw [inv.r10, Offset.sub_toNat' p (by omega) (by omega)]
          split <;> omega
    · rw [hmem, inv.r10]
      exact outWrites_frame inv.frame (by omega) (by omega) _
    · rw [hregs r h1 h2 h3 h4]; exact inv.regs r h1 h2 h3 h4
  by_cases hk : k = 1
  · subst hk
    left
    have hjm : j + 1 = m := by omega
    refine ⟨?_, hjm ▸ inv'⟩
    show t'.zf.map (!·) = some false
    rw [hzf, inv.rcx, show m - (m - 1) = 1 by omega]; rfl
  · right
    refine ⟨?_, k - 1, by omega, ⟨by simpa [show j + 1 = m - (k - 1) by omega] using inv', by omega, by omega⟩⟩
    show t'.zf.map (!·) = some true
    rw [hzf, inv.rcx, show m - (m - k) = k by omega, cnt_ne_zero (by omega) (by omega)]; rfl

end VG.Proof.Seed.X86_64
