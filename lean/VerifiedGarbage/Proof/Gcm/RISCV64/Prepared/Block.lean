module

-- separate module: The block arithmetic proof checks intermediate product spills independently from the function prologue, loop and frame cleanup.

public import VerifiedGarbage.Impl.Gcm.RISCV64.Prepared
public import VerifiedGarbage.Proof.Gcm.RISCV64.Law
public import VerifiedGarbage.Proof.Framework.RISCV64.MRun
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Gcm.Spec

/-! # Product spills in a separate writable frame -/

@[expose] public section
namespace VG.Proof.Gcm.RISCV64
open VG.Impl.Gcm.RISCV64.Prepared
open VG VG.RISCV64 VG.Impl.Gcm.RISCV64

def spillWord (r : Reg) (s : State) (d : Nat) : BitVec 64 := s.mem.readW (s.gpr r + BitVec.ofNat 64 d) 64
def spillRead (r : Reg) (s : State) (d : Nat) : Prop :=
  d < 2048 ∧ (s.gpr r + BitVec.ofNat 64 d).toNat % 8 = 0 ∧ InRegions (s.rd ++ s.wr) (s.gpr r + BitVec.ofNat 64 d) 8
def sharedTail (r : Reg) (k : Nat) : List Instr :=
  [.load .d .t0 r (slot (k + 0)), .load .d .t1 r (slot (k + 1)), .load .d .t2 r (slot (k + 2)), .load .d .t3 r (slot (k + 3)),
   .logic .xor B (Z 0) .t1, .logic .xor B B .t3, .logic .xor B .t0 B,
   .logic .xor T PL .t0, .logic .xor T T .t2, .logic .xor T T .t3,
   .shift .sll .d .t4 .t2 63, .logic .xor T T .t4, .shift .sll .d .t4 .t2 62, .logic .xor T T .t4,
   .shift .sll .d .t4 .t2 57, .logic .xor T T .t4,
   .logic .xor B B .t2, .shift .srl .d .t4 .t2 1, .logic .xor B B .t4, .shift .srl .d .t4 .t2 2,
   .logic .xor B B .t4, .shift .srl .d .t4 .t2 7, .logic .xor B B .t4,
   .logic .xor Y0 .t1 T, .shift .srl .d .t4 T 1, .logic .xor Y0 Y0 .t4, .shift .srl .d .t4 T 2,
   .logic .xor Y0 Y0 .t4, .shift .srl .d .t4 T 7, .logic .xor Y0 Y0 .t4,
   .shift .sll .d .t4 T 63, .logic .xor Y1 B .t4, .shift .sll .d .t4 T 62, .logic .xor Y1 Y1 .t4,
   .shift .sll .d .t4 T 57, .logic .xor Y1 Y1 .t4,
   .addi DP DP 16, .addi N N (-1)]

theorem sharedTail_ok (r : Reg) (k : Nat) (s : State)
    (ht0 : r ≠ .t0) (ht1 : r ≠ .t1) (ht2 : r ≠ .t2) (h0 : spillRead r s (slot (k + 0))) (h1 : spillRead r s (slot (k + 1))) (h2 : spillRead r s (slot (k + 2)))
    (h3 : spillRead r s (slot (k + 3))) :
    WP isa (.block (sharedTail r k)) s fun t =>
      t.gpr Y0 ++ t.gpr Y1 = Holes.reduce (spillWord r s (slot (k + 1)))
        (spillWord r s (slot (k + 0)) ^^^ (s.gpr (Z 0) ^^^ spillWord r s (slot (k + 1)) ^^^ spillWord r s (slot (k + 3))))
        ((s.gpr PL ^^^ spillWord r s (slot (k + 0)) ^^^ spillWord r s (slot (k + 2))) ^^^ spillWord r s (slot (k + 3))) (spillWord r s (slot (k + 2))) ∧
      t.gpr DP = s.gpr DP + 16 ∧ t.gpr N = s.gpr N - 1 ∧
      Keep tailRegs s t ∧ t.mem = s.mem ∧ t.sp = s.sp := by
  obtain ⟨a0, b0, c0⟩ := h0
  obtain ⟨a1, b1, c1⟩ := h1
  obtain ⟨a2, b2, c2⟩ := h2
  obtain ⟨a3, b3, c3⟩ := h3
  unfold sharedTail
  simp only [PL, Z, B, T, Y0, Y1, DP, N, slot, spillWord] at *
  -- `mrun`, with the writes kept folded and read through (`RegUpd`): thirty-eight instructions.
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ↓RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, addr, State.load, Width.bytes, imm12,
    BitVec.setWidth_eq, read_eight, Option.bind_some, Option.map_some, Option.some.injEq,
    exists_eq_left', reduceCtorEq, Nat.reduceMul, Nat.reduceLT, Nat.reduceAdd, ↓reduceIte, and_self,
    and_true, Int.reduceLE, Int.reduceLT, Int.reduceNeg, BitVec.ofInt_neg, BitVec.ofInt_ofNat,
    ← BitVec.sub_eq_add_neg, a0, a1, a2, a3, b0, b1, b2, b3, c0, c1, c2, c3, ht0, ht1, ht2]
  simp only [Holes.reduce, Holes.foldLo, Holes.foldHi, tailRegs]
  simp only [Keep]
  repeat' (first
    | rfl
    | exact True.intro
    | constructor
    | (intro r hr
       simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
       simp only [↓RegUpd.gpr_write, hr, ↓reduceIte]))


/-- Aligned writable doubleword in a caller-selected temporary region. -/
def wrAt (s : State) (r : Reg) (d : Nat) : Prop :=
  d < 2048 ∧ (s.gpr r + BitVec.ofNat 64 d).toNat % 8 = 0 ∧
    InRegions s.wr (s.gpr r + BitVec.ofNat 64 d) 8

def stPair (r : Reg) (k : Nat) : List Instr :=
  [.store .d PL r (slot k), .store .d (Z 0) r (slot (k+1))]

theorem stPair_ok (s : State) (r : Reg) (k : Nat)
    (h0 : wrAt s r (slot k)) (h1 : wrAt s r (slot (k+1))) :
    WP isa (.block (stPair r k)) s fun t => t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.mem = (s.mem.writeW (s.gpr r + BitVec.ofNat 64 (slot k)) (s.gpr PL)).writeW
        (s.gpr r + BitVec.ofNat 64 (slot (k + 1))) (s.gpr (Z 0)) := by
  obtain ⟨a0,b0,c0⟩ := h0
  obtain ⟨a1,b1,c1⟩ := h1
  unfold stPair
  simp only [PL, Z] at *
  mrun [a0,a1,b0,b1,c0,c1]

/-- A store to either temporary slot leaves read-only key words intact. -/
theorem table_after_stPair {s t : State} {r : Reg} {k : Nat}
    (hm : t.mem = (s.mem.writeW (s.gpr r + BitVec.ofNat 64 (slot k)) (s.gpr PL)).writeW
        (s.gpr r + BitVec.ofNat 64 (slot (k + 1))) (s.gpr (Z 0)))
    (hg : t.gpr FP = s.gpr FP) {off : Nat}
    (h₀ : Mem.Sep (s.gpr FP + BitVec.ofNat 64 off) 8 (s.gpr r + BitVec.ofNat 64 (slot k)) 8)
    (h₁ : Mem.Sep (s.gpr FP + BitVec.ofNat 64 off) 8 (s.gpr r + BitVec.ofNat 64 (slot (k+1))) 8) :
    fw t off = fw s off := by
  rw [fw, hg, hm, Mem.readW_writeW_sep h₁ (by decide), Mem.readW_writeW_sep h₀ (by decide)]
  rfl

/-- The two doublewords just written, addressed from either spill pointer. -/
theorem spill_after_pair {s t : State} {r : Reg} {k : Nat}
    (hm : t.mem = (s.mem.writeW (s.gpr r + BitVec.ofNat 64 (slot k)) (s.gpr PL)).writeW
        (s.gpr r + BitVec.ofNat 64 (slot (k + 1))) (s.gpr (Z 0))) (hg : t.gpr r = s.gpr r)
    (hk : k + 1 < 256) :
    t.mem.readW (t.gpr r + BitVec.ofNat 64 (slot k)) 64 = s.gpr PL ∧
    t.mem.readW (t.gpr r + BitVec.ofNat 64 (slot (k + 1))) 64 = s.gpr (Z 0) := by
  rw [hg, hm]
  refine ⟨?_, Mem.readW_writeW_self64 _ _ _⟩
  rw [Mem.readW_writeW_sep (slot_sep _ (by omega_using [hk]) (by omega_using [hk]) (by omega_using [])) (by decide),
    Mem.readW_writeW_self64]

/-- The spill address class used by the three half products. The four temporary slots may
be within the original frame after its table or in a separate writable scratch area. -/
structure SpillSlots (s : State) (r : Reg) (first : Nat) : Prop where
  fit : first + 4 ≤ 256
  wr : ∀ k < 4, wrAt s r (slot (first + k))
  sep : ∀ j < 36, ∀ k < 4, Mem.Sep (s.gpr FP + BitVec.ofNat 64 (slot j)) 8
    (s.gpr r + BitVec.ofNat 64 (slot (first+k))) 8

theorem SpillSlots.keep {s t : State} {r : Reg} {first : Nat} {regs : List Reg}
    (h : SpillSlots s r first) (k : Keep regs s t) (hr : r ∉ regs) (hf : FP ∉ regs) : SpillSlots t r first := by
  refine ⟨h.fit, fun j hj => ?_, fun j hj l hl => ?_⟩
  · simpa only [wrAt, k.gpr hr, k.2.2] using h.wr j hj
  · rw [k.gpr hf, k.gpr hr]
    exact h.sep j hj l hl

theorem SpillSlots.legacy {s : State} (h : BlkPre s) : SpillSlots s FP 36 := by
  refine ⟨by decide, fun k hk => h.wr (36 + k) (by omega_using [hk]) (by omega_using [hk]), ?_⟩
  intro j hj k hk
  exact slot_sep _ (by omega_using [hj]) (by omega_using [hk]) (by omega_using [hj, hk])


theorem splitBlock_eq : blockCodeWith HP 0 =
    Impl.Words.RISCV64.loadBE64 .t0 .t2 DP 0 ++
    Impl.Words.RISCV64.loadBE64 .t1 .t2 DP 8 ++ (bXor ++ (pmCode Y0 (slot 0) ++ (stPair .a0 0 ++
    (pmCode Y1 (slot 12) ++ (stPair .a0 2 ++ (([.logic .xor Y0 Y0 Y1] : List Instr) ++ (pmCode Y0 (slot 24) ++ sharedTail .a0 0)))))))

  := by simp only [blockCodeWith,bXor,stPair,sharedTail, List.append_assoc,List.cons_append,List.nil_append];rfl

theorem spillWord_congr {s t : State} {r : Reg} (hm : t.mem = s.mem) (hg : t.gpr r = s.gpr r)
    (d : Nat) : spillWord r t d = spillWord r s d := by rw [spillWord, hm, hg];rfl

theorem SpillSlots.read {s : State} {r : Reg} {first : Nat} (h : SpillSlots s r first) {k : Nat} (hk : k < 4) :
    spillRead r s (slot (first + k)) := by
  obtain ⟨d,a,z,hz,c⟩ := h.wr k hk
  exact ⟨d,a,z,List.mem_append_right _ hz,c⟩

theorem readSpillOther {s t : State} {r : Reg} {k : Nat}
    (hm : t.mem = (s.mem.writeW (s.gpr r + BitVec.ofNat 64 (slot k)) (s.gpr PL)).writeW
        (s.gpr r + BitVec.ofNat 64 (slot (k + 1))) (s.gpr (Z 0)))
    (hg : t.gpr r = s.gpr r) {j : Nat} (hk : k+1 < 256) (hj : j < 256)
    (h0 : j ≠ k) (h1 : j ≠ k+1) :
    spillWord r t (slot j) = spillWord r s (slot j) := by
  simp only [spillWord, hg, hm]
  rw [Mem.readW_writeW_sep (slot_sep _ (by omega_using [hj]) (by omega_using [hk]) h1) (by decide),
    Mem.readW_writeW_sep (slot_sep _ (by omega_using [hj]) (by omega_using [hk]) h0) (by decide)]

structure SplitPre (s : State) : Prop where
  masks : Masks s
  rd : ∀ k < 36, Rd8 s (8*k)
  wr : SpillSlots s .a0 0
  dat : InRegions (s.rd ++ s.wr) (s.gpr DP) 16
theorem splitBlock_ok (s : State) (hp : SplitPre s) :
    WP isa (.block (blockCodeWith HP 0)) s fun t =>
      t.gpr Y0 ++ t.gpr Y1 = mulT (s.gpr Y0 ^^^ ByteLoad.be64 s.mem (s.gpr DP) 0)
        (s.gpr Y1 ^^^ ByteLoad.be64 s.mem (s.gpr DP) 8) (fw s) ∧
      t.gpr DP = s.gpr DP + 16 ∧ t.gpr N = s.gpr N - 1 ∧ Keep blockRegs s t ∧ t.sp = s.sp ∧
      (∀ k < 36, fw t (8 * k) = fw s (8 * k)) ∧
      Frame [⟨s.gpr .a0, 32⟩] s.mem t.mem := by
  obtain ⟨hK, hR, hW, hD⟩ := hp
  obtain mk : ∀ (rs : List Reg), Reg.s0 ∉ rs → Reg.s1 ∉ rs → Reg.s2 ∉ rs → Reg.s3 ∉ rs →
      ∀ i < 4, Impl.Gcm.RISCV64.K i ∉ rs := by
    intro rs a b c d i hi; interval_cases i; exacts [a, b, c, d]
  obtain mk' : ∀ (rs : List Reg), Reg.s0 ∉ rs → Reg.s1 ∉ rs → Reg.s2 ∉ rs → Reg.s3 ∉ rs → Reg.s9 ∉ rs → Reg.a0 ∉ rs →
      ∀ {u v : State}, Keep rs u v → v.mem = u.mem → Masks u → (∀ k < 36, Rd8 u (8*k)) → SpillSlots u .a0 0 →
      Masks v ∧ (∀ k < 36, Rd8 v (8*k)) ∧ SpillSlots v .a0 0 ∧ (∀ d, fw v d = fw u d) := by
    intro rs a b c d e f u v hk hm hKu hRu hWu
    exact ⟨Keep.masks hk hKu (mk rs a b c d), fun k hk' => Keep.rd8 hk e (hRu k hk'),
      hWu.keep hk f e, fw_congr hm (Keep.gpr hk e)⟩
  obtain hR12 : ∀ {u : State} (o : Nat), (∀ k < 36, Rd8 u (8 * k)) → o + 12 ≤ 36 →
      ∀ k < 12, Rd8 u (slot o + 8 * k) := fun o h ho k hk => by
    rw [show slot o + 8 * k = 8 * (o + k) by simp only [slot]; omega_using []]; exact h _ (by omega_using [ho, hk])
  rw [splitBlock_eq, WP.block_append_iff]
  refine WP.mono (ld2_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s hD)
    fun u1 ⟨x0, x1, k1, m1, p1⟩ => ?_
  obtain ⟨K1, R1, W1, F1⟩ := mk' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) k1 m1 hK hR hW
  rw [WP.block_append_iff]
  refine WP.mono (bXor_ok u1) fun u2 ⟨y0, y1, k2, m2, p2⟩ => ?_
  obtain ⟨K2, R2, W2, F2⟩ := mk' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) k2 m2 K1 R1 W1
  rw [WP.block_append_iff]
  refine WP.mono (pm_ok u2 (X := Y0) (by decide) (slot 0) K2 (hR12 0 R2 (by decide)))
    fun u3 ⟨l1, l2, k3, m3, p3⟩ => ?_
  obtain ⟨K3, R3, W3, F3⟩ := mk' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) k3 m3 K2 R2 W2
  rw [WP.block_append_iff]
  refine WP.mono (stPair_ok u3 .a0 0 (W3.wr 0 (by decide)) (W3.wr 1 (by decide)))
    fun u4 ⟨g4, rd4, wr4, p4, m4⟩ => ?_
  obtain k4 : Keep [] u3 u4 := ⟨fun r _ => by rw [g4], rd4, wr4⟩
  obtain fp4 : u4.gpr FP = u3.gpr FP := by rw [g4]
  obtain K4 : Masks u4 := Keep.masks k4 K3 (mk _ (by decide) (by decide) (by decide) (by decide))
  obtain R4 : ∀ k < 36, Rd8 u4 (8 * k) := fun k hk => Keep.rd8 k4 (by decide) (R3 k hk)
  obtain W4 := W3.keep k4 (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pm_ok u4 (X := Y1) (by decide) (slot 12) K4 (hR12 12 R4 (by decide)))
    fun u5 ⟨h1, h2, k5, m5, p5⟩ => ?_
  obtain ⟨K5, R5, W5, F5⟩ := mk' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) k5 m5 K4 R4 W4
  rw [WP.block_append_iff]
  refine WP.mono (stPair_ok u5 .a0 2 (W5.wr 2 (by decide)) (W5.wr 3 (by decide)))
    fun u6 ⟨g6, rd6, wr6, p6, m6⟩ => ?_
  obtain k6 : Keep [] u5 u6 := ⟨fun r _ => by rw [g6], rd6, wr6⟩
  obtain fp6 : u6.gpr FP = u5.gpr FP := by rw [g6]
  obtain K6 : Masks u6 := Keep.masks k6 K5 (mk _ (by decide) (by decide) (by decide) (by decide))
  obtain R6 : ∀ k < 36, Rd8 u6 (8 * k) := fun k hk => Keep.rd8 k6 (by decide) (R5 k hk)
  rw [WP.block_append_iff]
  refine WP.mono (bY_ok u6) fun u7 ⟨e7, k7, m7, p7⟩ => ?_
  obtain ⟨K7, R7, W7, F7⟩ := mk' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) k7 m7 K6 R6
    (W5.keep k6 (by decide) (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (pm_ok u7 (X := Y0) (by decide) (slot 24) K7 (hR12 24 R7 (by decide)))
    fun u8 ⟨n1, n2, k8, m8, p8⟩ => ?_
  obtain ⟨-, _, W8, F8⟩ := mk' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) k8 m8 K7 R7
    W7
  refine WP.mono (sharedTail_ok .a0 0 u8 (by decide) (by decide) (by decide) (W8.read (k:=0) (by decide)) (W8.read (k:=1) (by decide)) (W8.read (k:=2) (by decide)) (W8.read (k:=3) (by decide)))
    fun t ⟨e, d, n, kt, mt, pt⟩ => ?_
  -- The frame pointer and the other registers through the steps.
  obtain f3 : u3.gpr .a0 = s.gpr .a0 := by
    rw [Keep.gpr k3 (by decide), Keep.gpr k2 (by decide), Keep.gpr k1 (by decide)]
  obtain f5 : u5.gpr .a0 = s.gpr .a0 := by rw [Keep.gpr k5 (by decide), g4, f3]
  obtain ⟨s36, s37⟩ := spill_after_pair (k:=0) m4 (congrFun g4 .a0) (by decide)
  obtain ⟨s38, s39⟩ := spill_after_pair (k:=2) m6 (congrFun g6 .a0) (by decide)
  obtain st4 : ∀ j < 36, fw u4 (8*j) = fw u3 (8*j) :=
    fun j hj => table_after_stPair m4 fp4 (W3.sep j hj 0 (by decide)) (W3.sep j hj 1 (by decide))
  obtain st6 : ∀ j < 36, fw u6 (8*j) = fw u5 (8*j) :=
    fun j hj => table_after_stPair m6 fp6 (W5.sep j hj 2 (by decide)) (W5.sep j hj 3 (by decide))
  obtain F86 : ∀ d, fw u8 d = fw u6 d := fun d => by rw [F8, F7]
  obtain S86 : ∀ d, spillWord .a0 u8 d = spillWord .a0 u6 d :=
    spillWord_congr (m8.trans m7) ((Keep.gpr k8 (by decide)).trans (Keep.gpr k7 (by decide)))
  obtain S5 : ∀ d, spillWord .a0 u5 d = spillWord .a0 u4 d := spillWord_congr m5 (Keep.gpr k5 (by decide))
  obtain g36 : spillWord .a0 u8 (slot 0) = u3.gpr PL := by
    rw [S86, readSpillOther m6 (congrFun g6 .a0) (by decide) (by decide) (by decide) (by decide), S5]; exact s36
  obtain g37 : spillWord .a0 u8 (slot 1) = u3.gpr (Z 0) := by
    rw [S86, readSpillOther m6 (congrFun g6 .a0) (by decide) (by decide) (by decide) (by decide), S5]; exact s37
  obtain g38 : spillWord .a0 u8 (slot 2) = u5.gpr PL := by rw [S86]; exact s38
  obtain g39 : spillWord .a0 u8 (slot 3) = u5.gpr (Z 0) := by rw [S86]; exact s39
  -- `Y` through the steps.
  obtain ya : u2.gpr Y0 = s.gpr Y0 ^^^ ByteLoad.be64 s.mem (s.gpr DP) 0 := by
    rw [y0, Keep.gpr k1 (by decide), x0]
  obtain yb : u2.gpr Y1 = s.gpr Y1 ^^^ ByteLoad.be64 s.mem (s.gpr DP) 8 := by
    rw [y1, Keep.gpr k1 (by decide), x1]
  obtain y4 : u4.gpr Y1 = u2.gpr Y1 := by rw [g4, Keep.gpr k3 (by decide)]
  obtain y6a : u6.gpr Y0 = u2.gpr Y0 := by
    rw [g6, Keep.gpr k5 (by decide), g4, Keep.gpr k3 (by decide)]
  obtain y6b : u6.gpr Y1 = u2.gpr Y1 := by rw [g6, Keep.gpr k5 (by decide), y4]
  -- The tables.
  obtain T0 : ∀ o j, fw u2 (o + j) = fw s (o + j) := fun o j => by rw [F2, F1]
  obtain T12 : ∀ j < 12, fw u4 (slot 12 + 8 * j) = fw s (slot 12 + 8 * j) := fun j hj => by
    rw [show slot 12 + 8 * j = 8 * (12 + j) by simp only [slot]; omega_using [], st4 _ (by omega_using [hj]),
      F3, F2, F1]
  obtain T24 : ∀ j < 12, fw u7 (slot 24 + 8 * j) = fw s (slot 24 + 8 * j) := fun j hj => by
    rw [show slot 24 + 8 * j = 8 * (24 + j) by simp only [slot]; omega_using [], F7, st6 _ (by omega_using [hj]),
      F5, st4 _ (by omega_using [hj]), F3, F2, F1]
  obtain hl : pmT (u2.gpr Y0) (fun j => fw u2 (slot 0 + 8 * j)) (fun j => fw u2 (slot 0 + 32 + 8 * j))
      (fun j => fw u2 (slot 0 + 64 + 8 * j)) = pmT (s.gpr Y0 ^^^ ByteLoad.be64 s.mem (s.gpr DP) 0)
      (fun j => fw s (slot 0 + 8 * j)) (fun j => fw s (slot 0 + 32 + 8 * j)) (fun j => fw s (slot 0 + 64 + 8 * j)) := by
    rw [ya]; exact pmT_congr _ (fun j _ => T0 _ _) (fun j _ => T0 _ _) (fun j _ => T0 _ _)
  obtain hh : pmT (u4.gpr Y1) (fun j => fw u4 (slot 12 + 8 * j)) (fun j => fw u4 (slot 12 + 32 + 8 * j))
      (fun j => fw u4 (slot 12 + 64 + 8 * j)) = pmT (s.gpr Y1 ^^^ ByteLoad.be64 s.mem (s.gpr DP) 8)
      (fun j => fw s (slot 12 + 8 * j)) (fun j => fw s (slot 12 + 32 + 8 * j))
      (fun j => fw s (slot 12 + 64 + 8 * j)) := by
    rw [y4, yb]
    refine pmT_congr _ (fun j hj => T12 j (by omega_using [hj])) (fun j hj => ?_) (fun j hj => ?_)
    · rw [show slot 12 + 32 + 8 * j = slot 12 + 8 * (4 + j) by simp only [slot]; omega_using []]; exact T12 _ (by omega_using [hj])
    · rw [show slot 12 + 64 + 8 * j = slot 12 + 8 * (8 + j) by simp only [slot]; omega_using []]; exact T12 _ (by omega_using [hj])
  obtain hm : pmT (u7.gpr Y0) (fun j => fw u7 (slot 24 + 8 * j)) (fun j => fw u7 (slot 24 + 32 + 8 * j))
      (fun j => fw u7 (slot 24 + 64 + 8 * j)) = pmT ((s.gpr Y0 ^^^ ByteLoad.be64 s.mem (s.gpr DP) 0) ^^^
        (s.gpr Y1 ^^^ ByteLoad.be64 s.mem (s.gpr DP) 8))
      (fun j => fw s (slot 24 + 8 * j)) (fun j => fw s (slot 24 + 32 + 8 * j))
      (fun j => fw s (slot 24 + 64 + 8 * j)) := by
    rw [e7, y6a, y6b, ya, yb]
    refine pmT_congr _ (fun j hj => T24 j (by omega_using [hj])) (fun j hj => ?_) (fun j hj => ?_)
    · rw [show slot 24 + 32 + 8 * j = slot 24 + 8 * (4 + j) by simp only [slot]; omega_using []]; exact T24 _ (by omega_using [hj])
    · rw [show slot 24 + 64 + 8 * j = slot 24 + 8 * (8 + j) by simp only [slot]; omega_using []]; exact T24 _ (by omega_using [hj])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e, g36, g37, g38, g39, n1, n2, l1, l2, h1, h2, hl, hh, hm]
    rfl
  · rw [d, Keep.gpr k8 (by decide), Keep.gpr k7 (by decide), g6, Keep.gpr k5 (by decide), g4,
      Keep.gpr k3 (by decide), Keep.gpr k2 (by decide), Keep.gpr k1 (by decide)]
  · rw [n, Keep.gpr k8 (by decide), Keep.gpr k7 (by decide), g6, Keep.gpr k5 (by decide), g4,
      Keep.gpr k3 (by decide), Keep.gpr k2 (by decide), Keep.gpr k1 (by decide)]
  · refine Keep.mono (Keep.trans k1 (Keep.trans k2 (Keep.trans k3 (Keep.trans k4 (Keep.trans k5
      (Keep.trans k6 (Keep.trans k7 (Keep.trans k8 kt)))))))) ?_
    simp only [pmRegs, holesRegs, tailRegs, blockRegs]; decide
  · rw [pt, p8, p7, p6, p5, p4, p3, p2, p1]
  · intro k hk
    rw [fw_congr mt (Keep.gpr kt (by decide)), F86, st6 k (by omega_using [hk]), F5,
      st4 k (by omega_using [hk]), F3, F2, F1]
  · rw [mt, m8, m7, m6, m5, m4, m3, m2, m1, f5, f3]
    obtain c : ∀ k, k < 4 → (⟨s.gpr .a0, 32⟩ : Region).Contains
        (s.gpr .a0 + BitVec.ofNat 64 (slot k)) (64/8) := fun k hk => Offset.contains_base _ (by simp only [slot]; omega_using [hk]) (by simp only [slot]; omega_using [hk])
    exact (((Frame.refl _ _).writeW List.mem_cons_self _ (c 0 (by decide))).writeW
      List.mem_cons_self _ (c 1 (by decide))).writeW List.mem_cons_self _ (c 2 (by decide))
      |>.writeW List.mem_cons_self _ (c 3 (by decide))


open VG.RISCV64.Steps
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom mul ofBytes)
structure SplitInv (H Y₀ : Block) (D : Addr) (m₀ : Mem) (n₀ : Nat) (sY : State) (i : Nat) (s : State) : Prop where
  y : w2 (s.gpr Y0) (s.gpr Y1) = ghashFrom H Y₀ (blocksAt m₀ D i)
  dp : s.gpr DP = D + BitVec.ofNat 64 (16 * i)
  n : s.gpr N = BitVec.ofNat 64 (n₀ - i)
  keep : Keep blockRegs sY s
  sp : s.sp = sY.sp
  tab : ∀ k < 36, fw s (8 * k) = fw sY (8 * k)
  frame : Frame [⟨sY.gpr .a0, 32⟩] sY.mem s.mem

/-- What the blocks need of the state they start from. -/
structure SplitLoopPre (H : Block) (D : Addr) (m₀ : Mem) (n₀ : Nat) (sY : State) : Prop where
  slots : SpillSlots sY .a0 0
  tableRead : ∀ k < 36, Rd8 sY (8 * k)
  masks : Masks sY
  key : ∃ h0 h1, H = h0 ++ h1 ∧ Tab (Holes.key0 h0 h1) (Holes.key1 h0 h1) (fw sY)
  dat : ∀ i < n₀, InRegions (sY.rd ++ sY.wr) (D + BitVec.ofNat 64 (16 * i)) 16
  bytes : ∀ i < n₀, ∀ j < 16, ∀ m : Mem, Frame [⟨sY.gpr .a0, 32⟩] sY.mem m →
    m (D + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 j) = m₀ (D + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 j)

theorem split_step {H Y₀ : Block} {D : Addr} {m₀ : Mem} {n₀ : Nat} {sY : State} (hL : SplitLoopPre H D m₀ n₀ sY)
    (hn₀ : n₀ < 2 ^ 64) {i : Nat} (hi : i < n₀) {s : State} (hs : SplitInv H Y₀ D m₀ n₀ sY i s) :
    WP isa (.block (blockCodeWith HP 0)) s (SplitInv H Y₀ D m₀ n₀ sY (i + 1)) := by
  obtain ⟨slots, tableRead, hK, ⟨h0, h1, hH, ht⟩, hd, hb⟩ := hL
  obtain pre : SplitPre s := ⟨Keep.masks hs.keep hK (fun j hj => by interval_cases j <;> decide),
    fun k hk => Keep.rd8 hs.keep (by decide) (tableRead k hk), slots.keep hs.keep (by decide) (by decide),
    by rw [hs.dp, hs.keep.2.1, hs.keep.2.2]; exact hd i hi⟩
  refine WP.mono (splitBlock_ok s pre) fun t ⟨ey, ed, en, kt, pt, tt, ft⟩ => ?_
  obtain tabs : Tab (Holes.key0 h0 h1) (Holes.key1 h0 h1) (fw s) := fun i' hi' j hj => by
    rw [hs.tab _ (by omega_using [hi', hj])]; exact ht i' hi' j hj
  -- The block, from the bytes at `DP`.
  obtain hx : ByteLoad.be64 s.mem (s.gpr DP) 0 ++ ByteLoad.be64 s.mem (s.gpr DP) 8 =
      blockAt m₀ (D + BitVec.ofNat 64 (16 * i)) := by
    rw [show ByteLoad.be64 s.mem (s.gpr DP) 0 ++ ByteLoad.be64 s.mem (s.gpr DP) 8 = hOf s.mem (s.gpr DP) from rfl,
      ← blockAt_hOf, hs.dp]
    exact Proof.Gcm.blockAt_congr fun j hj => hb i hi j hj _ hs.frame
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ey.trans ?_
    rw [mulT_tab tabs, Holes.mulK_eq, ← hH, ← BitVec.xor_append, hx, Proof.Gcm.ghashFrom_blocksAt_succ]
    exact congrArg (fun v => mul (v ^^^ _) H) hs.y
  · rw [ed, hs.dp, BitVec.add_assoc, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, BitVec.ofNat_add_ofNat]
    congr 2
  · rw [en, hs.n]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (a := n₀ - i) (by omega_using [hn₀])]
    omega_using [hi]
  · exact Keep.mono (Keep.trans hs.keep kt) (by simp only [blockRegs]; decide)
  · rw [pt, hs.sp]
  · intro k hk; rw [tt k hk, hs.tab k hk]
  · rw [Keep.gpr hs.keep (r:=.a0) (by decide)] at ft; exact hs.frame.trans ft

theorem split_loop {H Y₀ : Block} {D : Addr} {m₀ : Mem} {n₀ : Nat} {sY : State} (hL : SplitLoopPre H D m₀ n₀ sY)
    (hn₀ : n₀ < 2 ^ 64) (hpos : 0 < n₀) {s : State} (hs : SplitInv H Y₀ D m₀ n₀ sY 0 s) :
    WP isa (.loop (.block (blockCodeWith HP 0)) (.nonzero N)) s (SplitInv H Y₀ D m₀ n₀ sY n₀) := by
  refine WP.loop (M := isa) (fun k s' => ∃ i, k = n₀ - i ∧ i < n₀ ∧ SplitInv H Y₀ D m₀ n₀ sY i s')
    (fun k s' ⟨i, hk, hi, hb⟩ => WP.mono (split_step hL hn₀ hi hb) fun s'' hb' => ?_) n₀ s
    ⟨0, rfl, hpos, hs⟩
  obtain hev := eval_nonzero_ofNat s'' N (k := n₀ - (i + 1)) (by omega_using [hn₀]) hb'.n
  by_cases hl : i + 1 = n₀
  · exact .inl ⟨by rw [hev]; simp [hl], hl ▸ hb'⟩
  · exact .inr ⟨by rw [hev]; simp; omega_using [hi, hl], n₀ - (i + 1), by omega_using [hk, hi], i + 1, rfl, by omega_using [hi, hl], hb'⟩

end VG.Proof.Gcm.RISCV64
