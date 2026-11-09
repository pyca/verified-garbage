module

public import VerifiedGarbage.Spec.TripleDes
public import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.TripleDes.RISCV64.Bitsliced.Pass
public import VerifiedGarbage.Proof.TripleDes.RISCV64.Bitsliced.Transpose
public import VerifiedGarbage.Proof.TripleDes.Bitslice.Tdea
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Loops
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64

/-!
# Bitsliced Triple DES ECB on RISC-V

Blocks as little-endian words (`readW_bit`, `blockAt_of_readW`: a block's
little-endian word holds bit `i` of the block, big-endian as `decodeBlock`
reads it, at bit `i ^^^ 56`).

A batch of `k = min(n, 64)` blocks (`kOf`) is copied into the state words a
byte at a time, transposed (lane `b` is then IP of block `b`), put through
the three passes, transposed back and copied out; then the data pointer
`a1` moves past it and the count `a2` drops by `k`: each block becomes its
TDEA encryption or decryption (`batch_ok`).

`ecb_wp`: in a frame of 1056 bytes below the stack pointer, the caller's
`s1`–`s11`, `ra` and `s0` saved, the schedules copied and the masks stored
(`setup_ok`), the batches (`loop_ok`), the frame zeroed below the saved
registers and the registers restored (`finish_ok`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64.Bitsliced

open VG VG.Spec.TripleDes

theorem xor56_eq : ∀ p < 64, p ^^^ 56 = 8 * (7 - p / 8) + p % 8 := by decide

/-- Bit `j` of the little-endian word at `p`: bit `j % 8` of byte `j / 8`. -/
theorem readW_getLsbD (m : Mem) (p : Addr) {j : Nat} (hj : j < 64) :
    (m.readW p 64).getLsbD j = (m (p + BitVec.ofNat 64 (j / 8))).getLsbD (j % 8) := by
  rw [← Mem.extractLsb'_read m p (n := 8) (j := j / 8) (by omega), BitVec.getLsbD_extractLsb']
  simp only [Mem.readW, BitVec.setWidth_eq, show j % 8 < 8 from Nat.mod_lt _ (by decide),
    decide_true, Bool.true_and]
  congr 1; omega

/-- Bit `8 (7 - q) + r` of a block's big-endian word: bit `r` of byte `q`. -/
theorem catBlock_bit (b : Block) {q r : Nat} (hq : q < 8) (hr : r < 8) :
    (VG.Proof.TripleDes.catBlock b).getLsbD (8 * (7 - q) + r) = b[q].getLsbD r := by
  have hcases : ∀ k < 8, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by decide
  rcases hcases q hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [VG.Proof.TripleDes.catBlock, BitVec.getLsbD_append] <;>
      (repeat' split) <;> first | omega | (congr 1; omega)

/-- The little-endian word of a block, bit by bit. -/
theorem readW_bit (m : Mem) (p : Addr) {j : Nat} (hj : j < 64) :
    (m.readW p 64).getLsbD j = (decodeBlock (blockAt m p)).getLsbD (j ^^^ 56) := by
  rw [VG.Proof.TripleDes.decodeBlock_cat, xor56_eq j hj,
    catBlock_bit _ (by omega) (Nat.mod_lt _ (by decide)), readW_getLsbD m p hj]
  simp [blockAt]

/-- A word whose bits are those of `x` at `j ^^^ 56` is the little-endian word of
the block `encodeBlock x`. -/
theorem blockAt_of_readW (m : Mem) (p : Addr) (x : BitVec 64)
    (h : ∀ j < 64, (m.readW p 64).getLsbD j = x.getLsbD (j ^^^ 56)) :
    blockAt m p = encodeBlock x := by
  apply Vector.ext
  intro i hi
  simp only [blockAt, encodeBlock, Vector.getElem_ofFn]
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  have hj : 8 * i + r < 64 := by omega
  have e := h (8 * i + r) hj
  rw [readW_getLsbD m p hj, xor56_eq _ hj, show (8 * i + r) / 8 = i by omega,
    show (8 * i + r) % 8 = r by omega] at e
  rw [e]
  simp only [BitVec.getLsbD_setWidth, hr, decide_true, Bool.true_and, BitVec.getLsbD_ushiftRight]



open VG VG.RISCV64 VG.Impl.TripleDes.RISCV64.Bitslice VG.Spec.TripleDes VG.Impl.Words.RISCV64
open VG.Proof.TripleDes.Bitslice (ipLane transposeW tdeaW blockOut wAt)

/-- The batch's blocks: `min(n, 64)`. -/
def kOf (s : State) : Nat := min (s.gpr .a2).toNat 64

theorem kOf_le (s : State) : kOf s ≤ 64 := Nat.min_le_right _ _

/-! ## The batch's bytes -/

theorem batchBytes_ok (s : State) :
    WP isa batchBytes s fun s' => s'.gpr .s5 = BitVec.ofNat 64 (8 * kOf s) ∧
      (∀ r, r ≠ .t0 → r ≠ .s5 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.wr = s.wr := by
  unfold batchBytes
  have e₁ := exec_shift_d (s := s) (op := .srl) (d := .t0) (n := .a2) (sh := 6) (by decide)
  let s₁ := s.write .t0 (s.gpr .a2 >>> 6)
  apply WP.seq
  refine WP.of_runBlock ⟨s₁, by rw [runBlock_cons, e₁, runStep_some, runBlock_nil], ?_⟩
  have z : (s₁.gpr .t0 == 0) = decide ((s.gpr .a2).toNat < 64) := by
    simp only [s₁, RegUpd.gpr_write_self]
    by_cases h : (s.gpr .a2).toNat < 64
    · simp only [h, decide_true, beq_iff_eq]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      show _ = 0
      omega
    · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at this
      change _ = 0 at this
      omega
  refine WP.ite _ (by rw [Steps.eval_zero, z]) (fun hlt => ?_) (fun hge => ?_)
  · have hlt : (s.gpr .a2).toNat < 64 := by simpa using hlt
    have e₂ := exec_shift_d (s := s₁) (op := .sll) (d := .s5) (n := .a2) (sh := 3) (by decide)
    refine WP.of_runBlock ⟨s₁.write .s5 (s₁.gpr .a2 <<< 3),
      by rw [runBlock_cons, e₂, runStep_some, runBlock_nil], ?_, ?_, rfl, rfl⟩
    · simp only [RegUpd.gpr_write_self, s₁, RegUpd.gpr_write, reduceCtorEq, ite_false]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, kOf, Nat.min_eq_left (by omega),
        Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    · intro r h0 h5
      simp only [s₁, RegUpd.gpr_write, h0, h5, ite_false]
  · have hge : ¬ (s.gpr .a2).toNat < 64 := by simpa using hge
    have e₂ := exec_li (s := s₁) (d := .s5) (imm := 512) (by decide)
    refine WP.of_runBlock ⟨s₁.write .s5 (BitVec.ofInt 64 512),
      by rw [runBlock_cons, e₂, runStep_some, runBlock_nil], ?_, ?_, rfl, rfl⟩
    · rw [RegUpd.gpr_write_self, kOf, Nat.min_eq_right (by omega)]; rfl
    · intro r h0 h5
      simp only [s₁, RegUpd.gpr_write, h0, h5, ite_false]

/-! ## Copies -/

theorem sep_of_disjoint {a b : Addr} {n k : Nat} (h : (⟨a, n⟩ : Region).Disjoint ⟨b, k⟩) :
    Mem.Sep a n b k := fun x h₁ h₂ =>
  h x (by simp only [Region.Contains]; omega) (by simp only [Region.Contains]; omega)

/-- Copy `s5 = N` bytes from `src` to `dst`. -/
theorem copyBytes_ok {src dst : Reg}
    (hd : dst ≠ .t2 ∧ dst ≠ .t3 ∧ dst ≠ .t4) (s : State) {N : Nat} (hN : 0 < N) (hN' : N < 2 ^ 64)
    (hc : s.gpr .s5 = BitVec.ofNat 64 N)
    (hr : ∀ i < N, InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < N, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 i) 1)
    (hsep : Mem.Sep (s.gpr dst) N (s.gpr src) N) :
    WP isa (copyBytes src dst) s fun t =>
      (∀ i < N, t.mem (s.gpr dst + BitVec.ofNat 64 i) = s.mem (s.gpr src + BitVec.ofNat 64 i)) ∧
      Frame [⟨s.gpr dst, N⟩] s.mem t.mem ∧ (∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → t.gpr r = s.gpr r) ∧
      t.wr = s.wr := by
  unfold copyBytes
  have e₁ := exec_addi (s := s) (d := .t2) (n := src) (imm := 0) (by decide)
  let s₁ := s.write .t2 (s.gpr src + BitVec.ofInt 64 0)
  have e₂ := exec_addi (s := s₁) (d := .t3) (n := dst) (imm := 0) (by decide)
  let s₂ := s₁.write .t3 (s₁.gpr dst + BitVec.ofInt 64 0)
  have e₃ := exec_addi (s := s₂) (d := .t4) (n := .s5) (imm := 0) (by decide)
  let s₃ := s₂.write .t4 (s₂.gpr .s5 + BitVec.ofInt 64 0)
  have z : BitVec.ofInt 64 0 = 0#64 := rfl
  have g : ∀ r, r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → s₃.gpr r = s.gpr r := fun r a b c => by
    simp only [s₃, s₂, s₁, RegUpd.gpr_write, a, b, c, ite_false]
  have t2 : s₃.gpr .t2 = s.gpr src := by
    simp only [s₃, s₂, s₁, RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, z, BitVec.add_zero]
  have t3 : s₃.gpr .t3 = s.gpr dst := by
    simp only [s₃, s₂, s₁, RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, z, BitVec.add_zero, hd.1]
  have t4 : s₃.gpr .t4 = BitVec.ofNat 64 N := by
    simp only [s₃, s₂, s₁, RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, z, BitVec.add_zero, hc]
  apply WP.seq
  refine WP.of_runBlock ⟨s₃, by
    rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃, runStep_some,
      runBlock_nil], ?_⟩
  refine WP.mono (copyLoop_ok (tmp := .t1) (src := .t2) (dst := .t3) (cnt := .t4) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) s₃ hN hN' t4 (fun i hi => by rw [t2]; exact hr i hi)
    (fun i hi => by rw [t3]; exact hw i hi) (by rw [t2, t3]; exact hsep)) fun t ⟨tc, tf, tk⟩ => ?_
  refine ⟨fun i hi => by rw [← t3, tc i hi, t2]; rfl, by rw [← t3]; exact tf, fun r a b c e => ?_, tk.2.2⟩
  rw [tk.1 r (by simp [a, b, c, e]), g r b c e]

/-- A little-endian word from its bytes. -/
theorem readW_of_bytes {m m' : Mem} {a b : Addr} (h : ∀ i < 8, m' (b + BitVec.ofNat 64 i) = m (a + BitVec.ofNat 64 i)) :
    m'.readW b 64 = m.readW a 64 := by
  simp only [Mem.readW, BitVec.setWidth_eq]
  exact Mem.read_eq_of_bytes fun i hi => by rw [h i hi, Mem.extractLsb'_read m a hi]

/-! ## The batch -/

/-- The data: the `n` blocks at `D`, writable, apart from the frame and not
wrapping around. -/
structure Data (s : State) (D : Addr) (n : Nat) : Prop where
  wr : ∀ i < 8 * n, InRegions s.wr (D + BitVec.ofNat 64 i) 1
  fit : D.toNat + 8 * n ≤ 2 ^ 64
  sep : (⟨D, 8 * n⟩ : Region).Disjoint (frameR s)

theorem Data.byte {s : State} {D : Addr} {n : Nat} (h : Data s D n) {i : Nat} (hi : i < 8 * n) :
    InRegions s.wr (D + BitVec.ofNat 64 i) 1 :=
  h.wr i hi

/-- What a batch needs: the frame, the masks, a block left, and the data. -/
structure BatchPre (s : State) : Prop where
  room : Room s
  masks : MasksAt s
  pos : 1 ≤ (s.gpr .a2).toNat
  data : Data s (s.gpr .a1) (s.gpr .a2).toNat

structure BatchPost (d : Direction) (s s' : State) : Prop where
  s0 : s'.gpr .s0 = s.gpr .s0
  a1 : s'.gpr .a1 = wAt (s.gpr .a1) (kOf s)
  a2 : s'.gpr .a2 = s.gpr .a2 - BitVec.ofNat 64 (kOf s)
  wr : s'.wr = s.wr
  out : ∀ b < kOf s, blockAt s'.mem (wAt (s.gpr .a1) b) =
    blockOut (scheduleAt s.mem (schedA s)) d (blockAt s.mem (wAt (s.gpr .a1) b))
  frame : Frame [stR s, ⟨s.gpr .a1, 8 * kOf s⟩] s.mem s'.mem

/-- The state words' region is inside the frame. -/
theorem stR_sub (s : State) : Region.Sub (stR s) (frameR s) := Region.sub_prefix (by decide)

theorem sched_frame {s : State} (h : Room s) {m : Mem} (hf : Frame [stR s] s.mem m) :
    scheduleAt m (schedA s) = scheduleAt s.mem (schedA s) :=
  VG.Proof.TripleDes.scheduleAt_eq_of_frame _ hf fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    have := h.fit
    exact Offset.disjoint_base _ (by unfold schedOff; omega) (by unfold schedOff frameBytes at *; omega)

theorem frame_in {rs : List Region} {m m' : Mem} {r : Region} (h : Frame [r] m m') (hr : r ∈ rs) :
    Frame rs m m' :=
  h.mono fun r' h' => by simp only [List.mem_singleton] at h'; subst h'; exact hr

theorem shr3 : ∀ k ≤ 64, BitVec.ofNat 64 (8 * k) >>> 3 = BitVec.ofNat 64 k := by decide

theorem batch_ok (d : Direction) {s : State} (h : BatchPre s) : WP isa (batch d) s (BatchPost d s) := by
  have hpos := h.pos
  have fit := h.data.fit
  generalize hk : kOf s = k
  have hk1 : 1 ≤ k := by rw [← hk, kOf]; omega
  have hk64 : k ≤ 64 := hk ▸ kOf_le s
  have hkn : k ≤ (s.gpr .a2).toNat := by rw [← hk, kOf]; omega
  let D := s.gpr .a1
  let K := scheduleAt s.mem (schedA s)
  let L : List Region := [stR s, ⟨D, 8 * k⟩]
  have inS : stR s ∈ L := List.mem_cons_self
  have inD : (⟨D, 8 * k⟩ : Region) ∈ L := List.mem_cons_of_mem _ List.mem_cons_self
  have hdisj : (⟨D, 8 * k⟩ : Region).Disjoint (stR s) :=
    (h.data.sep.sub_left (Region.sub_prefix (by omega))).sub_right (stR_sub s)
  unfold batch
  -- the batch's bytes
  apply WP.seq
  refine WP.mono (WP.rdwr (batchBytes_ok s)) fun s₁ ⟨⟨b₁, g₁, m₁, _⟩, rd₁, wr₁, _⟩ => ?_
  rw [hk] at b₁
  have s0₁ : s₁.gpr .s0 = s.gpr .s0 := g₁ _ (by decide) (by decide)
  have a1₁ : s₁.gpr .a1 = D := g₁ _ (by decide) (by decide)
  have a2₁ : s₁.gpr .a2 = s.gpr .a2 := g₁ _ (by decide) (by decide)
  have h₁ : Room s₁ := h.room.congr s0₁ wr₁
  -- the copy in
  apply WP.seq
  refine WP.mono (copyBytes_ok (src := .a1) (dst := .s0) (by decide) s₁ (N := 8 * k) (by omega) (by omega) b₁
    (fun i hi => by
      rw [a1₁, rd₁, wr₁]
      obtain ⟨r, hr, hc⟩ := h.data.byte (i := i) (by omega)
      exact ⟨r, List.mem_append_right _ hr, hc⟩)
    (fun i hi => by
      rw [s0₁, wr₁]
      exact ⟨_, h.room.frame, Offset.contains_base _ (by unfold frameBytes; omega) (by omega)⟩)
    (by
      rw [s0₁, a1₁]
      exact sep_of_disjoint ((hdisj.sub_right (Region.sub_prefix (by omega))).symm))) fun s₂ ⟨c₂, f₂, g₂, wr₂⟩ => ?_
  have s0₂ : s₂.gpr .s0 = s.gpr .s0 := (g₂ _ (by decide) (by decide) (by decide) (by decide)).trans s0₁
  have a1₂ : s₂.gpr .a1 = D := (g₂ _ (by decide) (by decide) (by decide) (by decide)).trans a1₁
  have a2₂ : s₂.gpr .a2 = s.gpr .a2 := (g₂ _ (by decide) (by decide) (by decide) (by decide)).trans a2₁
  have h₂ : Room s₂ := h.room.congr s0₂ (wr₂.trans wr₁)
  have fs₂ : Frame [stR s] s.mem s₂.mem := by
    rw [← m₁]
    refine f₂.sub fun r hr => ⟨stR s, List.mem_singleton_self _, ?_⟩
    simp only [List.mem_singleton] at hr; subst hr
    rw [s0₁]; exact Region.sub_prefix (by omega)
  have w₂ : ∀ b < k, words s₂ b = s.mem.readW (wAt D b) 64 := by
    intro b hb
    simp only [words, sl, Straight.wordAddr, s0₂]
    refine readW_of_bytes fun i hi => ?_
    have e := c₂ (8 * b + i) (by omega)
    rw [s0₁, a1₁, m₁] at e
    rw [Offset.add_add, e, ← Offset.add_add]
  -- the transposition
  apply WP.seq
  obtain ⟨s₃, run₃, w₃, -, wr₃, -, s0₃, a1₃, a2₃, f₃⟩ :=
    transpose_ok h₂ (masksAt_frame s0₂ h.room fs₂ h.masks)
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have s0₃' : s₃.gpr .s0 = s.gpr .s0 := s0₃.trans s0₂
  have wr₃' : s₃.wr = s.wr := wr₃.trans (wr₂.trans wr₁)
  have h₃ : Room s₃ := h.room.congr s0₃' wr₃'
  have fs₃ : Frame [stR s] s.mem s₃.mem := fs₂.trans (by rw [← stR_congr s0₂]; exact f₃)
  -- the passes
  apply WP.seq
  refine WP.mono (WP.rdwr (passes_ok d h₃)) fun s₄ ⟨⟨w₄, k₄, _, wr₄, _, f₄⟩, _⟩ => ?_
  have s0₄ : s₄.gpr .s0 = s.gpr .s0 := (k₄ _ (by decide)).trans s0₃'
  have wr₄' : s₄.wr = s.wr := wr₄.trans wr₃'
  have h₄ : Room s₄ := h.room.congr s0₄ wr₄'
  have fs₄ : Frame [stR s] s.mem s₄.mem := fs₃.trans (by rw [← stR_congr s0₃']; exact f₄)
  have K₃ : scheduleAt s₃.mem (schedA s₃) = K := by
    rw [show schedA s₃ = schedA s by simp only [schedA, s0₃']]; exact sched_frame h.room fs₃
  -- the transposition back
  apply WP.seq
  obtain ⟨s₅, run₅, w₅, -, wr₅, -, s0₅, a1₅, a2₅, f₅⟩ :=
    transpose_ok h₄ (masksAt_frame s0₄ h.room fs₄ h.masks)
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have s0₅' : s₅.gpr .s0 = s.gpr .s0 := s0₅.trans s0₄
  have wr₅' : s₅.wr = s.wr := wr₅.trans wr₄'
  have fs₅ : Frame [stR s] s.mem s₅.mem := fs₄.trans (by rw [← stR_congr s0₄]; exact f₅)
  have a1₅' : s₅.gpr .a1 = D := a1₅.trans ((k₄ _ (by decide)).trans (a1₃.trans a1₂))
  have a2₅' : s₅.gpr .a2 = s.gpr .a2 := a2₅.trans ((k₄ _ (by decide)).trans (a2₃.trans a2₂))
  -- the batch's bytes again
  apply WP.seq
  refine WP.mono (WP.rdwr (batchBytes_ok s₅))
    fun s₆ ⟨⟨b₆, g₆, m₆, _⟩, rd₆, wr₆, _⟩ => ?_
  rw [show kOf s₅ = k by rw [← hk, kOf, kOf, a2₅']] at b₆
  have s0₆ : s₆.gpr .s0 = s.gpr .s0 := (g₆ _ (by decide) (by decide)).trans s0₅'
  have a1₆ : s₆.gpr .a1 = D := (g₆ _ (by decide) (by decide)).trans a1₅'
  have a2₆ : s₆.gpr .a2 = s.gpr .a2 := (g₆ _ (by decide) (by decide)).trans a2₅'
  have wr₆' : s₆.wr = s.wr := wr₆.trans wr₅'
  -- the copy out
  apply WP.seq
  refine WP.mono (copyBytes_ok (src := .s0) (dst := .a1) (by decide) s₆ (N := 8 * k) (by omega) (by omega) b₆
    (fun i hi => by
      rw [s0₆]
      exact ⟨_, List.mem_append_right _ (wr₆' ▸ h.room.frame),
        Offset.contains_base _ (by unfold frameBytes; omega) (by omega)⟩)
    (fun i hi => by rw [a1₆, wr₆']; exact h.data.byte (by omega))
    (by
      rw [s0₆, a1₆]
      exact sep_of_disjoint (hdisj.sub_right (Region.sub_prefix (by omega)))))
    fun s₇ ⟨c₇, f₇, g₇, wr₇⟩ => ?_
  have s0₇ : s₇.gpr .s0 = s.gpr .s0 := (g₇ _ (by decide) (by decide) (by decide) (by decide)).trans s0₆
  have a1₇ : s₇.gpr .a1 = D := (g₇ _ (by decide) (by decide) (by decide) (by decide)).trans a1₆
  have a2₇ : s₇.gpr .a2 = s.gpr .a2 := (g₇ _ (by decide) (by decide) (by decide) (by decide)).trans a2₆
  have s5₇ : s₇.gpr .s5 = BitVec.ofNat 64 (8 * k) := (g₇ _ (by decide) (by decide) (by decide) (by decide)).trans b₆
  -- the end
  have e₁ := exec_add (s := s₇) (d := .a1) (n := .a1) (m := .s5)
  let t₁ := s₇.write .a1 (s₇.gpr .a1 + s₇.gpr .s5)
  have e₂ := exec_shift_d (s := t₁) (op := .srl) (d := .t0) (n := .s5) (sh := 3) (by decide)
  let t₂ := t₁.write .t0 (t₁.gpr .s5 >>> 3)
  have e₃ := exec_sub (s := t₂) (d := .a2) (n := .a2) (m := .t0)
  refine WP.of_runBlock ⟨t₂.write .a2 (t₂.gpr .a2 - t₂.gpr .t0), by
    rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃, runStep_some,
      runBlock_nil], ?_⟩
  have frame : Frame L s.mem s₇.mem := by
    have a : Frame L s.mem s₅.mem := frame_in fs₅ inS
    have b : Frame L s₅.mem s₇.mem := by
      rw [← m₆]
      refine f₇.mono fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr; rw [a1₆]; exact inD
    exact a.trans b
  subst hk
  refine ⟨?_, ?_, ?_, wr₇.trans wr₆', fun b hb => ?_, frame⟩
  · simp only [t₂, t₁, RegUpd.gpr_write, reduceCtorEq, ite_false, s0₇]
  · simp only [t₂, t₁, RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, a1₇, s5₇, wAt, D]
  · simp only [t₂, t₁, RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, a2₇, s5₇, shr3 _ hk64]
  · -- every block of the batch
    have hb64 : b < 64 := by omega
    show blockAt s₇.mem (wAt D b) = blockOut K d (blockAt s.mem (wAt D b))
    have lane₃ : ipLane (words s₃) b = permute ip (decodeBlock (blockAt s.mem (wAt D b))) := by
      rw [VG.Proof.TripleDes.Bitslice.ipLane_congr w₃ b]
      refine VG.Proof.TripleDes.Bitslice.ipLane_transpose _ _ hb64 fun j hj => ?_
      rw [w₂ b hb]
      exact readW_bit s.mem (wAt D b) hj
    have word₇ : s₇.mem.readW (wAt D b) 64 = transposeW (words s₄) b := by
      rw [← w₅ b hb64]
      simp only [words, sl, Straight.wordAddr, s0₅']
      refine readW_of_bytes fun i hi => ?_
      have e := c₇ (8 * b + i) (by omega)
      rw [s0₆, a1₆, m₆] at e
      rw [wAt, Offset.add_add, e, ← Offset.add_add]
    rw [VG.Proof.TripleDes.Bitslice.blockOut_cores]
    apply blockAt_of_readW
    intro j hj
    rw [word₇, VG.Proof.TripleDes.Bitslice.transpose_out _ _ j hj,
      VG.Proof.TripleDes.Bitslice.ipLane_congr w₄ b, VG.Proof.TripleDes.Bitslice.tdeaW_lane _ _ _ hb64,
      lane₃, K₃]



open VG VG.RISCV64 VG.Impl.TripleDes.RISCV64.Bitslice VG.Spec.TripleDes VG.Impl.Words.RISCV64
open VG.Proof.TripleDes.Bitslice (blockOut wAt wAt_wAt blockAt_frame)
open VG.RISCV64.Straight (wordAddr)

/-! ## The masks -/

def maskCode (k : Nat) : List Instr :=
  li64 .t0 .t1 (swapMask (maskShifts.getD k 1)) ++ ([.store .d .t0 base (maskOff + 8 * k)] : List Instr)

theorem storeMasks_eq : storeMasks = (List.range 6).flatMap maskCode := rfl

/-- The mask words. -/
def maskR (s : State) : Region := ⟨wordAddr (s.gpr .s0) 112, 48⟩

theorem maskCode_ok {s : State} (h : Room s) {k : Nat} (hk : k < 6) :
    WP isa (.block (maskCode k)) s fun s' =>
      s'.mem = s.mem.writeW (wordAddr (s.gpr .s0) (112 + k)) (swapMask (maskShifts.getD k 1)) ∧
      (∀ r, r ≠ .t0 → r ≠ .t1 → s'.gpr r = s.gpr r) ∧ s'.wr = s.wr := by
  unfold maskCode
  rw [WP.block_append_iff]
  refine WP.mono (ByteLoad.li64_ok (s := s) (by decide) _) fun s₁ e => ?_
  subst e
  let s₁ := (s.write .t1 (sext32 ((swapMask (maskShifts.getD k 1)).setWidth 32))).write .t0
    (swapMask (maskShifts.getD k 1))
  have b₁ : s₁.gpr .s0 = s.gpr .s0 := by simp [s₁, RegUpd.gpr_write]
  have t0₁ : s₁.gpr .t0 = swapMask (maskShifts.getD k 1) := by simp [s₁, RegUpd.gpr_write]
  have ea : s₁.gpr base + BitVec.ofNat 64 (maskOff + 8 * k) = wordAddr (s.gpr .s0) (112 + k) := by
    rw [show base = .s0 from rfl, b₁, wordAddr, show maskOff + 8 * k = 8 * (112 + k) by unfold maskOff; omega]
  have e := exec_store_d (s := s₁) (t := .t0) (n := base) (off := maskOff + 8 * k)
    (by unfold maskOff; omega) (by rw [ea]; exact Straight.wordAddr_al h.al _ (by omega))
    (by rw [ea]; exact slot_in h (by omega))
  let A := wordAddr (s.gpr .s0) (112 + k)
  let v := swapMask (maskShifts.getD k 1)
  refine WP.of_runBlock ⟨{ s₁ with mem := s₁.mem.writeW A v }, by rw [runBlock_cons, e, runStep_some, runBlock_nil, ea, t0₁], rfl,
    fun r a b => ?_, rfl⟩
  show s₁.gpr r = s.gpr r
  simp only [s₁, RegUpd.gpr_write, a, b, ite_false]

theorem masks_ok {s : State} (h : Room s) : ∀ n ≤ 6,
    WP isa (.block ((List.range n).flatMap maskCode)) s fun s' =>
      (∀ k < n, s'.mem.readW (wordAddr (s.gpr .s0) (112 + k)) 64 = swapMask (maskShifts.getD k 1)) ∧
      (∀ r, r ≠ .t0 → r ≠ .t1 → s'.gpr r = s.gpr r) ∧ s'.wr = s.wr ∧ Frame [maskR s] s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun k hk => absurd hk (by omega), fun _ _ _ => rfl, rfl, Frame.refl _ _⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      WP.block_append_iff]
    refine WP.mono (masks_ok h n (by omega)) fun s₁ ⟨m₁, g₁, w₁, f₁⟩ => ?_
    have b₁ : s₁.gpr .s0 = s.gpr .s0 := g₁ _ (by decide) (by decide)
    have h₁ : Room s₁ := h.congr b₁ w₁
    refine WP.mono (maskCode_ok h₁ (k := n) (by omega)) fun s₂ ⟨m₂, g₂, w₂⟩ =>
      ⟨fun k hk => ?_, fun r a b => (g₂ r a b).trans (g₁ r a b), w₂.trans w₁, ?_⟩
    · rw [m₂, b₁]
      by_cases e : k = n
      · subst e; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (by
          simp only [wordAddr]
          exact Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
        exact m₁ k (by omega)
    · rw [m₂, b₁]
      exact f₁.writeW (List.mem_singleton_self _) _ (by
        simp only [maskR, wordAddr]
        rw [show 8 * (112 + n) = 8 * 112 + 8 * n by omega, ← Offset.add_add]
        exact Offset.contains_base _ (by omega) (by omega))

theorem masksAt_of {s s' : State} (hb : s'.gpr .s0 = s.gpr .s0)
    (h : ∀ k < 6, s'.mem.readW (wordAddr (s.gpr .s0) (112 + k)) 64 = swapMask (maskShifts.getD k 1)) :
    MasksAt s' := fun k hk => by rw [hb]; exact h k hk

/-! ## The setup -/

/-- The saved registers' slots, from the frame's base. -/
def savedL : List (Reg × Nat) := saved.map fun (r, o) => (r, savedOff + o)

theorem savedL_fits : Spill.Fits savedL := by decide

theorem savedL_le : ∀ p ∈ savedL, 944 ≤ p.2 ∧ p.2 + 8 ≤ 1048 := by decide

/-- A schedule from its bytes. -/
theorem scheduleAt_of_bytes {m m' : Mem} {p p' : Addr}
    (h : ∀ i < 384, m' (p' + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    scheduleAt m' p' = scheduleAt m p := by
  apply Vector.ext
  intro i hi
  rw [VG.Proof.TripleDes.scheduleAt_readW m' p' i hi, VG.Proof.TripleDes.scheduleAt_readW m p i hi]
  refine readW_of_bytes fun j hj => ?_
  rw [Offset.add_add, Offset.add_add, h _ (by omega)]

/-- What the setup needs: the frame at the stack pointer, writable, aligned
and apart from the schedules, which are readable. -/
structure SetupPre (u : State) : Prop where
  wr : (⟨u.sp, 1056⟩ : Region) ∈ u.wr
  al : u.sp.toNat % 8 = 0
  fit : u.sp.toNat + 1056 ≤ 2 ^ 64
  key : ∀ i < 384, InRegions (u.rd ++ u.wr) (u.gpr .a0 + BitVec.ofNat 64 i) 1
  sep : (⟨u.sp, 1056⟩ : Region).Disjoint ⟨u.gpr .a0, 384⟩

structure SetupPost (u v : State) : Prop where
  room : Room v
  s0 : v.gpr .s0 = u.sp
  masks : MasksAt v
  sched : scheduleAt v.mem (schedA v) = scheduleAt u.mem (u.gpr .a0)
  saved : Spill.Saved u.sp u.gpr savedL v.mem
  a1 : v.gpr .a1 = u.gpr .a1
  a2 : v.gpr .a2 = u.gpr .a2
  wr : v.wr = u.wr
  frame : Frame [⟨u.sp, 1056⟩] u.mem v.mem

theorem setup_ok {u : State} (h : SetupPre u) : WP isa setup u (SetupPost u) := by
  have fit := h.fit
  unfold setup
  apply WP.seq
  have hb : ([.addSp .t0 0] ++ saved.map (fun (r, o) => Instr.store .d r .t0 (savedOff + o)) ++
      [.addi base .t0 0, .addi .t3 base schedOff, .addi .t2 .a0 0, .li .t4 384] : List Instr) =
      .addSp .t0 0 :: (Spill.saveCode .t0 savedL ++
        [.addi base .t0 0, .addi .t3 base schedOff, .addi .t2 .a0 0, .li .t4 384]) := rfl
  rw [hb]
  let u₀ := u.write .t0 (u.sp + BitVec.ofNat 64 0)
  have t0₀ : u₀.gpr .t0 = u.sp := by simp [u₀, RegUpd.gpr_write]
  refine WP.block_cons_iff.mpr ⟨u₀, exec_addSp (s := u) (d := .t0) (imm := 0) (by decide), ?_⟩
  refine Spill.save_ok (by rw [t0₀]; exact h.al) savedL_fits.1 (fun p hp => ?_) ?_
  · rw [t0₀]
    exact ⟨_, h.wr, Offset.contains_base _ (by have := (savedL_le p hp).2; omega) (by have := (savedL_le p hp).2; omega)⟩
  let u₁ : State := { u₀ with mem := Spill.saveMem u₀.mem (u₀.gpr .t0) u₀.gpr savedL }
  have e₂ := exec_addi (s := u₁) (d := .s0) (n := .t0) (imm := 0) (by decide)
  let u₂ := u₁.write .s0 (u₁.gpr .t0 + BitVec.ofInt 64 0)
  have e₃ := exec_addi (s := u₂) (d := .t3) (n := .s0) (imm := (schedOff : Int)) (by decide)
  let u₃ := u₂.write .t3 (u₂.gpr .s0 + BitVec.ofInt 64 (schedOff : Int))
  have e₄ := exec_addi (s := u₃) (d := .t2) (n := .a0) (imm := 0) (by decide)
  let u₄ := u₃.write .t2 (u₃.gpr .a0 + BitVec.ofInt 64 0)
  have e₅ := exec_li (s := u₄) (d := .t4) (imm := 384) (by decide)
  let u₅ := u₄.write .t4 (BitVec.ofInt 64 384)
  have s0₅ : u₅.gpr .s0 = u.sp := by
    simp [u₅, u₄, u₃, u₂, u₁, RegUpd.gpr_write, t0₀]
  have t3₅ : u₅.gpr .t3 = u.sp + BitVec.ofNat 64 schedOff := by
    simp [u₅, u₄, u₃, u₂, u₁, RegUpd.gpr_write, t0₀]
  have t2₅ : u₅.gpr .t2 = u.gpr .a0 := by
    simp [u₅, u₄, u₃, u₂, u₁, u₀, RegUpd.gpr_write]
  have t4₅ : u₅.gpr .t4 = BitVec.ofNat 64 384 := by
    simp [u₅, RegUpd.gpr_write]
  have g₅ : ∀ r, r ≠ .t0 → r ≠ .s0 → r ≠ .t3 → r ≠ .t2 → r ≠ .t4 → u₅.gpr r = u.gpr r := by
    intro r a b c d e
    simp [u₅, u₄, u₃, u₂, u₁, u₀, RegUpd.gpr_write, a, b, c, d, e]
  have m₅ : u₅.mem = Spill.saveMem u.mem u.sp u₀.gpr savedL := by
    show Spill.saveMem u₀.mem (u₀.gpr .t0) u₀.gpr savedL = _
    rw [t0₀]; rfl
  have f₅ : Frame [⟨u.sp, 1056⟩] u.mem u₅.mem := by
    rw [m₅]
    have := Spill.saveMem_frame (lo := 0) (n := 1056) (fun p hp => ⟨Nat.zero_le _, by have := (savedL_le p hp).2; omega⟩)
      (by decide) u.mem u.sp u₀.gpr
    simpa only [BitVec.add_zero, BitVec.ofNat_eq_ofNat] using this
  have hkey₅ : (⟨u.sp + BitVec.ofNat 64 schedOff, 384⟩ : Region).Disjoint ⟨u.gpr .a0, 384⟩ :=
    h.sep.sub_left (Offset.sub_base _ (by unfold schedOff; omega))
  refine WP.block_cons_iff.mpr ⟨u₂, e₂, WP.block_cons_iff.mpr ⟨u₃, e₃, WP.block_cons_iff.mpr ⟨u₄, e₄,
    WP.block_cons_iff.mpr ⟨u₅, e₅, WP.block_nil ?_⟩⟩⟩⟩
  -- the schedules copied
  apply WP.seq
  refine WP.mono (copyLoop_ok (tmp := .t1) (src := .t2) (dst := .t3) (cnt := .t4) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) u₅ (N := 384) (by decide) (by decide) t4₅
    (fun i hi => by rw [t2₅]; exact h.key i hi)
    (fun i hi => by
      rw [t3₅]
      exact ⟨_, h.wr, by rw [Offset.add_add]; exact Offset.contains_base _ (by unfold schedOff; omega) (by unfold schedOff; omega)⟩)
    (by rw [t2₅, t3₅]; exact sep_of_disjoint hkey₅)) fun u₆ ⟨c₆, f₆, k₆⟩ => ?_
  have s0₆ : u₆.gpr .s0 = u.sp := (k₆.1 _ (by decide)).trans s0₅
  have wr₆ : u₆.wr = u.wr := k₆.2.2
  have h₆ : Room u₆ :=
    ⟨by simp only [frameR, s0₆, wr₆, frameBytes]; exact h.wr, by rw [s0₆]; exact h.al,
      by rw [s0₆]; unfold frameBytes; omega⟩
  -- the masks
  rw [storeMasks_eq]
  refine WP.mono (masks_ok h₆ 6 (Nat.le_refl _)) fun v ⟨m₇, g₇, w₇, f₇⟩ => ?_
  have s0₇ : v.gpr .s0 = u.sp := (g₇ _ (by decide) (by decide)).trans s0₆
  have hm₇ : maskR u₆ = ⟨u.sp + BitVec.ofNat 64 896, 48⟩ := by simp only [maskR, s0₆]
  rw [hm₇] at f₇
  have f₆' : Frame [⟨u.sp + BitVec.ofNat 64 schedOff, 384⟩] u₅.mem u₆.mem := by rw [← t3₅]; exact f₆
  refine ⟨h₆.congr (s0₇.trans s0₆.symm) w₇, s0₇, masksAt_of (s := u₆) (g₇ _ (by decide) (by decide)) m₇, ?_, ?_,
    (g₇ _ (by decide) (by decide)).trans ((k₆.1 _ (by decide)).trans (g₅ _ (by decide) (by decide)
      (by decide) (by decide) (by decide))),
    (g₇ _ (by decide) (by decide)).trans ((k₆.1 _ (by decide)).trans (g₅ _ (by decide) (by decide)
      (by decide) (by decide) (by decide))), w₇.trans wr₆, ?_⟩
  · -- the schedule
    rw [show schedA v = u.sp + BitVec.ofNat 64 schedOff by simp only [schedA, s0₇]]
    rw [VG.Proof.TripleDes.scheduleAt_eq_of_frame _ f₇ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by unfold schedOff; omega)) (by unfold schedOff; omega) (by omega)]
    refine scheduleAt_of_bytes fun i hi => ?_
    have e := c₆ i hi
    rw [t3₅, t2₅] at e
    rw [e, m₅]
    refine Spill.saveMem_frame (lo := 0) (n := 1056) (fun p hp => ⟨Nat.zero_le _, by have := (savedL_le p hp).2; omega⟩)
      (by decide) u.mem u.sp u₀.gpr _ fun r hr hc => ?_
    simp only [List.mem_singleton] at hr; subst hr
    rw [BitVec.add_zero] at hc
    exact h.sep _ hc (Offset.contains_base _ (by omega) (by omega))
  · -- the saved registers
    have sv₅ : Spill.Saved u.sp u.gpr savedL u₅.mem := by
      rw [m₅]
      intro p hp
      rw [Spill.saveMem_saved savedL_fits u.mem u.sp u₀.gpr p hp]
      have hne : p.1 ≠ .t0 := by revert p; decide
      simp [u₀, RegUpd.gpr_write, hne]
    have dj : ∀ (lo n : Nat), lo + n ≤ 944 → (⟨u.sp + BitVec.ofNat 64 944, 104⟩ : Region).Disjoint
        ⟨u.sp + BitVec.ofNat 64 lo, n⟩ := fun lo n hl =>
      Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
    exact (sv₅.frame_in (lo := 944) (n := 104) (fun p hp => ⟨(savedL_le p hp).1, (savedL_le p hp).2⟩) f₆' fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact dj _ _ (by unfold schedOff; omega)).frame_in
      (lo := 944) (n := 104) (fun p hp => ⟨(savedL_le p hp).1, (savedL_le p hp).2⟩) f₇
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dj _ _ (by omega)
  · -- the frame
    have sub : ∀ (lo n : Nat), lo + n ≤ 1056 → ∀ r ∈ [(⟨u.sp + BitVec.ofNat 64 lo, n⟩ : Region)],
        ∃ r' ∈ [(⟨u.sp, 1056⟩ : Region)], Region.Sub r r' := fun lo n hl r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ hl⟩
    exact (f₅.trans (f₆'.sub (sub _ _ (by unfold schedOff; omega)))).trans (f₇.sub (sub _ _ (by omega)))

/-! ## The batches -/

/-- What stays true of the data and the frame through the batches. -/
structure LoopEnv (B D : Addr) (n : Nat) (W : List Region) : Prop where
  data : ∀ i < 8 * n, InRegions W (D + BitVec.ofNat 64 i) 1
  fit : D.toNat + 8 * n ≤ 2 ^ 64
  sep : (⟨D, 8 * n⟩ : Region).Disjoint ⟨B, 1056⟩

/-- After the first `p` blocks. -/
structure LoopInv (d : Direction) (s : State) (B D : Addr) (n : Nat) (K : Schedule) (g : Reg → BitVec 64)
    (W : List Region) (p : Nat) (v : State) : Prop where
  le : p ≤ n
  room : Room v
  s0 : v.gpr .s0 = B
  masks : MasksAt v
  sched : scheduleAt v.mem (schedA v) = K
  a1 : v.gpr .a1 = wAt D p
  a2 : v.gpr .a2 = BitVec.ofNat 64 (n - p)
  wr : v.wr = W
  done : ∀ b < p, blockAt v.mem (wAt D b) = blockOut K d (blockAt s.mem (wAt D b))
  rest : ∀ b, p ≤ b → b < n → blockAt v.mem (wAt D b) = blockAt s.mem (wAt D b)
  saved : Spill.Saved B g savedL v.mem

theorem batch_step {d : Direction} {s : State} {B D : Addr} {n : Nat} {K : Schedule} {g : Reg → BitVec 64}
    {W : List Region} (E : LoopEnv B D n W) {p : Nat} (hp : p < n) {v : State}
    (I : LoopInv d s B D n K g W p v) :
    WP isa (batch d) v fun v' => LoopInv d s B D n K g W (p + min (n - p) 64) v' := by
  have fit := E.fit
  have hrem : (v.gpr .a2).toNat = n - p := by rw [I.a2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hkv : kOf v = min (n - p) 64 := by rw [kOf, hrem]
  have hDp : (wAt D p).toNat = D.toNat + 8 * p := by
    rw [wAt, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * p) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have pre : BatchPre v := by
    refine ⟨I.room, I.masks, by omega, ⟨fun i hi => ?_, by rw [hrem, I.a1, hDp]; omega, ?_⟩⟩
    · rw [I.wr, I.a1, wAt, Offset.add_add]; exact E.data _ (by rw [hrem] at hi; omega)
    · simp only [frameR, I.a1, I.s0, hrem, frameBytes]
      exact E.sep.sub_left (Offset.sub_base _ (by omega))
  refine WP.mono (batch_ok d pre) fun v' q => ?_
  obtain ⟨qs0, qa1, qa2, qwr, qout, qframe⟩ := q
  rw [hkv] at qa1 qa2 qout qframe
  generalize hk : min (n - p) 64 = k at qa1 qa2 qout qframe
  have hk1 : 1 ≤ k := by omega
  have hkn : k ≤ n - p := by omega
  have hst : stR v = ⟨B, 512⟩ := by simp only [stR, I.s0]
  have a1v : v.gpr .a1 = wAt D p := I.a1
  rw [hst, a1v] at qframe
  rw [a1v] at qa1 qout
  -- regions written by the batch, apart from the frame's other words and the other blocks
  have dataSub : Region.Sub ⟨wAt D p, 8 * k⟩ ⟨D, 8 * n⟩ := Offset.sub_base _ (by omega)
  have offB : ∀ (lo m : Nat), 512 ≤ lo → lo + m ≤ 1056 →
      ∀ r ∈ [(⟨B, 512⟩ : Region), ⟨wAt D p, 8 * k⟩], Region.Disjoint ⟨B + BitVec.ofNat 64 lo, m⟩ r :=
    fun lo m h1 h2 r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint_base _ h1 (by have := I.room.fit; rw [I.s0] at this; unfold frameBytes at this; omega)
      · exact (E.sep.sub_left dataSub).symm.sub_left (Offset.sub_base _ h2)
  have blk : ∀ b, (b < p ∨ p + k ≤ b) → b < n →
      ∀ r ∈ [(⟨B, 512⟩ : Region), ⟨wAt D p, 8 * k⟩], Region.Disjoint ⟨wAt D b, 8⟩ r := fun b hb hbn r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (E.sep.sub_left (Offset.sub_base _ (by omega))).sub_right (Region.sub_prefix (by omega))
    · simp only [wAt]
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
  have s0' : v'.gpr .s0 = B := qs0.trans I.s0
  refine ⟨by omega, I.room.congr qs0 qwr, s0', ?_, ?_, by rw [qa1, wAt_wAt], ?_, qwr.trans I.wr,
    fun b hb => ?_, fun b hb hbn => ?_, ?_⟩
  · -- the masks
    intro j hj
    rw [s0', ← I.s0, ← I.masks j hj, I.s0]
    exact qframe.readW (Region.contains_self _ 8) (by
      intro r hr
      have := offB (896 + 8 * j) 8 (by omega) (by omega) r hr
      simp only [wordAddr]; rw [show 8 * (112 + j) = 896 + 8 * j by omega]; exact this) (by decide)
  · -- the schedules
    rw [show schedA v' = schedA v by simp only [schedA, s0', I.s0], ← I.sched]
    refine VG.Proof.TripleDes.scheduleAt_eq_of_frame _ qframe fun r hr => ?_
    simp only [schedA, I.s0]
    exact offB 512 384 (by omega) (by omega) r hr
  · rw [qa2, I.a2, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) hkn]; congr 1; omega
  · -- the blocks done
    by_cases e : b < p
    · rw [blockAt_frame qframe (blk b (.inl e) (by omega)), I.done b e]
    · have hb' : b - p < k := by omega
      have := qout (b - p) hb'
      rw [wAt_wAt, show p + (b - p) = b by omega, I.sched, I.rest b (by omega) (by omega)] at this
      exact this
  · rw [blockAt_frame qframe (blk b (.inr hb) hbn), I.rest b (by omega) hbn]
  · exact I.saved.frame_in (lo := 944) (n := 104) (fun p hp => ⟨(savedL_le p hp).1, (savedL_le p hp).2⟩)
      qframe fun r hr => offB 944 104 (by omega) (by omega) r hr

theorem loop_ok {d : Direction} {s : State} {B D : Addr} {n : Nat} {K : Schedule} {g : Reg → BitVec 64}
    {W : List Region} (E : LoopEnv B D n W) (hn : 0 < n) {v : State} (I : LoopInv d s B D n K g W 0 v) :
    WP isa (.loop (batch d) (.nonzero .a2)) v (LoopInv d s B D n K g W n) := by
  have fit := E.fit
  refine WP.loop (M := isa) (fun m v => ∃ p, p < n ∧ m = n - p ∧ LoopInv d s B D n K g W p v) ?_ n v
    ⟨0, hn, rfl, I⟩
  rintro m v ⟨p, hp, rfl, J⟩
  refine WP.mono (batch_step E hp J) fun v' J' => ?_
  rw [Steps.eval_nonzero_ofNat _ _ (by omega) J'.a2]
  by_cases e : n - (p + min (n - p) 64) = 0
  · left
    refine ⟨by simp [e], ?_⟩
    rwa [show p + min (n - p) 64 = n by omega] at J'
  · right
    exact ⟨by simp [e], _, by omega, _, by omega, rfl, J'⟩

/-! ## The end -/

theorem restores_eq : (saved.map fun (r, o) => Instr.load .d r base (savedOff + o)) =
    Spill.restoreCode .s0 savedL := rfl

theorem finish_ok {d : Direction} {s : State} {B D : Addr} {n : Nat} {K : Schedule} {g : Reg → BitVec 64}
    {W : List Region} (E : LoopEnv B D n W) {v : State} (I : LoopInv d s B D n K g W n v) :
    WP isa finish v fun y => (∀ r ∈ savedL.map Prod.fst, y.gpr r = g r) ∧
      ∀ b < n, blockAt y.mem (wAt D b) = blockOut K d (blockAt s.mem (wAt D b)) := by
  have fit := E.fit
  have al : B.toNat % 8 = 0 := by rw [← I.s0]; exact I.room.al
  have bfit : B.toNat + 1056 ≤ 2 ^ 64 := by rw [← I.s0]; exact I.room.fit
  have inF : ∀ o m, o + m ≤ 1056 → InRegions v.wr (B + BitVec.ofNat 64 o) m := fun o m hm =>
    ⟨_, by have := I.room.frame; rwa [frameR, I.s0] at this, Offset.contains_base _ (by unfold frameBytes; omega)
      (by omega)⟩
  unfold finish
  have e₁ := exec_li (s := v) (d := .t1) (imm := 0) (by decide)
  let w₁ := v.write .t1 (BitVec.ofInt 64 0)
  have e₂ := exec_addi (s := w₁) (d := .t0) (n := base) (imm := 0) (by decide)
  let w₂ := w₁.write .t0 (w₁.gpr base + BitVec.ofInt 64 0)
  have e₃ := exec_li (s := w₂) (d := .t4) (imm := ((savedOff / 8 : Nat) : Int)) (by decide)
  let w₃ := w₂.write .t4 (BitVec.ofInt 64 ((savedOff / 8 : Nat) : Int))
  apply WP.seq
  refine WP.of_runBlock ⟨w₃, by
    rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃, runStep_some,
      runBlock_nil], ?_⟩
  have t0₃ : w₃.gpr .t0 = B := by simp [w₃, w₂, w₁, RegUpd.gpr_write, base, I.s0]
  have s0₃ : w₃.gpr .s0 = B := by simp [w₃, w₂, w₁, RegUpd.gpr_write, I.s0]
  have t4₃ : w₃.gpr .t4 = BitVec.ofNat 64 118 := by simp [w₃, RegUpd.gpr_write]; rfl
  apply WP.seq
  refine WP.mono (fillLoop_ok (v := .t1) (ptr := .t0) (cnt := .t4) (by decide) (by decide) (by decide) w₃
    (N := 118) (by decide) (by decide) t4₃ (by rw [t0₃]; exact al)
    (fun i hi => by rw [t0₃]; exact inF _ _ (by omega))) fun x ⟨_, fx, kx⟩ => ?_
  have s0x : x.gpr .s0 = B := (kx.1 _ (by decide)).trans s0₃
  rw [t0₃] at fx
  rw [restores_eq]
  have sv : Spill.Saved B g savedL x.mem :=
    I.saved.frame_in (lo := 944) (n := 104) (fun p hp => ⟨(savedL_le p hp).1, (savedL_le p hp).2⟩) fx
      fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint_base _ (by omega) (by omega)
  refine WP.mono (Spill.restore_wp (b := .s0) al s0x savedL_fits.1 (by decide) (fun p hp => ?_) sv)
    fun y r => ⟨fun q hq => r.gpr_of (.inl hq), fun b hb => ?_⟩
  · rw [kx.2.2]
    obtain ⟨R, hR, hc⟩ := inF p.2 8 (by have := (savedL_le p hp).2; omega)
    exact ⟨R, List.mem_append_right _ hR, hc⟩
  · rw [r.mem, blockAt_frame fx fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (E.sep.sub_left (Offset.sub_base _ (by omega))).sub_right (Region.sub_prefix (by omega))]
    exact I.done b hb

/-! ## The function -/

theorem preserved_saved : ∀ r ∈ preserved, r ∈ savedL.map Prod.fst := by decide

/-- What ECB may assume: the schedule readable, the `n` blocks writable,
apart from each other and from the 1056 bytes below the stack pointer, the
blocks not wrapping around. -/
structure EcbPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a0, 384⟩]
  wr : s.wr = [⟨s.gpr .a1, 8 * (s.gpr .a2).toNat⟩]
  keyData : (⟨s.gpr .a0, 384⟩ : Region).Disjoint ⟨s.gpr .a1, 8 * (s.gpr .a2).toNat⟩
  fit : (s.gpr .a1).toNat + 8 * (s.gpr .a2).toNat ≤ 2 ^ 64
  al : s.sp.toNat % 16 = 0
  sp : 1056 ≤ s.sp.toNat
  stackKey : (⟨s.sp - 1056, 1056⟩ : Region).Disjoint ⟨s.gpr .a0, 384⟩
  stackData : (⟨s.sp - 1056, 1056⟩ : Region).Disjoint ⟨s.gpr .a1, 8 * (s.gpr .a2).toNat⟩

theorem ecb_wp (d : Direction) {s : State} (h : EcbPre s) :
    WP isa (Impl.TripleDes.RISCV64.Bitslice.ecb d) s fun s' => abiPreserved s s' ∧ ∀ b < (s.gpr .a2).toNat,
      blockAt s'.mem (wAt (s.gpr .a1) b) =
        blockOut (scheduleAt s.mem (s.gpr .a0)) d (blockAt s.mem (wAt (s.gpr .a1) b)) := by
  have fit := h.fit
  have hsp := h.sp
  have hal := h.al
  let D := s.gpr .a1
  let n := (s.gpr .a2).toNat
  let K := scheduleAt s.mem (s.gpr .a0)
  unfold Impl.TripleDes.RISCV64.Bitslice.ecb
  refine WP.ite (s.gpr .a2 == 0) (by rw [Steps.eval_zero]) (fun hz => ?_) (fun hz => ?_)
  · have hn : (s.gpr .a2).toNat = 0 := by simp only [beq_iff_eq] at hz; simp [hz]
    exact WP.block_nil ⟨⟨fun _ _ => rfl, rfl, rfl⟩, fun b hb => absurd hb (by omega)⟩
  have hn : 0 < n := by
    have : s.gpr .a2 ≠ 0 := by simpa using hz
    have : (s.gpr .a2).toNat ≠ 0 := fun e => this (BitVec.eq_of_toNat_eq e)
    omega
  refine WP.alloc (n := frameBytes) ⟨by decide, by decide, by decide⟩ h.sp ?_
  let u := allocd frameBytes s
  have usp : u.sp = s.sp - 1056 := rfl
  have uspN : u.sp.toNat = s.sp.toNat - 1056 := by
    rw [usp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def]; show 1056 ≤ s.sp.toNat; omega)]; rfl
  have stackU : (⟨u.sp, 1056⟩ : Region) ∈ u.wr := List.mem_cons_self
  have pre : SetupPre u :=
    ⟨stackU, by rw [uspN]; omega, by rw [uspN]; omega,
      fun i hi => ⟨_, List.mem_append_left _ (by show _ ∈ s.rd; rw [h.rd]; exact List.mem_singleton_self _),
        Offset.contains_base _ (by omega) (by omega)⟩, h.stackKey⟩
  have body : WP isa (.seq setup (.seq (.loop (batch d) (.nonzero .a2)) finish)) u fun y =>
      (∀ r ∈ savedL.map Prod.fst, y.gpr r = u.gpr r) ∧
      ∀ b < n, blockAt y.mem (wAt D b) = blockOut K d (blockAt s.mem (wAt D b)) := by
    apply WP.seq
    refine WP.mono (setup_ok pre) fun v q => ?_
    have E : LoopEnv u.sp D n u.wr :=
      ⟨fun i hi => ⟨_, List.mem_cons_of_mem _ (by rw [h.wr]; exact List.mem_singleton_self _),
          Offset.contains_base _ (by omega) (by omega)⟩, fit, h.stackData.symm⟩
    have I0 : LoopInv d s u.sp D n K u.gpr u.wr 0 v :=
      ⟨Nat.zero_le _, q.room, q.s0, q.masks, q.sched, by rw [q.a1]; exact (BitVec.add_zero _).symm,
        by rw [q.a2, Nat.sub_zero]; exact ((BitVec.ofNat_toNat 64 (s.gpr .a2)).trans (BitVec.setWidth_eq _)).symm, q.wr, fun b hb => absurd hb (by omega),
        fun b _ hbn => blockAt_frame q.frame fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (h.stackData.symm.sub_left (Offset.sub_base _ (by omega))),
        q.saved⟩
    apply WP.seq
    refine WP.mono (loop_ok E hn I0) fun w J => ?_
    exact finish_ok E J
  refine WP.mono (WP.rdwr body) fun y ⟨⟨gy, by_⟩, _, _, spy⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, fun b hb => ?_⟩
  · show y.gpr r = s.gpr r
    exact gy r (preserved_saved r hr)
  · show y.sp + BitVec.ofNat 64 frameBytes = s.sp
    rw [spy, usp]; exact BitVec.sub_add_cancel s.sp _
  · show y.gpr .ra = s.gpr .ra
    exact gy .ra (by decide)
  · have e : (freed frameBytes y).mem = y.mem := by simp only [freed]
    rw [e]; exact by_ b hb

end VG.Proof.TripleDes.RISCV64.Bitsliced
