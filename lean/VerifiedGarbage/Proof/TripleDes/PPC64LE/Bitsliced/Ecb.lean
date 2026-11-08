module

public import VerifiedGarbage.Spec.TripleDes
public import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.Pass
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Bitsliced.Transpose
public import VerifiedGarbage.Proof.TripleDes.Bitslice.Tdea
public import VerifiedGarbage.Proof.Gather.PPC64LE.Copy
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.MovImm
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Bitsliced Triple DES ECB on PPC64LE

Blocks as little-endian words (`readW_bit`, `blockAt_of_readW`: a block's
little-endian word holds bit `i` of the block, big-endian as `decodeBlock`
reads it, at bit `i ^^^ 56`).

A batch of `k = min(n, 64)` blocks (`kOf`) is copied into the state words a
doubleword at a time (`Gather.PPC64LE.copyWords`), transposed (lane `b` is
then IP of block `b`), put through the three passes, transposed back and
copied out; then the data pointer `r4` moves past it and the count `r8`
drops by `k`: each block becomes its TDEA encryption or decryption
(`batch_ok`).

`ecb_wp`: the caller's `r2` and `r14`–`r31` saved in the scratch buffer,
the arguments moved, all ones in `r11` and the masks stored (`setup_ok`),
the batches (`loop_ok`), and the registers restored (`finish_ok`). As on
RISC-V (`Proof/TripleDes/RISCV64/Bitsliced/Ecb.lean`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE.Bitsliced

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

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Impl.TripleDes.PPC64LE.Bitslice VG.Spec.TripleDes
open VG.Proof.TripleDes.Bitslice (ipLane transposeW tdeaW blockOut wAt)
open VG.WriteBytes (writeBytes)

/-- Code keeps the permissions, the stack pointer and the link register. -/
theorem WP.rdwr {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.rdwr he⟩

/-- The batch's blocks: `min(n, 64)`. -/
def kOf (s : State) : Nat := min (s.gpr .r8).toNat 64

theorem kOf_le (s : State) : kOf s ≤ 64 := Nat.min_le_right _ _

/-! ## The batch's blocks -/

theorem batchBlocks_ok (s : State) :
    WP isa batchBlocks s fun s' => s'.gpr .r12 = BitVec.ofNat 64 (kOf s) ∧
      (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.wr = s.wr ∧ s'.rd = s.rd ∧
      s'.lr = s.lr := by
  unfold batchBlocks
  have e₁ := exec_lsr_d (s := s) (d := .r12) (n := .r8) (sh := 6) (by decide)
  let s₁ := s.write .r12 (s.gpr .r8 >>> 6)
  apply WP.seq
  refine WP.of_runBlock ⟨s₁, by
    rw [runBlock_cons, show batchN = .r12 from rfl, show left = .r8 from rfl, e₁, runStep_some,
      runBlock_nil], ?_⟩
  have z : (s₁.gpr .r12 == 0) = decide ((s.gpr .r8).toNat < 64) := by
    simp only [s₁, gpr_write_self]
    by_cases h : (s.gpr .r8).toNat < 64
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
  have ev : isa.eval (.zero .d batchN) s₁ = some (s₁.gpr .r12 == 0) := by
    change VG.PPC64LE.eval (.zero .d .r12) s₁ = _
    simp only [VG.PPC64LE.eval, State.read, Size.bits, BitVec.setWidth_eq]
  refine WP.ite _ (by rw [ev, z]) (fun hlt => ?_) (fun hge => ?_)
  · have hlt : (s.gpr .r8).toNat < 64 := by simpa using hlt
    refine WP.of_runBlock ⟨s₁.write .r12 (s₁.gpr .r8 ||| s₁.gpr .r8),
      by rw [runBlock_cons, show batchN = .r12 from rfl, show left = .r8 from rfl,
        Impl.TripleDes.PPC64LE.rr, exec_logic, runStep_some, runBlock_nil], ?_, ?_, rfl, rfl, rfl, rfl⟩
    · simp only [gpr_write_self, s₁, gpr_write, reduceCtorEq, ite_false, BitVec.or_self, kOf,
        Nat.min_eq_left (Nat.le_of_lt hlt), BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · intro r h0
      simp only [s₁, gpr_write, h0, ite_false]
  · have hge : ¬ (s.gpr .r8).toNat < 64 := by simpa using hge
    have e₂ := exec_li (s := s₁) (d := .r12) (imm := 64) (by decide)
    refine WP.of_runBlock ⟨s₁.write .r12 (BitVec.ofNat 64 64),
      by rw [runBlock_cons, show batchN = .r12 from rfl, e₂, runStep_some, runBlock_nil], ?_, ?_,
        rfl, rfl, rfl, rfl⟩
    · rw [gpr_write_self, kOf, Nat.min_eq_right (by omega)]
    · intro r h0
      simp only [s₁, gpr_write, h0, ite_false]

/-! ## Copies -/

/-- The bytes a doubleword copy wrote. -/
theorem writeBytes_copied (m : Mem) (S D : Addr) {N i : Nat} (hi : i < N) (hN : N < 2 ^ 64) :
    writeBytes m D (VG.Spec.Aes.bytesAt m S N) (D + BitVec.ofNat 64 i) = m (S + BitVec.ofNat 64 i) := by
  have hi' : (D + BitVec.ofNat 64 i - D).toNat = i := by
    rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [writeBytes, hi', VG.Spec.Aes.bytesAt, List.length_map, List.length_range, hi, ite_true,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.getD_some]

theorem covers_rdwr {rs rd wr : List Region} (h : Covers rs wr) : Covers rs (rd ++ wr) := fun a n hc => by
  obtain ⟨r, hr, hc⟩ := h a n hc; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem covers_of_sub {rs : List Region} {R : Region} (hR : R ∈ rs) {S : Addr} {off n : Nat}
    (hS : S = R.base + BitVec.ofNat 64 off) (hn : off + n ≤ R.len) : Covers [⟨S, n⟩] rs :=
  Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨R, hR, off, hS, hn⟩

/-- Copy the batch's `k` doublewords from `src` to `dst`. -/
theorem copyBatch_ok {src dst : Reg} (s : State) {S D : Addr} {k : Nat} (hk : 1 ≤ k) (hk' : k ≤ 64)
    (hS : s.gpr src = S) (hD : s.gpr dst = D) (hc : s.gpr .r12 = BitVec.ofNat 64 k)
    (hD9 : dst ≠ .r3) (hrd : Covers [⟨S, 8 * k⟩] (s.rd ++ s.wr)) (hwr : Covers [⟨D, 8 * k⟩] s.wr)
    (hsep : (⟨S, 8 * k⟩ : Region).Disjoint ⟨D, 8 * k⟩) :
    WP isa (copyBatch src dst) s fun t =>
      (∀ i < 8 * k, t.mem (D + BitVec.ofNat 64 i) = s.mem (S + BitVec.ofNat 64 i)) ∧
      Frame [⟨D, 8 * k⟩] s.mem t.mem ∧ t.gpr .r9 = D + BitVec.ofNat 64 (8 * k) ∧
      (∀ r, r ∉ Proof.Gather.PPC64LE.copyRegs → t.gpr r = s.gpr r) ∧ t.gpr .r4 = s.gpr .r4 ∧
      t.wr = s.wr ∧ t.rd = s.rd ∧ t.lr = s.lr := by
  unfold copyBatch
  let s₁ := s.write .r3 (s.gpr src ||| s.gpr src)
  let s₂ := s₁.write .r9 (s₁.gpr dst ||| s₁.gpr dst)
  let s₃ := s₂.write .r5 (s₂.gpr .r12 ||| s₂.gpr .r12)
  apply WP.seq
  refine WP.of_runBlock ⟨s₃, by
    rw [Impl.TripleDes.PPC64LE.rr, Impl.TripleDes.PPC64LE.rr, Impl.TripleDes.PPC64LE.rr, show batchN = .r12 from rfl,
      runBlock_cons, exec_logic, runStep_some, runBlock_cons, exec_logic, runStep_some, runBlock_cons, exec_logic,
      runStep_some, runBlock_nil], ?_⟩
  have g : ∀ r, r ≠ .r3 → r ≠ .r9 → r ≠ .r5 → s₃.gpr r = s.gpr r := fun r a b c => by
    simp only [s₃, s₂, s₁, gpr_write, a, b, c, ite_false]
  have pre : Proof.Gather.PPC64LE.WordsPre s₃ S D k :=
    ⟨by simp [s₃, s₂, s₁, gpr_write, hS], by simp [s₃, s₂, s₁, gpr_write, hD9, hD],
      by simp [s₃, s₂, s₁, gpr_write, hc], hk, by omega, hrd, hwr, hsep⟩
  refine WP.mono (Proof.Gather.PPC64LE.copyWords_wp s₃ pre) fun t ⟨tm, _, t9, t4, tk⟩ => ?_
  have hN : 8 * k < 2 ^ 64 := by omega
  refine ⟨fun i hi => by rw [tm]; exact writeBytes_copied _ _ _ hi hN, ?_, t9, fun r hr => ?_,
    by rw [t4]; exact g _ (by decide) (by decide) (by decide), tk.wr, tk.rd, tk.lr⟩
  · rw [tm]
    have := VG.WriteBytes.writeBytes_frame s₃.mem D (VG.Spec.Aes.bytesAt s₃.mem S (8 * k))
      (R := ⟨D, 8 * k⟩) (by
        rw [show (VG.Spec.Aes.bytesAt s₃.mem S (8 * k)).length = 8 * k by simp [VG.Spec.Aes.bytesAt]]
        exact Region.contains_self _ _)
    exact this
  · rw [tk.gpr r hr]
    exact g r (fun e => hr (by simp [e])) (fun e => hr (by simp [e])) (fun e => hr (by simp [e]))

/-- A little-endian word from its bytes. -/
theorem readW_of_bytes {m m' : Mem} {a b : Addr} (h : ∀ i < 8, m' (b + BitVec.ofNat 64 i) = m (a + BitVec.ofNat 64 i)) :
    m'.readW b 64 = m.readW a 64 := by
  simp only [Mem.readW, BitVec.setWidth_eq]
  exact Mem.read_eq_of_bytes fun i hi => by rw [h i hi, Mem.extractLsb'_read m a hi]

/-! ## The batch -/

/-- The data: the `n` blocks at `D`, writable, not wrapping around, apart
from the scratch buffer and the schedule. -/
structure Data (s : State) (D : Addr) (n : Nat) : Prop where
  wr : Covers [⟨D, 8 * n⟩] s.wr
  fit : D.toNat + 8 * n ≤ 2 ^ 64
  sep : (⟨D, 8 * n⟩ : Region).Disjoint (frameR s)
  key : (⟨D, 8 * n⟩ : Region).Disjoint ⟨s.gpr .r7, 384⟩

/-- What a batch needs: the buffer, the schedule, all ones, the masks, a
block left, and the data. -/
structure BatchPre (s : State) : Prop where
  room : Room s
  sched : Sched s
  ones : Ones s
  masks : MasksAt s
  pos : 1 ≤ (s.gpr .r8).toNat
  data : Data s (s.gpr .r4) (s.gpr .r8).toNat

/-- The registers a batch keeps. -/
def batchKept : List Reg := [.r10, .r7, .r11]

structure BatchPost (d : Direction) (s s' : State) : Prop where
  kept : ∀ r ∈ batchKept, s'.gpr r = s.gpr r
  r4 : s'.gpr .r4 = wAt (s.gpr .r4) (kOf s)
  r8 : s'.gpr .r8 = s.gpr .r8 - BitVec.ofNat 64 (kOf s)
  wr : s'.wr = s.wr
  rd : s'.rd = s.rd
  lr : s'.lr = s.lr
  out : ∀ b < kOf s, blockAt s'.mem (wAt (s.gpr .r4) b) =
    blockOut (scheduleAt s.mem (s.gpr .r7)) d (blockAt s.mem (wAt (s.gpr .r4) b))
  frame : Frame [stR s, ⟨s.gpr .r4, 8 * kOf s⟩] s.mem s'.mem

/-- The state words' region is inside the buffer. -/
theorem stR_sub (s : State) : Region.Sub (stR s) (frameR s) := Region.sub_prefix (by decide)

theorem frame_in {rs : List Region} {m m' : Mem} {r : Region} (h : Frame [r] m m') (hr : r ∈ rs) :
    Frame rs m m' :=
  h.mono fun r' h' => by simp only [List.mem_singleton] at h'; subst h'; exact hr

theorem batch_ok (d : Direction) {s : State} (h : BatchPre s) : WP isa (batch d) s (BatchPost d s) := by
  have hpos := h.pos
  have fit := h.data.fit
  generalize hk : kOf s = k
  have hk1 : 1 ≤ k := by rw [← hk, kOf]; omega
  have hk64 : k ≤ 64 := hk ▸ kOf_le s
  have hkn : k ≤ (s.gpr .r8).toNat := by rw [← hk, kOf]; omega
  let D := s.gpr .r4
  let B := s.gpr .r10
  let K := scheduleAt s.mem (s.gpr .r7)
  let L : List Region := [stR s, ⟨D, 8 * k⟩]
  have inS : stR s ∈ L := List.mem_cons_self
  have inD : (⟨D, 8 * k⟩ : Region) ∈ L := List.mem_cons_of_mem _ List.mem_cons_self
  have hdisj : (⟨D, 8 * k⟩ : Region).Disjoint (stR s) :=
    (h.data.sep.sub_left (Region.sub_prefix (by omega))).sub_right (stR_sub s)
  have hBk : Region.Sub ⟨B, 8 * k⟩ (stR s) := Region.sub_prefix (by omega)
  have keyFrame : ∀ r ∈ L, (⟨s.gpr .r7, 384⟩ : Region).Disjoint r := fun r hr => by
    simp only [L, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.sched.sep.sub_right (stR_sub s)
    · exact (h.data.key.sub_left (Region.sub_prefix (by omega))).symm
  have dataW : Covers [⟨D, 8 * k⟩] s.wr := Proof.Gather.PPC64LE.covers_prefix h.data.wr (by omega)
  have bufW : Covers [⟨B, 8 * k⟩] s.wr :=
    covers_of_sub h.room.frame (off := 0) (by simp [frameR, B]) (by simp [frameR]; omega)
  unfold batch
  -- the batch's blocks
  apply WP.seq
  refine WP.mono (batchBlocks_ok s) fun s₁ ⟨b₁, g₁, m₁, wr₁, rd₁, lr₁⟩ => ?_
  rw [hk] at b₁
  -- the copy in
  apply WP.seq
  refine WP.mono (copyBatch_ok (src := .r4) (dst := base) (S := D) (D := B) s₁ hk1 hk64 (g₁ _ (by decide))
    (g₁ _ (by decide)) b₁ (by decide)
    (by rw [rd₁, wr₁]; exact covers_rdwr dataW)
    (by rw [wr₁]; exact bufW) (hdisj.sub_right hBk)) fun s₂ ⟨c₂, f₂, _, g₂, a4₂, wr₂, rd₂, lr₂⟩ => ?_
  have k₂ : ∀ r, r ∉ Proof.Gather.PPC64LE.copyRegs → r ≠ .r12 → s₂.gpr r = s.gpr r := fun r a b =>
    (g₂ r a).trans (g₁ r b)
  have s10₂ : s₂.gpr .r10 = B := k₂ _ (by decide) (by decide)
  have h₂ : Room s₂ := h.room.congr s10₂ (wr₂.trans wr₁)
  have fs₂ : Frame [stR s] s.mem s₂.mem := by
    rw [← m₁]
    exact f₂.sub fun r hr => ⟨stR s, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact hBk⟩
  have w₂ : ∀ b < k, words s₂ b = s.mem.readW (wAt D b) 64 := by
    intro b hb
    simp only [words, sl, Straight.wordAddr, s10₂]
    refine readW_of_bytes fun i hi => ?_
    have e := c₂ (8 * b + i) (by omega)
    rw [m₁] at e
    rw [Offset.add_add, e, ← Offset.add_add]
  -- the transposition
  apply WP.seq
  obtain ⟨s₃, run₃, w₃, rd₃, wr₃, -, lr₃, s10₃, k₃, f₃⟩ :=
    transpose_ok h₂ (masksAt_frame s10₂ fs₂ h.masks)
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have s10₃ : s₃.gpr .r10 = B := s10₃.trans s10₂
  have hc₃ : ∀ r ∈ [Reg.r4, .r7, .r8, .r11], s₃.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [k₃ _ (by decide), a4₂, g₁ _ (by decide)]
    all_goals rw [k₃ _ (by decide), k₂ _ (by decide) (by decide)]
  have wr₃' : s₃.wr = s.wr := wr₃.trans (wr₂.trans wr₁)
  have rd₃' : s₃.rd = s.rd := rd₃.trans (rd₂.trans rd₁)
  have h₃ : Room s₃ := h.room.congr s10₃ wr₃'
  have fs₃ : Frame [stR s] s.mem s₃.mem := fs₂.trans (by rw [← stR_congr s10₂]; exact f₃)
  have hs₃ : Sched s₃ := h.sched.congr (hc₃ .r7 (by decide)) s10₃ rd₃'
  have ho₃ : Ones s₃ := by rw [Ones, hc₃ .r11 (by decide)]; exact h.ones
  have K₃ : scheduleAt s₃.mem (s₃.gpr .r7) = K := by
    rw [hc₃ .r7 (by decide)]
    exact VG.Proof.TripleDes.scheduleAt_eq_of_frame _ fs₃ fun r hr => keyFrame r (by
      simp only [List.mem_singleton] at hr; subst hr; exact inS)
  -- the passes
  apply WP.seq
  refine WP.mono (WP.rdwr (passes_ok d h₃ hs₃ ho₃)) fun s₄ ⟨⟨w₄, k₄, rd₄, wr₄, _, lr₄, f₄⟩, _⟩ => ?_
  have s10₄ : s₄.gpr .r10 = B := (k₄ _ (by decide)).trans s10₃
  have wr₄' : s₄.wr = s.wr := wr₄.trans wr₃'
  have h₄ : Room s₄ := h.room.congr s10₄ wr₄'
  have fs₄ : Frame [stR s] s.mem s₄.mem := fs₃.trans (by rw [← stR_congr s10₃]; exact f₄)
  -- the transposition back
  apply WP.seq
  obtain ⟨s₅, run₅, w₅, rd₅, wr₅, -, lr₅, s10₅, k₅, f₅⟩ :=
    transpose_ok h₄ (masksAt_frame s10₄ fs₄ h.masks)
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have s10₅ : s₅.gpr .r10 = B := s10₅.trans s10₄
  have wr₅' : s₅.wr = s.wr := wr₅.trans wr₄'
  have fs₅ : Frame [stR s] s.mem s₅.mem := fs₄.trans (by rw [← stR_congr s10₄]; exact f₅)
  have hc₅ : ∀ r ∈ [Reg.r4, .r7, .r8, .r11], s₅.gpr r = s.gpr r := fun r hr => by
    have h1 : r ∈ transKept ∧ r ∈ passKept := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    rw [k₅ r h1.1, k₄ r h1.2, hc₃ r hr]
  -- the batch's blocks again
  apply WP.seq
  refine WP.mono (batchBlocks_ok s₅) fun s₆ ⟨b₆, g₆, m₆, wr₆, rd₆, lr₆⟩ => ?_
  rw [show kOf s₅ = k by rw [← hk, kOf, kOf, hc₅ .r8 (by decide)]] at b₆
  have wr₆' : s₆.wr = s.wr := wr₆.trans wr₅'
  have s10₆ : s₆.gpr .r10 = B := (g₆ _ (by decide)).trans s10₅
  have a4₆ : s₆.gpr .r4 = D := (g₆ _ (by decide)).trans (hc₅ .r4 (by decide))
  -- the copy out
  apply WP.seq
  refine WP.mono (copyBatch_ok (src := base) (dst := .r4) (S := B) (D := D) s₆ hk1 hk64 s10₆ a4₆ b₆ (by decide)
    (by rw [wr₆']; exact covers_rdwr bufW)
    (by rw [wr₆']; exact dataW) (hdisj.sub_right hBk).symm)
    fun s₇ ⟨c₇, f₇, r9₇, g₇, a4₇, wr₇, rd₇, lr₇⟩ => ?_
  have k₇ : ∀ r, r ∉ Proof.Gather.PPC64LE.copyRegs → r ≠ .r12 → s₇.gpr r = s₅.gpr r := fun r a b =>
    (g₇ r a).trans (g₆ r b)
  have r12₇ : s₇.gpr .r12 = BitVec.ofNat 64 k := (g₇ _ (by decide)).trans b₆
  -- the end
  let t₁ := s₇.write .r4 (s₇.gpr .r9 ||| s₇.gpr .r9)
  let t₂ := t₁.write .r8 (t₁.gpr .r8 - t₁.gpr .r12)
  refine WP.of_runBlock ⟨t₂, by
    rw [Impl.TripleDes.PPC64LE.rr, show left = .r8 from rfl, show batchN = .r12 from rfl, runBlock_cons,
      exec_logic, runStep_some, runBlock_cons, exec_sub, runStep_some, runBlock_nil], ?_⟩
  have frame : Frame L s.mem s₇.mem := by
    have a : Frame L s.mem s₅.mem := frame_in fs₅ inS
    have b : Frame L s₅.mem s₇.mem := by
      rw [← m₆]
      refine f₇.mono fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr; exact inD
    exact a.trans b
  subst hk
  refine ⟨fun r hr => ?_, ?_, ?_, wr₇.trans wr₆', rd₇.trans (rd₆.trans (rd₅.trans (rd₄.trans rd₃'))), lr₇.trans
    (lr₆.trans (lr₅.trans (lr₄.trans (lr₃.trans (lr₂.trans lr₁))))), fun b hb => ?_, frame⟩
  · simp only [batchKept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simp only [t₂, t₁, gpr_write, reduceCtorEq, ite_false]
      rw [k₇ _ (by decide) (by decide), s10₅]
    all_goals
      simp only [t₂, t₁, gpr_write, reduceCtorEq, ite_false]
      rw [k₇ _ (by decide) (by decide), hc₅ _ (by decide)]
  · simp only [t₂, t₁, gpr_write, reduceCtorEq, ite_false, ite_true, r9₇, BitVec.or_self, wAt, D]
  · simp only [t₂, t₁, gpr_write, reduceCtorEq, ite_false, ite_true, r12₇]
    rw [k₇ _ (by decide) (by decide), hc₅ _ (by decide)]
  · -- every block of the batch
    have hb64 : b < 64 := by omega
    show blockAt t₂.mem (wAt D b) = blockOut K d (blockAt s.mem (wAt D b))
    have lane₃ : ipLane (words s₃) b = permute ip (decodeBlock (blockAt s.mem (wAt D b))) := by
      rw [VG.Proof.TripleDes.Bitslice.ipLane_congr w₃ b]
      refine VG.Proof.TripleDes.Bitslice.ipLane_transpose _ _ hb64 fun j hj => ?_
      rw [w₂ b hb]
      exact readW_bit s.mem (wAt D b) hj
    have word₇ : s₇.mem.readW (wAt D b) 64 = transposeW (words s₄) b := by
      rw [← w₅ b hb64]
      simp only [words, sl, Straight.wordAddr, s10₅]
      refine readW_of_bytes fun i hi => ?_
      have e := c₇ (8 * b + i) (by omega)
      rw [m₆] at e
      rw [wAt, Offset.add_add, e, Offset.add_add]
    rw [VG.Proof.TripleDes.Bitslice.blockOut_cores]
    apply blockAt_of_readW
    intro j hj
    rw [show t₂.mem = s₇.mem from rfl, word₇, VG.Proof.TripleDes.Bitslice.transpose_out _ _ j hj,
      VG.Proof.TripleDes.Bitslice.ipLane_congr w₄ b, VG.Proof.TripleDes.Bitslice.tdeaW_lane _ _ _ hb64,
      lane₃, K₃]

open VG.PPC64LE.Straight (wordAddr)
open VG.Proof.TripleDes.Bitslice (wAt_wAt blockAt_frame)

/-! ## The masks -/

def maskCode (k : Nat) : List Instr :=
  movImm64 .r12 (swapMask (maskShifts.getD k 1)) ++ ([.store .d .r12 base (maskOff + 8 * k)] : List Instr)

theorem storeMasks_eq : storeMasks = (List.range 6).flatMap maskCode := rfl

theorem movImm64_ok (d : Reg) (v : BitVec 64) (s : State) :
    ∃ s', runBlock isa (movImm64 d v) s = some s' ∧ s'.gpr d = v ∧ (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.lr = s.lr := by
  rw [movImm64, runBlock_cons, exec_lis, runStep_some, runBlock_cons, exec_ori, runStep_some,
    runBlock_cons, exec_lsl (by decide), runStep_some, runBlock_cons, exec_oris, runStep_some,
    runBlock_cons, exec_ori, runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [gpr_write_self]
    exact movImm64_eq v
  · simp [gpr_write, hr]

theorem maskCode_ok {s : State} (h : Room s) {k : Nat} (hk : k < 6) :
    WP isa (.block (maskCode k)) s fun s' =>
      s'.mem = s.mem.writeW (wordAddr (s.gpr .r10) (64 + k)) (swapMask (maskShifts.getD k 1)) ∧
      (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.wr = s.wr ∧ s'.rd = s.rd ∧ s'.lr = s.lr := by
  unfold maskCode
  obtain ⟨s₁, run₁, d₁, o₁, m₁, rd₁, wr₁, -, lr₁⟩ := movImm64_ok .r12 (swapMask (maskShifts.getD k 1)) s
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have b₁ : s₁.gpr .r10 = s.gpr .r10 := o₁ _ (by decide)
  have ea : s₁.gpr base + BitVec.ofNat 64 (maskOff + 8 * k) = wordAddr (s.gpr .r10) (64 + k) := by
    rw [show base = .r10 from rfl, b₁, wordAddr, show maskOff + 8 * k = 8 * (64 + k) by unfold maskOff; omega]
  have e := exec_store_d (s := s₁) (t := .r12) (n := base) (off := maskOff + 8 * k) (by decide)
    ⟨by unfold maskOff; omega, by unfold maskOff; omega⟩ (by rw [ea, wr₁]; exact slot_in h (by omega))
  let s₂ : State :=
    { s₁ with mem := s₁.mem.writeW (s₁.gpr base + BitVec.ofNat 64 (maskOff + 8 * k)) (s₁.gpr .r12) }
  refine WP.of_runBlock ⟨s₂, by rw [runBlock_cons, e, runStep_some, runBlock_nil], ?_, fun r hr => ?_,
    wr₁, rd₁, lr₁⟩
  · show s₁.mem.writeW (s₁.gpr base + BitVec.ofNat 64 (maskOff + 8 * k)) (s₁.gpr .r12) = _
    rw [ea, d₁, m₁]
  · exact o₁ r hr

theorem masks_ok {s : State} (h : Room s) : ∀ n ≤ 6,
    WP isa (.block ((List.range n).flatMap maskCode)) s fun s' =>
      (∀ k < n, s'.mem.readW (wordAddr (s.gpr .r10) (64 + k)) 64 = swapMask (maskShifts.getD k 1)) ∧
      (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.wr = s.wr ∧ s'.rd = s.rd ∧ s'.lr = s.lr ∧
      Frame [maskR s] s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun k hk => absurd hk (by omega), fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      WP.block_append_iff]
    refine WP.mono (masks_ok h n (by omega)) fun s₁ ⟨m₁, g₁, w₁, rd₁, lr₁, f₁⟩ => ?_
    have b₁ : s₁.gpr .r10 = s.gpr .r10 := g₁ _ (by decide)
    have h₁ : Room s₁ := h.congr b₁ w₁
    refine WP.mono (maskCode_ok h₁ (k := n) (by omega)) fun s₂ ⟨m₂, g₂, w₂, rd₂, lr₂⟩ =>
      ⟨fun k hk => ?_, fun r a => (g₂ r a).trans (g₁ r a), w₂.trans w₁, rd₂.trans rd₁, lr₂.trans lr₁, ?_⟩
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
        rw [show 8 * (64 + n) = 8 * 64 + 8 * n by omega, ← Offset.add_add]
        exact Offset.contains_base _ (by omega) (by omega))

/-! ## The setup -/

/-- The saved registers' slots, from the scratch buffer's base. -/
def savedL : List (Reg × Nat) := saved.map fun (r, o) => (r, savedOff + o)

theorem savedL_fits : Spill.Fits savedL := by decide

theorem savedL_le : ∀ p ∈ savedL, 560 ≤ p.2 ∧ p.2 + 8 ≤ 712 := by decide

theorem savedL_restorable : Spill.Restorable .r10 savedL := by decide

/-- What the setup needs: the scratch buffer writable. -/
structure SetupPre (u : State) : Prop where
  buf : (⟨u.gpr .r6, 1024⟩ : Region) ∈ u.wr

structure SetupPost (u v : State) : Prop where
  room : Room v
  r10 : v.gpr .r10 = u.gpr .r6
  r7 : v.gpr .r7 = u.gpr .r3
  r8 : v.gpr .r8 = u.gpr .r5
  r4 : v.gpr .r4 = u.gpr .r4
  ones : Ones v
  masks : MasksAt v
  saved : Spill.Saved (u.gpr .r6) u.gpr savedL v.mem
  rd : v.rd = u.rd
  wr : v.wr = u.wr
  lr : v.lr = u.lr
  frame : Frame [⟨u.gpr .r6, 1024⟩] u.mem v.mem

theorem ones_eq : ((0xFFFF : BitVec 16) ++ (0 : BitVec 16)).signExtend 64 ||| (0xFFFF : BitVec 16).setWidth 64 =
    BitVec.allOnes 64 := by decide

theorem setup_ok {u : State} (h : SetupPre u) : WP isa (.block setup) u (SetupPost u) := by
  have hb : setup = Spill.saveCode .r6 savedL ++
      ([Impl.TripleDes.PPC64LE.rr base .r6, Impl.TripleDes.PPC64LE.rr sched .r3,
        Impl.TripleDes.PPC64LE.rr left .r5, .lis ones 0xFFFF, .ori ones ones 0xFFFF] ++ storeMasks) := by
    rw [setup, List.append_assoc]; rfl
  rw [hb]
  refine Spill.save_ok (by decide) savedL_fits.1 (fun p hp =>
    ⟨_, h.buf, Offset.contains_base _ (by have := (savedL_le p hp).2; omega)
      (by have := (savedL_le p hp).2; omega)⟩) ?_
  let u₁ : State := { u with mem := Spill.saveMem u.mem (u.gpr .r6) u.gpr savedL }
  let u₂ := u₁.write .r10 (u₁.gpr .r6 ||| u₁.gpr .r6)
  let u₃ := u₂.write .r7 (u₂.gpr .r3 ||| u₂.gpr .r3)
  let u₄ := u₃.write .r8 (u₃.gpr .r5 ||| u₃.gpr .r5)
  let u₅ := u₄.write .r11 (((0xFFFF : BitVec 16) ++ (0 : BitVec 16)).signExtend 64)
  let u₆ := u₅.write .r11 (u₅.gpr .r11 ||| (0xFFFF : BitVec 16).setWidth 64)
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨u₆, by
    rw [Impl.TripleDes.PPC64LE.rr, Impl.TripleDes.PPC64LE.rr, Impl.TripleDes.PPC64LE.rr,
      show base = .r10 from rfl, show sched = .r7 from rfl, show left = .r8 from rfl, show ones = .r11 from rfl,
      runBlock_cons, exec_logic, runStep_some, runBlock_cons, exec_logic, runStep_some, runBlock_cons,
      exec_logic, runStep_some, runBlock_cons, exec_lis, runStep_some, runBlock_cons, exec_ori,
      runStep_some, runBlock_nil], ?_⟩
  have g₆ : ∀ r, r ≠ .r10 → r ≠ .r7 → r ≠ .r8 → r ≠ .r11 → u₆.gpr r = u.gpr r := fun r a b c d => by
    simp [u₆, u₅, u₄, u₃, u₂, u₁, gpr_write, a, b, c, d]
  have r10₆ : u₆.gpr .r10 = u.gpr .r6 := by simp [u₆, u₅, u₄, u₃, u₂, u₁, gpr_write]
  have r7₆ : u₆.gpr .r7 = u.gpr .r3 := by simp [u₆, u₅, u₄, u₃, u₂, u₁, gpr_write]
  have r8₆ : u₆.gpr .r8 = u.gpr .r5 := by simp [u₆, u₅, u₄, u₃, u₂, u₁, gpr_write]
  have r11₆ : u₆.gpr .r11 = BitVec.allOnes 64 := by
    simp only [u₆, u₅, gpr_write_self]; exact ones_eq
  have m₆ : u₆.mem = Spill.saveMem u.mem (u.gpr .r6) u.gpr savedL := rfl
  have f₆ : Frame [⟨u.gpr .r6, 1024⟩] u.mem u₆.mem := by
    rw [m₆]
    exact Spill.saveMem_frame_base (fun p hp => by have := (savedL_le p hp).2; omega) (by decide) _ _ _
  have h₆ : Room u₆ := ⟨by simp only [frameR, r10₆]; exact h.buf⟩
  -- the masks
  rw [storeMasks_eq]
  refine WP.mono (masks_ok h₆ 6 (Nat.le_refl _)) fun v ⟨m₇, g₇, w₇, rd₇, lr₇, f₇⟩ => ?_
  have hm₇ : maskR u₆ = ⟨u.gpr .r6 + BitVec.ofNat 64 512, 48⟩ := by
    simp only [maskR, r10₆, wordAddr]
  rw [hm₇] at f₇
  have r10₇ : v.gpr .r10 = u.gpr .r6 := (g₇ _ (by decide)).trans r10₆
  refine ⟨h₆.congr (g₇ _ (by decide)) w₇, r10₇, (g₇ _ (by decide)).trans r7₆, (g₇ _ (by decide)).trans r8₆,
    (g₇ _ (by decide)).trans (g₆ _ (by decide) (by decide) (by decide) (by decide)),
    by rw [Ones, g₇ _ (by decide)]; exact r11₆, fun k hk => by rw [r10₇, ← r10₆]; exact m₇ k hk, ?_,
    rd₇, w₇, lr₇, ?_⟩
  · -- the saved registers
    have sv₆ : Spill.Saved (u.gpr .r6) u.gpr savedL u₆.mem := by
      rw [m₆]; exact Spill.saveMem_saved savedL_fits u.mem (u.gpr .r6) u.gpr
    exact sv₆.frame_in (lo := 560) (n := 152) (fun p hp => ⟨(savedL_le p hp).1, by
      have := (savedL_le p hp).2; omega⟩) f₇ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  · exact f₆.trans (f₇.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub_base _ (by omega)⟩)

/-! ## The batches -/

/-- What stays true of the data, the schedule and the buffer through the
batches. -/
structure LoopEnv (B D S : Addr) (n : Nat) (R W : List Region) : Prop where
  data : Covers [⟨D, 8 * n⟩] W
  fit : D.toNat + 8 * n ≤ 2 ^ 64
  sep : (⟨D, 8 * n⟩ : Region).Disjoint ⟨B, 1024⟩
  key : (⟨D, 8 * n⟩ : Region).Disjoint ⟨S, 384⟩
  schedRd : (⟨S, 384⟩ : Region) ∈ R
  schedSep : (⟨S, 384⟩ : Region).Disjoint ⟨B, 1024⟩

/-- After the first `p` blocks. -/
structure LoopInv (d : Direction) (s : State) (B D S : Addr) (n : Nat) (K : Schedule)
    (g : Reg → BitVec 64) (R W : List Region) (L : Addr) (p : Nat) (v : State) : Prop where
  le : p ≤ n
  r10 : v.gpr .r10 = B
  r7 : v.gpr .r7 = S
  ones : Ones v
  masks : MasksAt v
  sched : scheduleAt v.mem S = K
  r4 : v.gpr .r4 = wAt D p
  r8 : v.gpr .r8 = BitVec.ofNat 64 (n - p)
  rd : v.rd = R
  wr : v.wr = W
  lr : v.lr = L
  room : Room v
  done : ∀ b < p, blockAt v.mem (wAt D b) = blockOut K d (blockAt s.mem (wAt D b))
  rest : ∀ b, p ≤ b → b < n → blockAt v.mem (wAt D b) = blockAt s.mem (wAt D b)
  saved : Spill.Saved B g savedL v.mem

/-- A region apart from a nonempty one is not the whole address space. -/
theorem len_lt_of_disjoint {D B : Addr} {n m : Nat} (h : (⟨D, n⟩ : Region).Disjoint ⟨B, m⟩) (hm : 0 < m)
    (hn : n ≤ 2 ^ 64) : n < 2 ^ 64 := by
  refine Nat.lt_of_le_of_ne hn fun e => h B ?_ ?_
  · simp only [Region.Contains, e]; have := (B - D).isLt; omega
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

theorem batch_step {d : Direction} {s : State} {B D S : Addr} {n : Nat} {K : Schedule}
    {g : Reg → BitVec 64} {R W : List Region} {L : Addr} (E : LoopEnv B D S n R W) {p : Nat} (hp : p < n)
    {v : State} (I : LoopInv d s B D S n K g R W L p v) :
    WP isa (batch d) v fun v' => LoopInv d s B D S n K g R W L (p + min (n - p) 64) v' := by
  have fit := E.fit
  have hlt : 8 * n < 2 ^ 64 := len_lt_of_disjoint E.sep (by decide) (by omega)
  have hrem : (v.gpr .r8).toNat = n - p := by rw [I.r8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hkv : kOf v = min (n - p) 64 := by rw [kOf, hrem]
  have hDp : (wAt D p).toNat = D.toNat + 8 * p := by
    rw [wAt, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * p) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have dataSubN : Region.Sub ⟨wAt D p, 8 * (n - p)⟩ ⟨D, 8 * n⟩ := Offset.sub_base _ (by omega)
  have pre : BatchPre v := by
    refine ⟨I.room, ⟨by rw [I.r7, I.rd]; exact E.schedRd, by
        simp only [frameR, I.r7, I.r10]; exact E.schedSep⟩, I.ones, I.masks, by omega,
      ⟨?_, by rw [hrem, I.r4, hDp]; omega, ?_, ?_⟩⟩
    · rw [I.wr, I.r4, hrem]
      exact Proof.Gather.PPC64LE.covers_off E.data (by omega) hlt
    · simp only [frameR, I.r4, I.r10, hrem]
      exact E.sep.sub_left dataSubN
    · simp only [I.r4, I.r7, hrem]
      exact E.key.sub_left dataSubN
  refine WP.mono (batch_ok d pre) fun v' q => ?_
  obtain ⟨qk, q4, q8, qwr, qrd, qlr, qout, qframe⟩ := q
  rw [hkv] at q4 q8 qout qframe
  generalize hk : min (n - p) 64 = k at q4 q8 qout qframe
  have hk1 : 1 ≤ k := by omega
  have hkn : k ≤ n - p := by omega
  have hst : stR v = ⟨B, 512⟩ := by simp only [stR, I.r10]
  rw [hst, I.r4] at qframe
  rw [I.r4] at q4 qout
  rw [I.r7] at qout
  have dataSub : Region.Sub ⟨wAt D p, 8 * k⟩ ⟨D, 8 * n⟩ := Offset.sub_base _ (by omega)
  -- regions written by the batch, apart from the buffer's other words and the other blocks
  have offB : ∀ (lo m : Nat), 512 ≤ lo → lo + m ≤ 1024 →
      ∀ r ∈ [(⟨B, 512⟩ : Region), ⟨wAt D p, 8 * k⟩], Region.Disjoint ⟨B + BitVec.ofNat 64 lo, m⟩ r :=
    fun lo m h1 h2 r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint_base _ h1 (by omega)
      · exact (E.sep.sub_left dataSub).symm.sub_left (Offset.sub_base _ h2)
  have keyD : ∀ r ∈ [(⟨B, 512⟩ : Region), ⟨wAt D p, 8 * k⟩], (⟨S, 384⟩ : Region).Disjoint r :=
    fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact E.schedSep.sub_right (Region.sub_prefix (by omega))
      · exact (E.key.sub_left dataSub).symm
  have blk : ∀ b, (b < p ∨ p + k ≤ b) → b < n →
      ∀ r ∈ [(⟨B, 512⟩ : Region), ⟨wAt D p, 8 * k⟩], Region.Disjoint ⟨wAt D b, 8⟩ r := fun b hb hbn r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (E.sep.sub_left (Offset.sub_base _ (by omega))).sub_right (Region.sub_prefix (by omega))
    · simp only [wAt]
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
  have r10' : v'.gpr .r10 = B := (qk .r10 (by decide)).trans I.r10
  have r7' : v'.gpr .r7 = S := (qk .r7 (by decide)).trans I.r7
  refine ⟨by omega, r10', r7', by rw [Ones, qk .r11 (by decide)]; exact I.ones, ?_, ?_,
    by rw [q4, wAt_wAt], ?_, qrd.trans I.rd, qwr.trans I.wr, qlr.trans I.lr, I.room.congr (qk .r10 (by decide)) qwr,
    fun b hb => ?_, fun b hb hbn => ?_, ?_⟩
  · -- the masks
    intro j hj
    rw [r10', ← I.r10, ← I.masks j hj, I.r10]
    exact qframe.readW (Region.contains_self _ 8) (by
      intro r hr
      have := offB (512 + 8 * j) 8 (by omega) (by omega) r hr
      simp only [wordAddr]; rw [show 8 * (64 + j) = 512 + 8 * j by omega]; exact this) (by decide)
  · -- the schedule
    rw [← I.sched]
    exact VG.Proof.TripleDes.scheduleAt_eq_of_frame _ qframe keyD
  · rw [q8, I.r8, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) hkn]; congr 1; omega
  · -- the blocks done
    by_cases e : b < p
    · rw [blockAt_frame qframe (blk b (.inl e) (by omega)), I.done b e]
    · have hb' : b - p < k := by omega
      have := qout (b - p) hb'
      rw [wAt_wAt, show p + (b - p) = b by omega, I.sched, I.rest b (by omega) (by omega)] at this
      exact this
  · rw [blockAt_frame qframe (blk b (.inr hb) hbn), I.rest b (by omega) hbn]
  · exact I.saved.frame_in (lo := 560) (n := 152) (fun p hp => ⟨(savedL_le p hp).1, by
      have := (savedL_le p hp).2; omega⟩) qframe fun r hr => offB 560 152 (by omega) (by omega) r hr

theorem eval_nonzero8 (s : State) {a : Nat} (ha : a < 2 ^ 64) (h : s.gpr .r8 = BitVec.ofNat 64 a) :
    isa.eval (.nonzero .d left) s = some (decide (a ≠ 0)) :=
  eval_nonzero_ofNat s .r8 ha h

theorem loop_ok {d : Direction} {s : State} {B D S : Addr} {n : Nat} {K : Schedule}
    {g : Reg → BitVec 64} {R W : List Region} {L : Addr} (E : LoopEnv B D S n R W) (hn : 0 < n)
    {v : State} (I : LoopInv d s B D S n K g R W L 0 v) :
    WP isa (.loop (batch d) (.nonzero .d left)) v (LoopInv d s B D S n K g R W L n) := by
  have fit := E.fit
  have hlt : 8 * n < 2 ^ 64 := len_lt_of_disjoint E.sep (by decide) (by omega)
  refine WP.loop (M := isa) (fun m v => ∃ p, p < n ∧ m = n - p ∧ LoopInv d s B D S n K g R W L p v) ?_ n v
    ⟨0, hn, rfl, I⟩
  rintro m v ⟨p, hp, rfl, J⟩
  refine WP.mono (batch_step E hp J) fun v' J' => ?_
  rw [eval_nonzero8 _ (by omega) J'.r8]
  by_cases e : n - (p + min (n - p) 64) = 0
  · left
    refine ⟨by simp [e], ?_⟩
    rwa [show p + min (n - p) 64 = n by omega] at J'
  · right
    exact ⟨by simp [e], _, by omega, _, by omega, rfl, J'⟩

/-! ## The end -/

theorem finish_eq : finish = Spill.restoreCode .r10 savedL := rfl

theorem finish_ok {d : Direction} {s : State} {B D S : Addr} {n : Nat} {K : Schedule}
    {g : Reg → BitVec 64} {R W : List Region} {L : Addr} {v : State}
    (I : LoopInv d s B D S n K g R W L n v) :
    WP isa (.block finish) v fun y => (∀ r ∈ savedL.map Prod.fst, y.gpr r = g r) ∧ y.lr = L ∧
      ∀ b < n, blockAt y.mem (wAt D b) = blockOut K d (blockAt s.mem (wAt D b)) := by
  rw [finish_eq]
  refine WP.mono (Spill.restore_wp (b := .r10) (by decide) I.r10 savedL_fits.1 savedL_restorable
    (fun p hp => ?_) I.saved) fun y r => ⟨fun q hq => r.gpr_of (.inl hq), r.lr.trans I.lr, fun b hb => ?_⟩
  · have hf := I.room.frame
    rw [frameR, I.r10] at hf
    exact ⟨_, List.mem_append_right _ hf, Offset.contains_base _ (by have := (savedL_le p hp).2; omega)
      (by have := (savedL_le p hp).2; omega)⟩
  · rw [r.mem]; exact I.done b hb

/-! ## The function -/

theorem preserved_saved : ∀ r ∈ preserved, r ∈ savedL.map Prod.fst := by decide

/-- What ECB may assume: the schedule readable, the `n` blocks and the
scratch buffer writable, apart from each other, the blocks not wrapping
around. -/
structure EcbPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r3, 384⟩]
  wr : s.wr = [⟨s.gpr .r4, 8 * (s.gpr .r5).toNat⟩, ⟨s.gpr .r6, 1024⟩]
  keyData : (⟨s.gpr .r3, 384⟩ : Region).Disjoint ⟨s.gpr .r4, 8 * (s.gpr .r5).toNat⟩
  keyBuf : (⟨s.gpr .r3, 384⟩ : Region).Disjoint ⟨s.gpr .r6, 1024⟩
  dataBuf : (⟨s.gpr .r4, 8 * (s.gpr .r5).toNat⟩ : Region).Disjoint ⟨s.gpr .r6, 1024⟩
  fit : (s.gpr .r4).toNat + 8 * (s.gpr .r5).toNat ≤ 2 ^ 64

theorem ecb_wp (d : Direction) {s : State} (h : EcbPre s) :
    WP isa (Impl.TripleDes.PPC64LE.Bitslice.ecb d) s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.lr = s.lr ∧ ∀ b < (s.gpr .r5).toNat,
        blockAt s'.mem (wAt (s.gpr .r4) b) =
          blockOut (scheduleAt s.mem (s.gpr .r3)) d (blockAt s.mem (wAt (s.gpr .r4) b)) := by
  let D := s.gpr .r4
  let n := (s.gpr .r5).toNat
  let K := scheduleAt s.mem (s.gpr .r3)
  unfold Impl.TripleDes.PPC64LE.Bitslice.ecb
  have ev : isa.eval (.zero .d .r5) s = some (s.gpr .r5 == 0) := by
    change VG.PPC64LE.eval (.zero .d .r5) s = _
    simp only [VG.PPC64LE.eval, State.read, Size.bits, BitVec.setWidth_eq]
  refine WP.ite (s.gpr .r5 == 0) ev (fun hz => ?_) (fun hz => ?_)
  · have hn : (s.gpr .r5).toNat = 0 := by simp only [beq_iff_eq] at hz; simp [hz]
    exact WP.block_nil ⟨fun _ _ => rfl, rfl, fun b hb => absurd hb (by omega)⟩
  have hn : 0 < n := by
    have : s.gpr .r5 ≠ 0 := by simpa using hz
    have : (s.gpr .r5).toNat ≠ 0 := fun e => this (BitVec.eq_of_toNat_eq e)
    omega
  have bufW : (⟨s.gpr .r6, 1024⟩ : Region) ∈ s.wr := by rw [h.wr]; simp
  apply WP.seq
  refine WP.mono (setup_ok ⟨bufW⟩) fun v q => ?_
  have E : LoopEnv (s.gpr .r6) D (s.gpr .r3) n s.rd s.wr :=
    ⟨covers_of_sub (R := ⟨D, 8 * n⟩) (by rw [h.wr]; exact List.mem_cons_self) (off := 0) (by simp) (by simp),
      h.fit, h.dataBuf, h.keyData.symm, by rw [h.rd]; simp, h.keyBuf⟩
  have I0 : LoopInv d s (s.gpr .r6) D (s.gpr .r3) n K s.gpr s.rd s.wr s.lr 0 v :=
    ⟨Nat.zero_le _, q.r10, q.r7, q.ones, q.masks,
      by rw [VG.Proof.TripleDes.scheduleAt_eq_of_frame _ q.frame fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.keyBuf],
      by rw [q.r4]; exact (BitVec.add_zero _).symm,
      by rw [q.r8, Nat.sub_zero]; exact ((BitVec.ofNat_toNat 64 (s.gpr .r5)).trans (BitVec.setWidth_eq _)).symm,
      q.rd, q.wr, q.lr, q.room, fun b hb => absurd hb (by omega),
      fun b _ hbn => blockAt_frame q.frame fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (h.dataBuf.sub_left (Offset.sub_base _ (by omega))),
      q.saved⟩
  apply WP.seq
  refine WP.mono (loop_ok E hn I0) fun w J => ?_
  refine WP.mono (finish_ok J) fun y ⟨gy, ly, by_⟩ => ⟨fun r hr => gy r (preserved_saved r hr), ly, by_⟩

end VG.Proof.TripleDes.PPC64LE.Bitsliced
