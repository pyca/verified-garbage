module

public import VerifiedGarbage.Proof.Scrypt.BlockMix
public import VerifiedGarbage.Proof.Scrypt.AArch64.Common
public import VerifiedGarbage.Proof.Scrypt.AArch64.Salsa
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
public import VerifiedGarbage.Proof.Framework.AArch64.Depth
import VerifiedGarbage.Proof.Scrypt.Memory
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Scrypt.BlockMix
meta import VerifiedGarbage.Proof.Scrypt.AArch64.Common
meta import VerifiedGarbage.Proof.Scrypt.AArch64.Salsa
meta import VerifiedGarbage.Proof.Framework.AArch64.Spill
meta import VerifiedGarbage.Proof.Framework.AArch64.Depth
meta import VerifiedGarbage.Proof.Scrypt.Memory
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Sha256.Stream

/-!
# scryptBlockMix on AArch64: the loop's layout and invariants

The function's body runs inside a frame saving `x30`; the state `s₀` here is
the one the body starts in, and the frame is handled in
this file.
-/

@[expose] public section

namespace VG.Proof.Scrypt.AArch64.BlockMix

open VG VG.AArch64 VG.Impl.Scrypt.AArch64
open VG.Spec.Scrypt (bytesAt blk salsa)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Scrypt (yAt xBefore yAt_eq xBefore_succ)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open VG.Proof.MdStream.AArch64 (Upd wp_mov wp_addImm wp_subImm sub_ofNat)
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt add_ofNat toNat_add_ofNat contains_off sub_off disj_off
  InRegions.of_mem frame_bytesAt bytesAt_writeBytes_self xorBytes_length bytesAt_length blk_bytesAt)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev bP : Addr := s₀.gpr .x0
abbrev rr : Nat := (s₀.gpr .x1).toNat
abbrev yP : Addr := s₀.gpr .x2
abbrev sc : Addr := s₀.gpr .x4
abbrev bR : Region := ⟨bP s₀, rr s₀ * 128⟩
abbrev yR : Region := ⟨yP s₀, rr s₀ * 128⟩
abbrev scR : Region := ⟨sc s₀, 128⟩
/-- The input. -/
abbrev B : List Byte := bytesAt s₀.mem (bP s₀) (128 * rr s₀)

/-- `Y[2i]` goes to `y + 64 i`. -/
abbrev yE (i : Nat) : Addr := yP s₀ + BitVec.ofNat 64 (64 * i)
/-- `Y[2i + 1]` goes to `y + 64 (r + i)`. -/
abbrev yO (i : Nat) : Addr := yP s₀ + BitVec.ofNat 64 (64 * (rr s₀ + i))
/-- `B[2i]`. -/
abbrev bB (i : Nat) : Addr := bP s₀ + BitVec.ofNat 64 (128 * i)
/-- Where `X` is before the pair `(2k, 2k + 1)`. -/
def xP : Nat → Addr
  | 0 => bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)
  | k + 1 => yO s₀ k

/-- The caller's `x19`–`x24` are saved in the scratch space. -/
abbrev Saved (m : Mem) : Prop := Spill.Saved (sc s₀) s₀.gpr bmSaved m

end

/-- The callee-saved registers the code never writes (`x30` aside). -/
def others : List Reg := [.x25, .x26, .x27, .x28]

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [bR s₀]
  wr : s₀.wr = [yR s₀, scR s₀]
  y_s : (yR s₀).Disjoint (scR s₀)
  b_y : (bR s₀).Disjoint (yR s₀)
  b_s : (bR s₀).Disjoint (scR s₀)
  b_nw : (bP s₀).toNat + rr s₀ * 128 ≤ 2 ^ 64
  y_nw : (yP s₀).toNat + rr s₀ * 128 ≤ 2 ^ 64
  s_nw : (sc s₀).toNat + 128 ≤ 2 ^ 64
  x3 : s₀.gpr .x3 = s₀.gpr .x1
  pos : 0 < rr s₀

section
variable {s₀ : State} (hp : Pre s₀)
include hp

/-- `y` is not the whole address space, since `scratch` is not in it. -/
theorem r_lt : 128 * rr s₀ < 2 ^ 64 := by
  by_contra hc
  refine hp.y_s (sc s₀) ?_ (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith)
  simp only [Region.Contains]
  have := (sc s₀ - yP s₀).isLt
  omega_arith

theorem in_y {o n : Nat} (h : o + n ≤ 128 * rr s₀) :
    (yR s₀).Contains (yP s₀ + BitVec.ofNat 64 o) n :=
  contains_off (by omega_arith) (by have := r_lt hp; omega_arith)

theorem in_b {o n : Nat} (h : o + n ≤ 128 * rr s₀) :
    (bR s₀).Contains (bP s₀ + BitVec.ofNat 64 o) n :=
  contains_off (by omega_arith) (by have := r_lt hp; omega_arith)

/-- Two parts of `y`. -/
theorem y_disj {o₁ n₁ o₂ n₂ : Nat} (h : o₁ + n₁ ≤ o₂ ∨ o₂ + n₂ ≤ o₁) (h₁ : o₁ + n₁ ≤ 128 * rr s₀)
    (h₂ : o₂ + n₂ ≤ 128 * rr s₀) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) :
    Region.Disjoint ⟨yP s₀ + BitVec.ofNat 64 o₁, n₁⟩ ⟨yP s₀ + BitVec.ofNat 64 o₂, n₂⟩ :=
  have := r_lt hp
  disj_off _ h (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)

theorem y_sub {o n : Nat} (h : o + n ≤ 128 * rr s₀) : Region.Sub ⟨yP s₀ + BitVec.ofNat 64 o, n⟩ (yR s₀) :=
  sub_off (by omega_arith) (by have := r_lt hp; omega_arith)

theorem b_sub {o n : Nat} (h : o + n ≤ 128 * rr s₀) : Region.Sub ⟨bP s₀ + BitVec.ofNat 64 o, n⟩ (bR s₀) :=
  sub_off (by omega_arith) (by have := r_lt hp; omega_arith)

end

theorem in_s (s₀ : State) {o n : Nat} (h : o + n ≤ 128) :
    (scR s₀).Contains (sc s₀ + BitVec.ofNat 64 o) n :=
  contains_off h (by omega_arith)

theorem s_sub (s₀ : State) {o n : Nat} (h : o + n ≤ 128) :
    Region.Sub ⟨sc s₀ + BitVec.ofNat 64 o, n⟩ (scR s₀) :=
  sub_off h (by omega_arith)

/-! ## The loop invariant -/

/-- After `k` pairs. -/
structure Inv (s₀ : State) (k : Nat) (s : State) : Prop where
  k_le : k ≤ rr s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x19 : s.gpr .x19 = bB s₀ k
  x20 : s.gpr .x20 = yE s₀ k
  x21 : s.gpr .x21 = yO s₀ k
  x22 : s.gpr .x22 = sc s₀
  x23 : s.gpr .x23 = BitVec.ofNat 64 (rr s₀ - k)
  x24 : s.gpr .x24 = xP s₀ k
  keep : ∀ r ∈ others, s.gpr r = s₀.gpr r
  frame : Frame [yR s₀, scR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  done : ∀ i < k, bytesAt s.mem (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
    bytesAt s.mem (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)
  x : bytesAt s.mem (xP s₀ k) 64 = xBefore (B s₀) (rr s₀) (2 * k)

/-- The input is unchanged in any memory that differs from the initial one
only in `y` and `scratch`. -/
theorem b_frame {s₀ : State} (hp : Pre s₀) {m : Mem} (hf : Frame [yR s₀, scR s₀] s₀.mem m)
    {o n : Nat} (ho : o + n ≤ 128 * rr s₀) :
    bytesAt m (bP s₀ + BitVec.ofNat 64 o) n = bytesAt s₀.mem (bP s₀ + BitVec.ofNat 64 o) n := by
  refine frame_bytesAt hf (fun r hr => ?_) (by have := r_lt hp; omega_arith)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.b_y.sub_left (b_sub hp ho)
  · exact hp.b_s.sub_left (b_sub hp ho)

/-- Block `i` of the input. -/
theorem blk_B (s₀ : State) {i : Nat} (hi : i < 2 * rr s₀) :
    blk (B s₀) i = bytesAt s₀.mem (bP s₀ + BitVec.ofNat 64 (64 * i)) 64 :=
  blk_bytesAt _ _ (by omega_arith)

/-! ## A call of `vg_salsa20_8` on a block of `y` -/

/-- A 64-byte slot of `y` at offset `o`. -/
abbrev slot (s₀ : State) (o : Nat) : Region := ⟨yP s₀ + BitVec.ofNat 64 o, 64⟩

/-! ## One pair -/

theorem slot_s {s₀ : State} (hp : Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) :
    (slot s₀ o).Disjoint ⟨sc s₀, 64⟩ :=
  (hp.y_s.sub_left (y_sub hp ho)).sub_right (Region.sub_prefix (by omega_arith))

/-- What a call's frame keeps: our caller's saved registers. -/
theorem saved_keep {s₀ : State} (hp : Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) {m m' : Mem}
    (hf : Frame [slot s₀ o, ⟨sc s₀, 64⟩] m m') (h : Saved s₀ m) : Saved s₀ m' :=
  Spill.Saved.frame h hf fun p hp' r hr => by
  have hp8 : p.2 + 8 ≤ 128 ∧ 64 ≤ p.2 := by revert p; decide
  have hsub : Region.Sub ⟨sc s₀ + BitVec.ofNat 64 p.2, 8⟩ (scR s₀) := s_sub s₀ (by omega_arith)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (hp.y_s.sub_left (y_sub hp ho)).sub_right hsub |>.symm
  · have := disj_off (sc s₀) (o₁ := p.2) (n₁ := 8) (o₂ := 0) (n₂ := 64) (by omega_arith) (by omega_arith)
      (by omega_arith) (by omega_arith) (by omega_arith)
    simpa using this

/-- What a call's frame keeps: the other blocks of `y`. -/
theorem slot_keep {s₀ : State} (hp : Pre s₀) {o o' : Nat} (ho : o + 64 ≤ 128 * rr s₀)
    (ho' : o' + 64 ≤ 128 * rr s₀) (hd : o' + 64 ≤ o ∨ o + 64 ≤ o') {m m' : Mem}
    (hf : Frame [slot s₀ o, ⟨sc s₀, 64⟩] m m') :
    bytesAt m' (yP s₀ + BitVec.ofNat 64 o') 64 = bytesAt m (yP s₀ + BitVec.ofNat 64 o') 64 := by
  refine frame_bytesAt hf (fun r hr => ?_) (by omega_arith)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact y_disj hp hd ho' ho (by omega_arith) (by omega_arith)
  · exact slot_s hp ho'

theorem frame_big {s₀ : State} (hp : Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) {m m' : Mem}
    (hf : Frame [slot s₀ o, ⟨sc s₀, 64⟩] m m') : Frame [yR s₀, scR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨yR s₀, List.mem_cons_self, y_sub hp ho⟩
    · exact ⟨scR s₀, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by omega_arith)⟩

/-- The state after both halves of pair `k`. -/
structure Mid (s₀ : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x19 : s.gpr .x19 = bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))
  x20 : s.gpr .x20 = yE s₀ k
  x21 : s.gpr .x21 = yO s₀ k
  x22 : s.gpr .x22 = sc s₀
  x23 : s.gpr .x23 = BitVec.ofNat 64 (rr s₀ - k)
  keep : ∀ r ∈ others, s.gpr r = s₀.gpr r
  frame : Frame [yR s₀, scR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  done : ∀ i < k + 1, bytesAt s.mem (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
    bytesAt s.mem (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)

/-- The memory after pair `k`. -/
theorem mem_ok {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) {s s₂ s₅ : State}
    (h : Inv s₀ k s)
    (f₂ : Frame [slot s₀ (64 * k), ⟨sc s₀, 64⟩] s.mem s₂.mem)
    (b₂ : bytesAt s₂.mem (yE s₀ k) 64 =
      salsa (xorBytes (bytesAt s.mem (xP s₀ k) 64) (bytesAt s.mem (bB s₀ k) 64)))
    (f₅ : Frame [slot s₀ (64 * (rr s₀ + k)), ⟨sc s₀, 64⟩] s₂.mem s₅.mem)
    (b₅ : bytesAt s₅.mem (yO s₀ k) 64 = salsa (xorBytes (bytesAt s₂.mem (yE s₀ k) 64)
      (bytesAt s₂.mem (bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))) 64))) :
    Frame [yR s₀, scR s₀] s₀.mem s₅.mem ∧ Saved s₀ s₅.mem ∧
    ∀ i < k + 1, bytesAt s₅.mem (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
      bytesAt s₅.mem (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1) := by
  have lt := r_lt hp
  have oE : 64 * k + 64 ≤ 128 * rr s₀ := by omega_arith
  have oO : 64 * (rr s₀ + k) + 64 ≤ 128 * rr s₀ := by omega_arith
  have F₂ := h.frame.trans (frame_big hp oE f₂)
  have yE_eq : bytesAt s₂.mem (yE s₀ k) 64 = yAt (B s₀) (rr s₀) (2 * k) := by
    rw [b₂, h.x, b_frame hp h.frame (by omega_arith : 128 * k + 64 ≤ 128 * rr s₀),
      show 128 * k = 64 * (2 * k) by omega_arith, ← blk_B s₀ (by omega_arith), yAt_eq]
  have hb : bytesAt s₂.mem (bP s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))) 64 =
      blk (B s₀) (2 * k + 1) := by
    rw [blk_B s₀ (by omega_arith)]
    exact b_frame hp F₂ (by omega_arith)
  refine ⟨F₂.trans (frame_big hp oO f₅), saved_keep hp oO f₅ (saved_keep hp oE f₂ h.saved),
    fun i hi => ?_⟩
  by_cases hik : i = k
  · subst i
    refine ⟨?_, ?_⟩
    · rw [slot_keep hp oO oE (by omega_arith) f₅, yE_eq]
    · rw [b₅, yE_eq, hb, yAt_eq (B s₀) (rr s₀) (2 * k + 1), xBefore_succ]
  · have hi' : i < k := by omega_arith
    obtain ⟨d₁, d₂⟩ := h.done i hi'
    refine ⟨?_, ?_⟩
    · rw [slot_keep hp oO (by omega_arith) (by omega_arith) f₅, slot_keep hp oE (by omega_arith) (by omega_arith) f₂, d₁]
    · rw [slot_keep hp oO (by omega_arith) (by omega_arith) f₅, slot_keep hp oE (by omega_arith) (by omega_arith) f₂, d₂]

/-- The pointers move on. -/
theorem regs_ok {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) {s : State}
    (h : Mid s₀ k s) :
    WP isa (.block [mov .x24 .x21, .addImm .x .x19 .x19 64, .addImm .x .x20 .x20 64,
      .addImm .x .x21 .x21 64, .subImm .x .x23 .x23 1]) s (Inv s₀ (k + 1)) := by
  have lt := r_lt hp
  refine wp_mov fun s₆ u₆ => wp_addImm (by decide) fun s₇ u₇ => wp_addImm (by decide) fun s₈ u₈ =>
    wp_addImm (by decide) fun s₉ u₉ => wp_subImm (by decide) fun s₁₀ u₁₀ => WP.block_nil ?_
  have m₁₀ : s₁₀.mem = s.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem]
  have g : ∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x23 → r ≠ .x24 → s₁₀.gpr r = s.gpr r :=
    fun r h19 h20 h21 h23 h24 => by
      rw [u₁₀.other _ h23, u₉.other _ h21, u₈.other _ h20, u₇.other _ h19, u₆.other _ h24]
  refine ⟨(by omega_arith), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, h.rd]
  · rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, h.wr]
  · rw [u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, h.sp]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr,
      u₆.other _ (by decide), h.x19, add_ofNat]
    congr 2; omega_arith
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide),
      u₆.other _ (by decide), h.x20, add_ofNat]
    congr 2
  · rw [u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), h.x21, add_ofNat]
    congr 2
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h.x22]
  · rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), h.x23, sub_ofNat (by omega_arith)]
    congr 1
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.gpr, h.x21]
    rfl
  · intro r hr
    have : r ≠ .x19 ∧ r ≠ .x20 ∧ r ≠ .x21 ∧ r ≠ .x23 ∧ r ≠ .x24 := by
      simp only [others, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [g r this.1 this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2, h.keep r hr]
  · rw [m₁₀]; exact h.frame
  · rw [m₁₀]; exact h.saved
  · rw [m₁₀]; exact h.done
  · rw [m₁₀]
    show bytesAt s.mem (yO s₀ k) 64 = _
    rw [(h.done k (by omega_arith)).2]
    rfl

end VG.Proof.Scrypt.AArch64.BlockMix

/-!
# scryptBlockMix on AArch64: the whole function

The prologue saves our caller's `x19`–`x24` in `scratch` and sets up the
loop's registers; the loop runs the `r` pairs; the epilogue restores the
registers. Around all of it, a frame saves `x30`, which the calls replace.
-/

namespace VG.Proof.Scrypt.AArch64.BlockMix

open VG VG.AArch64 VG.Impl.Scrypt.AArch64
open VG.Spec.Scrypt (bytesAt blk blockMix)
open VG.Proof.Scrypt (yAt xBefore blockMix_eq flatMap_congr)
open VG.Proof.MdStream.AArch64 (Upd Mupd wp_mov wp_add wp_addImm wp_subImm wp_ldr wp_str
  eval_nonzero ofNat_beq_zero readW_writeW_save write_frame_bytes)
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt add_ofNat InRegions.of_mem frame_bytesAt bytesAt_add
  bytesAt_blocks bytesAt_congr)

/-! ## The prologue -/

/-- The memory after the prologue's stores. -/
abbrev saveMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (sc s₀) s₀.gpr bmSaved

theorem saveMem_saved (s₀ : State) : Saved s₀ (saveMem s₀) := Spill.saveMem_saved (by decide) _ _ _

theorem saveMem_frame (s₀ : State) : Frame [scR s₀] s₀.mem (saveMem s₀) :=
  Spill.saveMem_frame_base (by decide) (by decide) _ _ _

theorem prologue_eq : bmPrologue = Spill.saveCode .x4 bmSaved ++
    ([mov .x23 .x1, mov .x19 .x0, mov .x20 .x2, mov .x22 .x4,
     .lsl .x .x9 .x1 6, .add .x .x21 .x2 .x9,
     .lsl .x .x9 .x1 7, .add .x .x24 .x0 .x9, .subImm .x .x24 .x24 64] : List Instr) := rfl

theorem save_ok {s₀ : State} (hp : Pre s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s₁, s₁.gpr = s₀.gpr → s₁.rd = s₀.rd → s₁.wr = s₀.wr → s₁.sp = s₀.sp →
      s₁.mem = saveMem s₀ → WP isa (.block rest) s₁ Q) :
    WP isa (.block (Spill.saveCode .x4 bmSaved ++ rest)) s₀ Q :=
  Spill.save_ok (by decide) (fun p hp' => by
    rw [hp.wr]; exact InRegions.of_mem (by simp) (in_s s₀ (by revert p; decide)))
    (k _ rfl rfl rfl rfl rfl)

theorem shl_eq {x : BitVec 64} {n : Nat} (h : x.toNat * 2 ^ n < 2 ^ 64) :
    x <<< n = BitVec.ofNat 64 (x.toNat * 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, toNat_ofNat_lt h, Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

theorem add_sub64 (a : Addr) {n : Nat} (h : 64 ≤ n) :
    a + BitVec.ofNat 64 n - BitVec.ofNat 64 64 = a + BitVec.ofNat 64 (n - 64) := by
  rw [show n = (n - 64) + 64 by omega_arith, BitVec.ofNat_add, ← BitVec.add_assoc, Nat.add_sub_cancel,
    BitVec.add_sub_cancel]

/-- The registers the loop starts with. -/
theorem setup_ok {s₀ : State} (hp : Pre s₀) {s₁ : State} (g : s₁.gpr = s₀.gpr)
    (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (hsp : s₁.sp = s₀.sp) (hm : s₁.mem = saveMem s₀) :
    WP isa (.block [mov .x23 .x1, mov .x19 .x0, mov .x20 .x2, mov .x22 .x4,
     .lsl .x .x9 .x1 6, .add .x .x21 .x2 .x9,
     .lsl .x .x9 .x1 7, .add .x .x24 .x0 .x9, .subImm .x .x24 .x24 64]) s₁ (Inv s₀ 0) := by
  have lt : 128 * (s₀.gpr .x1).toNat < 2 ^ 64 := r_lt hp
  have pos := hp.pos
  refine wp_mov fun a ua => wp_mov fun b ub => wp_mov fun c uc => wp_mov fun d ud =>
    wp_lsl (by decide) fun e ue => wp_add fun f uf => wp_lsl (by decide) fun g' ug =>
    wp_add fun h uh => wp_subImm (by decide) fun i ui => WP.block_nil ?_
  have x1 : d.gpr .x1 = s₀.gpr .x1 := by
    rw [ud.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), g]
  have e9 : e.gpr .x9 = BitVec.ofNat 64 (64 * rr s₀) := by
    rw [ue.gpr, x1, shl_eq (by simp; omega_arith), Nat.mul_comm]
  have g9 : g'.gpr .x9 = BitVec.ofNat 64 (128 * rr s₀) := by
    rw [ug.gpr, uf.other _ (by decide), ue.other _ (by decide), x1, shl_eq (by simp; omega_arith),
      Nat.mul_comm]
  have hm' : i.mem = saveMem s₀ := by
    rw [ui.mem, uh.mem, ug.mem, uf.mem, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem, hm]
  have k : ∀ r, r ≠ .x9 → r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → r ≠ .x24 →
      i.gpr r = s₀.gpr r := fun r h9 h19 h20 h21 h22 h23 h24 => by
    rw [ui.other _ h24, uh.other _ h24, ug.other _ h9, uf.other _ h21, ue.other _ h9,
      ud.other _ h22, uc.other _ h20, ub.other _ h19, ua.other _ h23, g]
  refine ⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => absurd hi (by omega_arith), ?_⟩
  · rw [ui.rd, uh.rd, ug.rd, uf.rd, ue.rd, ud.rd, uc.rd, ub.rd, ua.rd, hrd]
  · rw [ui.wr, uh.wr, ug.wr, uf.wr, ue.wr, ud.wr, uc.wr, ub.wr, ua.wr, hwr]
  · rw [ui.sp, uh.sp, ug.sp, uf.sp, ue.sp, ud.sp, uc.sp, ub.sp, ua.sp, hsp]
  · rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide),
      uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.gpr, ua.other _ (by decide), g]
    simp
  · rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide),
      uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide), uc.gpr,
      ub.other _ (by decide), ua.other _ (by decide), g]
    simp
  · rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide), uf.gpr, e9,
      ue.other _ (by decide), ud.other _ (by decide), uc.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), g]
    simp
  · rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide),
      uf.other _ (by decide), ue.other _ (by decide), ud.gpr, uc.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), g]
  · rw [ui.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide),
      uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      uc.other _ (by decide), ub.other _ (by decide), ua.gpr, g]
    simp
  · rw [ui.gpr, uh.gpr, g9, ug.other _ (by decide), uf.other _ (by decide),
      ue.other _ (by decide), ud.other _ (by decide), uc.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), g, add_sub64 _ (by omega_arith)]
    rfl
  · intro r hr
    have : r ≠ .x9 ∧ r ≠ .x19 ∧ r ≠ .x20 ∧ r ≠ .x21 ∧ r ≠ .x22 ∧ r ≠ .x23 ∧ r ≠ .x24 := by
      simp only [others, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    obtain ⟨h9, h19, h20, h21, h22, h23, h24⟩ := this
    exact k r h9 h19 h20 h21 h22 h23 h24
  · rw [hm']; exact (saveMem_frame s₀).mono (by simp)
  · rw [hm']; exact saveMem_saved s₀
  · rw [hm']
    show bytesAt (saveMem s₀) (bP s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)) 64 =
      blk (B s₀) (2 * rr s₀ - 1)
    rw [blk_B s₀ (by omega_arith), show 64 * (2 * rr s₀ - 1) = 128 * rr s₀ - 64 by omega_arith]
    refine frame_bytesAt (saveMem_frame s₀) (fun r hr => ?_) (by omega_arith)
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.b_s.sub_left (b_sub hp (by omega_arith))

/-! ## The epilogue -/

theorem preserved_cases : ∀ r ∈ preserved, r ≠ .x30 → r ∈ bmSaved.map Prod.fst ∨ r ∈ others := by
  decide

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Inv s₀ (rr s₀) s) :
    WP isa (.block bmEpilogue) s fun s' => s'.mem = s.mem ∧ s'.sp = s.sp ∧
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s₀.gpr r) :=
  WP.mono (Spill.restore_wp (b := .x22) h.x22 (by decide) (by decide) (fun p hp' => by
      rw [h.rd, h.wr, hp.rd, hp.wr]; exact InRegions.of_mem (by simp) (in_s s₀ (by revert p; decide)))
    h.saved) fun s' h' => ⟨h'.mem, h'.sp, fun r hr h30 =>
      h'.gpr_of ((preserved_cases r hr h30).imp id (h.keep r))⟩

/-! ## The body of the frame -/

/-- The output, from the blocks the loop wrote. -/
theorem post_of {s₀ : State} {m : Mem}
    (h : ∀ i < rr s₀, bytesAt m (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
      bytesAt m (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)) :
    bytesAt m (yP s₀) (128 * rr s₀) = blockMix (rr s₀) (B s₀) := by
  rw [blockMix_eq, show 128 * rr s₀ = 64 * rr s₀ + 64 * rr s₀ by omega_arith, bytesAt_add,
    bytesAt_blocks, bytesAt_blocks]
  congr 1
  · refine flatMap_congr fun i hi => ?_
    rw [List.mem_range] at hi
    exact (h i hi).1
  · refine flatMap_congr fun i hi => ?_
    rw [List.mem_range] at hi
    rw [add_ofNat, ← Nat.mul_add]
    exact (h i hi).2

/-! ## The whole function -/

/-- The frame's 16 bytes are free. -/
structure Stack (s₀ : State) : Prop where
  sp16 : 16 ≤ s₀.sp.toNat
  b : Region.Disjoint ⟨s₀.sp - 16, 16⟩ (bR s₀)
  y : Region.Disjoint ⟨s₀.sp - 16, 16⟩ (yR s₀)
  s : Region.Disjoint ⟨s₀.sp - 16, 16⟩ (scR s₀)

theorem pre_of {s₀ : State} (h : Proof.Scrypt.blockMixAArch64.pre s₀) : Pre s₀ ∧ Stack s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  rw [h13] at h2 h3 h4 h8 h11
  exact ⟨⟨h1, h2, h3, h4, h5, h10, h11, h12, h13, h14⟩, ⟨h6, h7, h8, h9⟩⟩

/-- The state the body starts in, inside the frame. -/
abbrev inner (s₀ : State) : State :=
  { s₀ with sp := s₀.sp - 16, mem := s₀.mem.write (s₀.sp - 16) 8 (s₀.gpr .x30) }

end VG.Proof.Scrypt.AArch64.BlockMix

/-!
# scryptBlockMix on AArch64: the public arguments

Only the pointers and `r` are public: the registers that hold them agree
in two runs with the same public data (`agree₀`).
-/

namespace VG.Proof.Scrypt.AArch64.BlockMix

open VG VG.AArch64

theorem agree₀ {s₁ s₂ : State} (hpub : Proof.Scrypt.blockMixAArch64.pub s₁ s₂) :
    VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

end VG.Proof.Scrypt.AArch64.BlockMix
