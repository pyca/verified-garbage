module

public import VerifiedGarbage.Impl.Ecdsa.AArch64.VerifyHash
public import VerifiedGarbage.Proof.Ecdsa.Verify.Hash
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
public import VerifiedGarbage.Proof.Framework.AArch64.StackScratchConsts
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.MdStream.AArch64.Common
import VerifiedGarbage.Proof.Rc2.AArch64.Stream.Copy
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Impl.Ecdsa.AArch64.VerifyHash

/-!
# ECDSA verification of the hash function's output on AArch64: the conversion

Untrusted: everything here is checked by Lean. As on RISC-V
(`Proof/Ecdsa/Verify/RISCV64/Hash.lean`), whose structure this follows.
`convert_ok`: `convert len wide` writes `fixedDigest len wide` of the hash
at `x1` (`x2` bytes) to the first `len` bytes of the buffer at `x5`,
changing only the buffer's 80 bytes and the registers `x9`–`x13`, `x1` and
`x2`. Then `hashed` runs the verification of the `len` bytes on the buffer
(`hashed_correct`, `hashed_ct`), and `withStackScratch` allocates the buffer
(`verifyHash_verified_nil`, `verifyHash_verified_cons`).

The instruction steps are `Proof/MdStream/AArch64/Common.lean`'s
(`wp_ldrb`, `wp_strb`, …), and the copy of a short hash is RC2's
(`Proof.Rc2.AArch64.Stream.copy_ok`). The lemmas about bytes that do not
depend on the target are `Proof/Ecdsa/Verify/Hash.lean`'s.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64.Hash

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64.VerifyHash
open VG.Proof.MdStream.AArch64 (Upd Mupd wp_addImm wp_mov wp_movz wp_add wp_and wp_lsr wp_lsl wp_ldrb
  wp_strb eval_nonzero)

variable {len : Nat} {s : State}

/-- The registers `convert` writes. -/
abbrev clob : List Reg := [.x9, .x10, .x11, .x12, .x13, .x1, .x2]

/-- Every other general-purpose register, which `convert` keeps. -/
abbrev kept : List Reg := [.x0, .x3, .x4, .x5, .x6, .x7, .x8, .x14, .x15, .x16, .x17, .x19, .x20, .x21,
  .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x30]

theorem kept_of_not_clob {r : Reg} (h : r ∉ clob) : r ∈ kept := by
  cases r <;> simp_all

/-- `s` and `t` agree but on the registers `rs`, and have the same permissions. -/
structure Keep (rs : List Reg) (s t : State) : Prop where
  gpr : ∀ r, r ∉ rs → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr

/-- What `convert` needs of its state: the hash's bytes readable, the
buffer's 80 bytes writable and apart from them, neither wrapping around. -/
structure CPre (len : Nat) (s : State) : Prop where
  len1 : 0 < len
  len66 : len ≤ 66
  rd : ∀ i < (s.gpr .x2).toNat, InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 i) 1
  wr : ∀ i < 80, InRegions s.wr (s.gpr .x5 + BitVec.ofNat 64 i) 1
  sep : (⟨s.gpr .x5, 80⟩ : Region).Disjoint ⟨s.gpr .x1, (s.gpr .x2).toNat⟩
  fitB : (s.gpr .x5).toNat + 80 ≤ 2 ^ 64
  fitD : (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64

/-- The hash. -/
abbrev hashOf (s : State) : List Byte := Spec.Ecdsa.bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat

/-- The buffer's contents and what `convert` changes in memory. -/
structure MPost (len : Nat) (wide : Bool) (s t : State) : Prop where
  buf : ∀ i < len, t.mem (s.gpr .x5 + BitVec.ofNat 64 i) = (fixedDigest len wide (hashOf s)).getD i 0
  frame : Frame [⟨s.gpr .x5, 80⟩] s.mem t.mem

/-- What `convert` leaves. -/
structure CPost (len : Nat) (wide : Bool) (s t : State) : Prop where
  buf : ∀ i < len, t.mem (s.gpr .x5 + BitVec.ofNat 64 i) = (fixedDigest len wide (hashOf s)).getD i 0
  frame : Frame [⟨s.gpr .x5, 80⟩] s.mem t.mem
  keep : Keep clob s t
  sp : t.sp = s.sp
  vpres : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

/-! ## Bytes -/

theorem hash_byte {i : Nat} (hi : i < (s.gpr .x2).toNat) :
    (hashOf s).getD i 0 = s.mem (s.gpr .x1 + BitVec.ofNat 64 i) :=
  bytesAt_getD _ _ _ _ hi

/-- A byte of the buffer is not one of the hash's. -/
theorem buf_not_hash (hp : CPre len s) {x : Addr} (hx : (⟨s.gpr .x5, 80⟩ : Region).Contains x 1) {i : Nat}
    (hi : i < (s.gpr .x2).toNat) : x ≠ s.gpr .x1 + BitVec.ofNat 64 i := by
  rintro rfl
  exact hp.sep _ hx (Offset.contains_base _ (by omega) (by omega))

theorem setWidth_byte64 (b : Byte) : ((b.setWidth 64).setWidth 8 : Byte) = b := by
  ext i hi; simp

/-! ## Steps the common lemmas leave out -/

section
variable {is : List Instr} {Q : State → Prop}

theorem wp_orr {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ||| s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .orr .x d n m :: is)) s Q :=
  Proof.MdStream.AArch64.WP.cons (s' := s.write .x d (s.gpr n ||| s.gpr m)) (by simp [exec, State.read])
    (k _ (Upd.write64 _ _ _))

end

/-! ## The test -/

/-- `test`'s value is nonzero exactly when the hash has at least `len` bytes. -/
theorem test_value (x : BitVec 64) (h1 : 0 < len) (h66 : len ≤ 66) :
    ((x >>> 7 ||| ((x &&& (127 : BitVec 16).setWidth 64) + BitVec.ofNat 64 (128 - len)) >>> 7) != 0) =
      decide (len ≤ x.toNat) := by
  have hx := x.isLt
  have hm : (x &&& (127 : BitVec 16).setWidth 64).toNat = x.toNat % 128 := by
    rw [BitVec.toNat_and, show ((127 : BitVec 16).setWidth 64).toNat = 2 ^ 7 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  have ha : ((x &&& (127 : BitVec 16).setWidth 64) + BitVec.ofNat 64 (128 - len)).toNat =
      x.toNat % 128 + (128 - len) := by
    rw [BitVec.toNat_add, hm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 128 - len) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hz : ∀ y : BitVec 64, (y != 0) = decide (y.toNat ≠ 0) := fun y => by
    by_cases h : y.toNat = 0
    · have : y = 0 := BitVec.eq_of_toNat_eq (by rw [h]; rfl)
      subst this; rfl
    · rw [decide_eq_true h]
      exact bne_iff_ne.mpr fun e => h (by rw [e]; rfl)
  rw [hz, BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight, ha,
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  by_cases hb : x.toNat < 128
  · have e : x.toNat / 2 ^ 7 = 0 := Nat.div_eq_of_lt hb
    rw [e, Nat.zero_or, Nat.mod_eq_of_lt hb]
    simp only [Nat.reducePow]
    by_cases hl : len ≤ x.toNat
    · have : (x.toNat + (128 - len)) / 128 = 1 := by omega
      simp [this, hl]
    · have : (x.toNat + (128 - len)) / 128 = 0 := by omega
      simp [this, hl]
  · have hne : x.toNat / 2 ^ 7 ≠ 0 := by simp only [Nat.reducePow]; omega
    have : x.toNat / 2 ^ 7 ||| (x.toNat % 128 + (128 - len)) / 2 ^ 7 ≠ 0 := by
      intro h; exact hne (Nat.or_eq_zero_iff.mp h).1
    simp [this, show len ≤ x.toNat by omega]

/-- What `test` leaves: `x11` decides the branch, and only `x10`–`x12` change. -/
theorem test_ok {Q : State → Prop} (hp : CPre len s)
    (k : ∀ s₁, Keep [.x10, .x11, .x12] s s₁ → s₁.mem = s.mem → s₁.sp = s.sp →
      eval (.nonzero .x .x11) s₁ = some (decide (len ≤ (s.gpr .x2).toNat)) → Q s₁) :
    WP isa (.block (test len)) s Q := by
  have h1 := hp.len1
  have h66 := hp.len66
  unfold test
  refine wp_lsr (by decide) fun s₁ u₁ => wp_movz fun s₂ u₂ => wp_and fun s₃ u₃ =>
    wp_addImm (by omega) fun s₄ u₄ => wp_lsr (by decide) fun s₅ u₅ => wp_orr fun s₆ u₆ =>
      WP.block_nil (k s₆ ⟨fun r hr => ?_, ?_, ?_⟩ ?_ ?_ ?_)
  · have h10 : r ≠ .x10 := fun e => hr (by simp [e])
    have h11 : r ≠ .x11 := fun e => hr (by simp [e])
    have h12 : r ≠ .x12 := fun e => hr (by simp [e])
    rw [u₆.other _ h11, u₅.other _ h12, u₄.other _ h12, u₃.other _ h12, u₂.other _ h11, u₁.other _ h10]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · rw [eval_nonzero, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide)]
    rw [test_value _ h1 h66]

/-! ## The cases -/

/-- After `k` bytes of the long copy. -/
structure LInv (len : Nat) (s : State) (k : Nat) (u : State) : Prop where
  mem : ∀ j < k, u.mem (s.gpr .x5 + BitVec.ofNat 64 j) = s.mem (s.gpr .x1 + BitVec.ofNat 64 j)
  frame : Frame [⟨s.gpr .x5, 80⟩] s.mem u.mem
  x1 : u.gpr .x1 = s.gpr .x1
  x5 : u.gpr .x5 = s.gpr .x5
  rd : u.rd = s.rd
  wr : u.wr = s.wr

/-- A hash of at least `len` bytes: its leftmost `len`. -/
theorem long_ok {len : Nat} (wide : Bool) {s s₁ : State} (hp : CPre len s)
    (hk : Keep [.x10, .x11, .x12] s s₁) (hm : s₁.mem = s.mem)
    (hl : len ≤ (s.gpr .x2).toNat) :
    WP isa (.block (long len)) s₁ (MPost len wide s) := by
  have h66 := hp.len66
  have hB := hp.fitB
  refine WP.mono (wp_range_flatMap (M := isa) (LInv len s) (fun k u hk' h => ?_) len (Nat.le_refl _) s₁
    ⟨fun j hj => absurd hj (Nat.not_lt_zero _), by rw [hm]; exact Frame.refl _ _, hk.gpr _ (by decide),
      hk.gpr _ (by decide), hk.rd, hk.wr⟩) fun t ht => ⟨fun i hi => ?_, ht.frame⟩
  · refine wp_ldrb (a := s.gpr .x1 + BitVec.ofNat 64 k) (by omega) (by rw [h.x1])
      (by rw [h.rd, h.wr]; exact hp.rd k (by omega)) fun u₁ g₁ => ?_
    refine wp_strb (a := s.gpr .x5 + BitVec.ofNat 64 k) (by omega) (by rw [g₁.other _ (by decide), h.x5])
      (by rw [g₁.wr, h.wr]; exact hp.wr k (by omega)) fun u₂ g₂ => WP.block_nil ?_
    have hv : (u₁.gpr .x9).setWidth 8 = s.mem (s.gpr .x1 + BitVec.ofNat 64 k) := by
      rw [g₁.gpr, setWidth_byte64]
      exact h.frame _ fun r hr hc => by
        simp only [List.mem_singleton] at hr; subst hr
        exact buf_not_hash hp hc (i := k) (by omega) rfl
    have hm₂ : u₂.mem = u.mem.writeW (s.gpr .x5 + BitVec.ofNat 64 k) (s.mem (s.gpr .x1 + BitVec.ofNat 64 k)) := by
      rw [g₂.mem, g₁.mem, hv]
    refine ⟨fun j hj => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hm₂]
      by_cases e : j = k
      · subst e; rw [byte_writeW_eq]
      · rw [byte_writeW_ne' _ _ _ (by omega) (by omega) e, h.mem j (by omega)]
    · rw [hm₂]
      exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    · rw [g₂.gpr, g₁.other _ (by decide), h.x1]
    · rw [g₂.gpr, g₁.other _ (by decide), h.x5]
    · rw [g₂.rd, g₁.rd, h.rd]
    · rw [g₂.wr, g₁.wr, h.wr]
  · rw [ht.mem i hi, ← hash_byte (by omega), fixedDigest,
      ite_eq_left_of_eq_true _ _ (eq_true (by rw [length_bytesAt]; exact hl)),
      List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]

/-- The buffer holds the zeros and the hash (`tz`), in a state with the
entry's buffer pointer and permissions. -/
structure ZInv (len : Nat) (s u : State) : Prop where
  mem : ∀ j < 72, u.mem (s.gpr .x5 + BitVec.ofNat 64 j) = tz len (hashOf s) j
  frame : Frame [⟨s.gpr .x5, 80⟩] s.mem u.mem
  x5 : u.gpr .x5 = s.gpr .x5
  wr : u.wr = s.wr

/-- After `k` bytes of the shift. -/
structure SInv (len : Nat) (s : State) (k : Nat) (u : State) : Prop where
  mem : ∀ j < 72, u.mem (s.gpr .x5 + BitVec.ofNat 64 j) =
    if j < k then sh (tz len (hashOf s) j) (tz len (hashOf s) (j + 1)) else tz len (hashOf s) j
  frame : Frame [⟨s.gpr .x5, 80⟩] s.mem u.mem
  x5 : u.gpr .x5 = s.gpr .x5
  wr : u.wr = s.wr

theorem shift_ok (hp : CPre len s) (hl : (s.gpr .x2).toNat < len) {u : State} (hz : ZInv len s u) :
    WP isa (.block (shiftBytes len)) u (MPost len true s) := by
  have h66 := hp.len66
  have hB := hp.fitB
  refine WP.mono (wp_range_flatMap (M := isa) (SInv len s) (fun k u₁ hk h => ?_) len (Nat.le_refl _) u
    ⟨fun j hj => by simp only [Nat.not_lt_zero, ite_false]; exact hz.mem j hj, hz.frame, hz.x5, hz.wr⟩)
    fun t ht => ⟨fun i hi => ?_, ht.frame⟩
  · have hw : ∀ j < 80, InRegions u₁.wr (s.gpr .x5 + BitVec.ofNat 64 j) 1 := fun j hj => by
      rw [h.wr]; exact hp.wr j hj
    refine wp_ldrb (a := s.gpr .x5 + BitVec.ofNat 64 k) (by omega) (by rw [h.x5])
      (inRegions_wr (hw k (by omega))) fun u₂ g₂ => ?_
    refine wp_ldrb (a := s.gpr .x5 + BitVec.ofNat 64 (k + 1)) (by omega)
      (by rw [g₂.other _ (by decide), h.x5])
      (by rw [g₂.rd, g₂.wr]; exact inRegions_wr (hw (k + 1) (by omega))) fun u₃ g₃ => ?_
    refine wp_lsl (by decide) fun u₄ g₄ => wp_lsr (by decide) fun u₅ g₅ => wp_add fun u₆ g₆ => ?_
    refine wp_strb (a := s.gpr .x5 + BitVec.ofNat 64 k) (by omega)
      (by rw [g₆.other _ (by decide), g₅.other _ (by decide), g₄.other _ (by decide), g₃.other _ (by decide),
        g₂.other _ (by decide), h.x5])
      (by rw [g₆.wr, g₅.wr, g₄.wr, g₃.wr, g₂.wr]; exact hw k (by omega)) fun u₇ g₇ => WP.block_nil ?_
    have hv : (u₆.gpr .x9).setWidth 8 = sh (tz len (hashOf s) k) (tz len (hashOf s) (k + 1)) := by
      rw [g₆.gpr, g₅.other _ (by decide), g₅.gpr, g₄.gpr, g₄.other _ (by decide), g₃.gpr, g₃.other _ (by decide),
        g₂.gpr, g₂.mem, h.mem k (by omega), h.mem (k + 1) (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega)]
      exact shift_byte _ _
    have hm : u₇.mem = u₁.mem.writeW (s.gpr .x5 + BitVec.ofNat 64 k)
        (sh (tz len (hashOf s) k) (tz len (hashOf s) (k + 1))) := by
      rw [g₇.mem, hv, g₆.mem, g₅.mem, g₄.mem, g₃.mem, g₂.mem]
    refine ⟨fun j hj => ?_, ?_, ?_, ?_⟩
    · rw [hm]
      by_cases e : j = k
      · subst e; rw [byte_writeW_eq, ite_eq_left (by omega)]
      · rw [byte_writeW_ne' _ _ _ (by omega) (by omega) e, h.mem j hj]
        by_cases hjk : j < k
        · rw [ite_eq_left hjk, ite_eq_left (by omega)]
        · rw [ite_eq_right hjk, ite_eq_right (by omega)]
    · rw [hm]
      exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    · rw [g₇.gpr, g₆.other _ (by decide), g₅.other _ (by decide), g₄.other _ (by decide),
        g₃.other _ (by decide), g₂.other _ (by decide), h.x5]
    · rw [g₇.wr, g₆.wr, g₅.wr, g₄.wr, g₃.wr, g₂.wr, h.wr]
  · rw [ht.mem i (by omega), ite_eq_left hi, fixed_short (by rw [length_bytesAt]; exact hl) true hi]
    rfl

theorem tail_ok (wide : Bool) (hp : CPre len s) (hl : (s.gpr .x2).toNat < len) {u : State}
    (hz : ZInv len s u) :
    WP isa (.block (if wide then shiftBytes len else [])) u (MPost len wide s) := by
  cases wide with
  | true => exact shift_ok hp hl hz
  | false =>
    refine WP.block_nil ⟨fun i hi => ?_, hz.frame⟩
    rw [hz.mem i (by have := hp.len66; omega), fixed_short (by rw [length_bytesAt]; exact hl) false hi]
    rfl

/-- After `k` of the zero bytes. -/
structure ZsInv (s : State) (k : Nat) (u : State) : Prop where
  mem : ∀ j < k, u.mem (s.gpr .x5 + BitVec.ofNat 64 j) = 0
  frame : Frame [⟨s.gpr .x5, 80⟩] s.mem u.mem
  x12 : u.gpr .x12 = 0
  keep : Keep [.x10, .x11, .x12] s u
  sp : u.sp = s.sp

theorem zeros_ok (hp : CPre len s) {s₁ : State} (hk : Keep [.x10, .x11, .x12] s s₁) (hm : s₁.mem = s.mem)
    (hsp : s₁.sp = s.sp) :
    WP isa (.block (.movz .x .x12 0 0 :: zeroBytes)) s₁ (ZsInv s 72) := by
  have hB := hp.fitB
  refine wp_movz fun s₂ u₂ => ?_
  have h₀ : ZsInv s 0 s₂ :=
    ⟨fun j hj => absurd hj (Nat.not_lt_zero _), by rw [u₂.mem, hm]; exact Frame.refl _ _, by rw [u₂.gpr]; rfl,
      ⟨fun r hr => by
        rw [u₂.other r (fun e => hr (by simp [e])), hk.gpr r hr], by rw [u₂.rd, hk.rd], by rw [u₂.wr, hk.wr]⟩,
      by rw [u₂.sp, hsp]⟩
  refine wp_range_flatMap (M := isa) (ZsInv s) (fun k u hk' h => ?_) 72 (Nat.le_refl _) s₂ h₀
  have hx5 : u.gpr .x5 = s.gpr .x5 := h.keep.gpr _ (by decide)
  refine wp_strb (a := s.gpr .x5 + BitVec.ofNat 64 k) (by omega) (by rw [hx5])
    (by rw [h.keep.wr]; exact hp.wr k (by omega)) fun u₁ g₁ => WP.block_nil ?_
  have hm₁ : u₁.mem = u.mem.writeW (s.gpr .x5 + BitVec.ofNat 64 k) (0 : Byte) := by
    rw [g₁.mem, h.x12]; rfl
  refine ⟨fun j hj => ?_, ?_, by rw [g₁.gpr, h.x12], ⟨fun r hr => by rw [g₁.gpr, h.keep.gpr r hr],
    by rw [g₁.rd, h.keep.rd], by rw [g₁.wr, h.keep.wr]⟩, by rw [g₁.sp, h.sp]⟩
  · rw [hm₁]
    by_cases e : j = k
    · subst e; rw [byte_writeW_eq]
    · rw [byte_writeW_ne' _ _ _ (by omega) (by omega) e, h.mem j (by omega)]
  · rw [hm₁]
    exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))

theorem short_ok (wide : Bool) (hp : CPre len s) {s₁ : State} (hk : Keep [.x10, .x11, .x12] s s₁)
    (hm : s₁.mem = s.mem) (hsp : s₁.sp = s.sp) (hl : (s.gpr .x2).toNat < len) :
    WP isa (short len wide) s₁ (MPost len wide s) := by
  have h66 := hp.len66
  have hB := hp.fitB
  unfold short
  refine WP.seq (WP.block_append (WP.mono (zeros_ok hp hk hm hsp) fun s₂ h₂ => ?_))
  refine wp_addImm (by omega) fun s₃ u₃ => Proof.MdStream.AArch64.wp_sub fun s₄ u₄ => WP.block_nil ?_
  have e1 : s₄.gpr .x1 = s.gpr .x1 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), h₂.keep.gpr _ (by decide)]
  have e2 : s₄.gpr .x2 = s.gpr .x2 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), h₂.keep.gpr _ (by decide)]
  have e5 : s₄.gpr .x5 = s.gpr .x5 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), h₂.keep.gpr _ (by decide)]
  have et : s₄.gpr .x13 = s.gpr .x5 + BitVec.ofNat 64 (len - (s.gpr .x2).toNat) := by
    rw [u₄.gpr, u₃.gpr, u₃.other .x2 (by decide), h₂.keep.gpr .x5 (by decide), h₂.keep.gpr .x2 (by decide)]
    conv => lhs; rw [← ofNat_toNat64 (s.gpr .x2)]
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg, Offset.ofNat_sub_ofNat (by omega)]
  have em : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
  have ewr : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, h₂.keep.wr]
  have erd : s₄.rd = s.rd := by rw [u₄.rd, u₃.rd, h₂.keep.rd]
  have hz : ∀ j < 72, s₄.mem (s.gpr .x5 + BitVec.ofNat 64 j) = 0 := fun j hj => by
    rw [em]; exact h₂.mem j hj
  have hzf : Frame [⟨s.gpr .x5, 80⟩] s.mem s₄.mem := by rw [em]; exact h₂.frame
  have hdig : ∀ i < (s.gpr .x2).toNat, s₄.mem (s.gpr .x1 + BitVec.ofNat 64 i) =
      s.mem (s.gpr .x1 + BitVec.ofNat 64 i) := by
    intro i hi
    exact hzf _ fun r hr hc => by
      simp only [List.mem_singleton] at hr; subst hr
      exact buf_not_hash hp hc hi rfl
  -- The copy (`copy_ok`): the hash to `x13`, nothing if it is empty.
  refine WP.seq (Proof.Rc2.AArch64.Stream.copy_ok (src := .x1) (dst := .x13) (cnt := .x2) (so := 0) (dd := 0)
    (by decide) (by decide) ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    (A := s.gpr .x1) (B := s.gpr .x5 + BitVec.ofNat 64 (len - (s.gpr .x2).toNat)) (k := (s.gpr .x2).toNat)
    (by rw [e1, BitVec.add_zero]) (by rw [et, BitVec.add_zero]) (by rw [e2, ofNat_toNat64]) (s.gpr .x2).isLt
    (fun i hi => by rw [erd, ewr]; exact hp.rd i hi)
    (fun i hi => by rw [ewr, Offset.add_add]; exact hp.wr _ (by omega))
    (fun x h2 h1 => hp.sep x (in_buf (off := len - (s.gpr .x2).toNat) (n := (s.gpr .x2).toNat) h1 (by omega)) h2)
    fun t ht => ?_)
  have hlen : (Spec.Rc2.bytesAt s₄.mem (s.gpr .x1) (s.gpr .x2).toNat).length = (s.gpr .x2).toNat := by
    simp [Spec.Rc2.bytesAt]
  refine tail_ok wide hp hl ⟨fun j hj => ?_, ?_, ?_, ?_⟩
  · -- The copied bytes are the hash's, at `len - digest_len`; the rest are the zeros.
    rw [ht.mem, WriteBytes.writeBytes, hlen, Offset.sub_toNat' _ (by omega) (by omega)]
    by_cases hin : len - (s.gpr .x2).toNat ≤ j ∧ j < len
    · simp only [hin.1, ite_true, show j - (len - (s.gpr .x2).toNat) < (s.gpr .x2).toNat by omega]
      rw [tz, ite_eq_left (by rw [length_bytesAt]; exact hin), length_bytesAt,
        show Spec.Rc2.bytesAt s₄.mem (s.gpr .x1) (s.gpr .x2).toNat =
          Spec.Ecdsa.bytesAt s₄.mem (s.gpr .x1) (s.gpr .x2).toNat from rfl,
        bytesAt_getD _ _ _ _ (by omega), hdig _ (by omega), hash_byte (by omega)]
    · have hn : ¬ ((if len - (s.gpr .x2).toNat ≤ j then j - (len - (s.gpr .x2).toNat)
          else 2 ^ 64 + j - (len - (s.gpr .x2).toNat)) < (s.gpr .x2).toNat) := by
        split <;> omega
      rw [ite_eq_right hn, hz j hj, tz, ite_eq_right (by rw [length_bytesAt]; exact hin)]
  · rw [ht.mem]
    refine hzf.trans (WriteBytes.writeBytes_frame _ _ _ ?_)
    rw [hlen]
    exact Offset.contains_base _ (by omega) (by omega)
  · rw [ht.other _ (by decide) (by decide) (by decide) (by decide), e5]
  · rw [ht.wr, ewr]

theorem convert_mem (wide : Bool) (hp : CPre len s) : WP isa (convert len wide) s (MPost len wide s) := by
  unfold convert
  refine WP.seq (test_ok hp fun s₁ hk hm hsp hev => ?_)
  refine WP.ite (decide (len ≤ (s.gpr .x2).toNat)) hev (fun h => long_ok wide hp hk hm ?_)
    (fun h => short_ok wide hp hk hm hsp ?_)
  · exact of_decide_eq_true h
  · exact Nat.lt_of_not_le (of_decide_eq_false h)

/-- Code keeps the permissions and the stack pointer. -/
theorem WP.rdwr {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.rdwr he⟩

/-- No instruction of `convert` writes a register of `kept`. -/
theorem convert_kept (wide : Bool) :
    (convert len wide).allInstrs (fun i => kept.all fun r => !clobbers i r) = true := by
  cases wide <;>
  simp [Code.allInstrs_eq, instrs, convert, test, long, short, shiftBytes, zeroBytes,
    Impl.Rc2.AArch64.Stream.copy, Impl.Rc2.AArch64.Stream.copyBody, List.all_flatMap, clobbers, dstOf]

/-- Nor a preserved vector register. -/
theorem convert_keepsV (wide : Bool) : (convert len wide).allInstrs keepsV = true := by
  cases wide <;>
  simp [Code.allInstrs_eq, instrs, convert, test, long, short, shiftBytes, zeroBytes,
    Impl.Rc2.AArch64.Stream.copy, Impl.Rc2.AArch64.Stream.copyBody, List.all_flatMap, keepsV, vdstOf]

/-- `convert`: the buffer's first `len` bytes are `fixedDigest` of the hash,
and only the buffer and `x9`–`x13`, `x1`, `x2` change. -/
theorem convert_ok (wide : Bool) (hp : CPre len s) : WP isa (convert len wide) s (CPost len wide s) :=
  WP.mono (WP.preservedV (WP.rdwr (WP.gprs (rs := kept) (convert_mem wide hp)
    (convert_kept wide) (by cases wide <;> rfl))) (convert_keepsV wide))
    fun _ ⟨⟨⟨hm, hk⟩, hrd, hwr, hsp⟩, hv⟩ =>
    ⟨hm.buf, hm.frame, ⟨fun r hr => hk r (kept_of_not_clob hr), hrd, hwr⟩, hsp, hv⟩

/-! ## The contracts, by register -/

variable (I : Spec.Ecdsa.Instance)

/-- The regions of `hashed`'s arguments. -/
structure IPre (st : Nat) (s : State) : Prop where
  stk : st = 0 ∨ st ≤ s.sp.toNat
  rd : s.rd = [⟨s.gpr .x0, 2 * I.curve.len + 1⟩, ⟨s.gpr .x1, (s.gpr .x2).toNat⟩, ⟨s.gpr .x3, 2 * I.curve.len⟩]
  wr : s.wr = [⟨s.gpr .x4, Spec.Ecdsa.scratchWords * 8⟩, ⟨s.gpr .x5, 80⟩]
  d04 : (⟨s.gpr .x0, 2 * I.curve.len + 1⟩ : Region).Disjoint ⟨s.gpr .x4, Spec.Ecdsa.scratchWords * 8⟩
  d05 : (⟨s.gpr .x0, 2 * I.curve.len + 1⟩ : Region).Disjoint ⟨s.gpr .x5, 80⟩
  d14 : (⟨s.gpr .x1, (s.gpr .x2).toNat⟩ : Region).Disjoint ⟨s.gpr .x4, Spec.Ecdsa.scratchWords * 8⟩
  d15 : (⟨s.gpr .x1, (s.gpr .x2).toNat⟩ : Region).Disjoint ⟨s.gpr .x5, 80⟩
  d34 : (⟨s.gpr .x3, 2 * I.curve.len⟩ : Region).Disjoint ⟨s.gpr .x4, Spec.Ecdsa.scratchWords * 8⟩
  d35 : (⟨s.gpr .x3, 2 * I.curve.len⟩ : Region).Disjoint ⟨s.gpr .x5, 80⟩
  d45 : (⟨s.gpr .x4, Spec.Ecdsa.scratchWords * 8⟩ : Region).Disjoint ⟨s.gpr .x5, 80⟩
  below : ∀ r ∈ stackBelow s.sp st,
    r.Disjoint ⟨s.gpr .x0, 2 * I.curve.len + 1⟩ ∧ r.Disjoint ⟨s.gpr .x1, (s.gpr .x2).toNat⟩ ∧
      r.Disjoint ⟨s.gpr .x3, 2 * I.curve.len⟩ ∧ r.Disjoint ⟨s.gpr .x4, Spec.Ecdsa.scratchWords * 8⟩ ∧
      r.Disjoint ⟨s.gpr .x5, 80⟩
  f0 : (s.gpr .x0).toNat + (2 * I.curve.len + 1) ≤ 2 ^ 64
  f1 : (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64
  f3 : (s.gpr .x3).toNat + 2 * I.curve.len ≤ 2 ^ 64
  f4 : (s.gpr .x4).toNat + Spec.Ecdsa.scratchWords * 8 ≤ 2 ^ 64
  f5 : (s.gpr .x5).toNat + 80 ≤ 2 ^ 64

/-- `verifyHashContract`'s postcondition. -/
abbrev hPost : I.verifyHashSig.Post abi.ptrBits := fun pk digest digestLen sig _scratch m _m' r =>
  r = if Spec.Ecdsa.verify I.curve (Spec.Ecdsa.bytesAt m pk (2 * I.curve.len + 1))
      (Spec.Ecdsa.hashToInt I.curve (Spec.Ecdsa.bytesAt m digest digestLen.toNat))
      (Spec.Ecdsa.bytesAt m sig (2 * I.curve.len))
    then 1 else 0

/-- `verifyHashContract`'s leak. -/
abbrev hLeak : Curry (I.verifyHashSig.words abi.ptrBits) (Mem → List Nat) :=
  fun pk digest digestLen sig _scratch m =>
    (Spec.Ecdsa.bytesAt m pk (2 * I.curve.len + 1) ++ Spec.Ecdsa.bytesAt m digest digestLen.toNat ++
      Spec.Ecdsa.bytesAt m sig (2 * I.curve.len)).map (·.toNat)

/-- What the verification that takes the `len` bytes needs, by register:
`public` in `x0`, the bytes in `x1`, `sig` in `x2`, `scratch` in `x3`. -/
structure KPre (st : Nat) (s : State) : Prop where
  stk : st = 0 ∨ st ≤ s.sp.toNat
  rd : s.rd = [⟨s.gpr .x0, 2 * I.curve.len + 1⟩, ⟨s.gpr .x1, I.curve.len⟩, ⟨s.gpr .x2, 2 * I.curve.len⟩]
  wr : s.wr = [⟨s.gpr .x3, Spec.Ecdsa.scratchWords * 8⟩]
  d03 : (⟨s.gpr .x0, 2 * I.curve.len + 1⟩ : Region).Disjoint ⟨s.gpr .x3, Spec.Ecdsa.scratchWords * 8⟩
  d13 : (⟨s.gpr .x1, I.curve.len⟩ : Region).Disjoint ⟨s.gpr .x3, Spec.Ecdsa.scratchWords * 8⟩
  d23 : (⟨s.gpr .x2, 2 * I.curve.len⟩ : Region).Disjoint ⟨s.gpr .x3, Spec.Ecdsa.scratchWords * 8⟩
  below : ∀ r ∈ stackBelow s.sp st,
    r.Disjoint ⟨s.gpr .x0, 2 * I.curve.len + 1⟩ ∧ r.Disjoint ⟨s.gpr .x1, I.curve.len⟩ ∧
      r.Disjoint ⟨s.gpr .x2, 2 * I.curve.len⟩ ∧ r.Disjoint ⟨s.gpr .x3, Spec.Ecdsa.scratchWords * 8⟩
  f0 : (s.gpr .x0).toNat + (2 * I.curve.len + 1) ≤ 2 ^ 64
  f1 : (s.gpr .x1).toNat + I.curve.len ≤ 2 ^ 64
  f2 : (s.gpr .x2).toNat + 2 * I.curve.len ≤ 2 ^ 64
  f3 : (s.gpr .x3).toNat + Spec.Ecdsa.scratchWords * 8 ≤ 2 ^ 64

/-- The key's bytes, at `x0`. -/
abbrev pkB (s : State) : List Byte := Spec.Ecdsa.bytesAt s.mem (s.gpr .x0) (2 * I.curve.len + 1)

/-- The verification, of the bytes at `pk`, `e` and `sg`, as the function returns it. -/
abbrev vres (m : Mem) (pk : Addr) (e : Nat) (sg : Addr) : BitVec 32 :=
  if Spec.Ecdsa.verify I.curve (Spec.Ecdsa.bytesAt m pk (2 * I.curve.len + 1)) e
    (Spec.Ecdsa.bytesAt m sg (2 * I.curve.len)) then 1 else 0

/-- `hashed`'s contract, by register, with the tables `K`. -/
def hashR (K : List (String × List (BitVec 64))) (st : Nat) : Contract isa where
  pre s := IPre I st (stripConsts K s) ∧ ConstsOk K st s
  post s s' := (s'.gpr .x0).setWidth 32 =
    vres I s.mem (s.gpr .x0) (Spec.Ecdsa.hashToInt I.curve (hashOf s)) (s.gpr .x3)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧
    s₁.gpr .x5 = s₂.gpr .x5 ∧
    (pkB I s₁ ++ hashOf s₁ ++ Spec.Ecdsa.bytesAt s₁.mem (s₁.gpr .x3) (2 * I.curve.len)).map (·.toNat) =
      (pkB I s₂ ++ hashOf s₂ ++ Spec.Ecdsa.bytesAt s₂.mem (s₂.gpr .x3) (2 * I.curve.len)).map (·.toNat) ∧
    ∀ c ∈ K, s₁.syms c.1 = s₂.syms c.1

/-- The contract of the verification that takes the `len` bytes, by register. -/
def coreR (K : List (String × List (BitVec 64))) (st : Nat) : Contract isa where
  pre s := KPre I st (stripConsts K s) ∧ ConstsOk K st s
  post s s' := (s'.gpr .x0).setWidth 32 =
    vres I s.mem (s.gpr .x0)
      (Spec.Ecdsa.hashToInt I.curve (Spec.Ecdsa.bytesAt s.mem (s.gpr .x1) I.curve.len)) (s.gpr .x2)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧
    (pkB I s₁ ++ Spec.Ecdsa.bytesAt s₁.mem (s₁.gpr .x1) I.curve.len ++
        Spec.Ecdsa.bytesAt s₁.mem (s₁.gpr .x2) (2 * I.curve.len)).map (·.toNat) =
      (pkB I s₂ ++ Spec.Ecdsa.bytesAt s₂.mem (s₂.gpr .x1) I.curve.len ++
        Spec.Ecdsa.bytesAt s₂.mem (s₂.gpr .x2) (2 * I.curve.len)).map (·.toNat) ∧
    ∀ c ∈ K, s₁.syms c.1 = s₂.syms c.1

/-! ## Running the verification on the bytes -/

/-- Verified code run from `s` with narrower permissions: its run from `s`. -/
theorem WP.narrowRun {c : Prog isa} {P : State → Prop} {Q : State → State → Prop}
    (hv : ∀ s, P s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ Q s s') {s : State}
    {rd wr : List Region} (hpre : P (s.withRegions rd wr)) (hc : Covers (rd ++ wr) (s.rd ++ s.wr))
    (hw : Covers wr s.wr) :
    WP isa c s fun s' => abiPreserved s s' ∧ Q (s.withRegions rd wr) (s'.withRegions rd wr) := by
  obtain ⟨t, s₁, he, ha, hq⟩ := hv _ hpre
  obtain ⟨hr, hwr, -⟩ := Exec.rdwr he
  simp only [State.withRegions_rd, State.withRegions_wr] at hr hwr
  have he' := Exec.widen he (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
  simp only [State.withRegions_withRegions, State.withRegions_self] at he'
  have e : (s₁.withRegions s.rd s.wr).withRegions rd wr = s₁ := by
    rw [State.withRegions_withRegions, ← hr, ← hwr]; rfl
  exact ⟨t, _, he', ⟨ha.1, ha.2.1, ha.2.2⟩, by rw [e]; exact hq⟩

theorem length_constRegs (K : List (String × List (BitVec 64))) (s : State) :
    (constRegs K s).length = K.length := by simp [constRegs, Abi.constRegions]

theorem covers_self {r : Region} {rs : List Region} (h : r ∈ rs) :
    ∃ r' ∈ rs, ∃ off, r.base = r'.base + BitVec.ofNat 64 off ∧ off + r.len ≤ r'.len :=
  ⟨r, h, 0, by simp, by omega⟩

/-- The state after `convert` (`u`) and the moves of the arguments (`v`). -/
structure VFacts (s u v : State) : Prop where
  x0 : v.gpr .x0 = s.gpr .x0
  x1 : v.gpr .x1 = s.gpr .x5
  x2 : v.gpr .x2 = s.gpr .x3
  x3 : v.gpr .x3 = s.gpr .x4
  mem : v.mem = u.mem
  rd : v.rd = s.rd
  wr : v.wr = s.wr
  sp : v.sp = s.sp
  pres : ∀ r ∈ preserved, v.gpr r = s.gpr r
  vpres : ∀ r ∈ preservedV, (v.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  syms : v.syms = s.syms

/-- The verification's readable regions: the key, the `len` bytes, the
signature, and the tables. -/
abbrev rdV (K : List (String × List (BitVec 64))) (s : State) : List Region :=
  [⟨s.gpr .x0, 2 * I.curve.len + 1⟩, ⟨s.gpr .x5, I.curve.len⟩, ⟨s.gpr .x3, 2 * I.curve.len⟩] ++ constRegs K s

/-- Its writable region: `scratch`. -/
abbrev wrV (s : State) : List Region := [⟨s.gpr .x4, Spec.Ecdsa.scratchWords * 8⟩]

section
variable {I} {wide : Bool} {K : List (String × List (BitVec 64))} {st : Nat}

theorem hs_rd {s : State} (hs : (hashR I K st).pre s) :
    s.rd = [⟨s.gpr .x0, 2 * I.curve.len + 1⟩, ⟨s.gpr .x1, (s.gpr .x2).toNat⟩,
      ⟨s.gpr .x3, 2 * I.curve.len⟩] ++ constRegs K s := by
  have e := hs.1.rd
  simp only [stripConsts, State.withRegions_rd, State.withRegions_gpr] at e
  rw [← List.take_append_drop (s.rd.length - K.length) s.rd, e, hs.2.1]

theorem cpre_of (hL : 8 * I.curve.len = Spec.Ecdsa.nBits I.curve + if wide then 7 else 0)
    (h66 : I.curve.len ≤ 66) {s : State} (hs : (hashR I K st).pre s) : CPre I.curve.len s := by
  have hp := hs.1
  have hn := nBits_pos I.curve
  have hwr : s.wr = [⟨s.gpr .x4, Spec.Ecdsa.scratchWords * 8⟩, ⟨s.gpr .x5, 80⟩] := hp.wr
  have f5 : (s.gpr .x5).toNat + 80 ≤ 2 ^ 64 := hp.f5
  have f1 : (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64 := hp.f1
  refine ⟨by split at hL <;> omega, h66,
    fun i hi => ⟨⟨s.gpr .x1, (s.gpr .x2).toNat⟩, ?_, Offset.contains_base _ (by omega) (by omega)⟩,
    fun i hi => ⟨⟨s.gpr .x5, 80⟩, ?_, Offset.contains_base _ (by omega) (by omega)⟩, hp.d15.symm, f5, f1⟩
  · rw [hs_rd hs]; simp
  · rw [hwr]; simp

/-- The arguments' moves write no preserved vector register. -/
theorem args_keepsV : (Code.block args : Prog isa).allInstrs keepsV = true := by
  simp [Code.allInstrs_eq, instrs, args, mov, keepsV, vdstOf]

theorem args_ok {s u : State} (hu : CPost I.curve.len wide s u) (hsy : u.syms = s.syms) :
    WP isa (.block args) u (VFacts s u) := by
  refine WP.mono_syms (WP.preservedV (Q := fun v => v.gpr .x0 = s.gpr .x0 ∧ v.gpr .x1 = s.gpr .x5 ∧
      v.gpr .x2 = s.gpr .x3 ∧ v.gpr .x3 = s.gpr .x4 ∧ v.mem = u.mem ∧ v.rd = s.rd ∧ v.wr = s.wr ∧
      v.sp = s.sp ∧ (∀ r ∈ preserved, v.gpr r = s.gpr r))
    (wp_mov fun v₁ g₁ => wp_mov fun v₂ g₂ => wp_mov fun v g₃ => WP.block_nil ?_) args_keepsV) fun v ⟨hv, hvv⟩ hsv =>
      ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2.1, hv.2.2.2.2.2.1, hv.2.2.2.2.2.2.1,
        hv.2.2.2.2.2.2.2.1, hv.2.2.2.2.2.2.2.2, fun r hr => (hvv r hr).trans (hu.vpres r hr), hsv.trans hsy⟩
  have k := hu.keep
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · rw [g₃.other _ (by decide), g₂.other _ (by decide), g₁.other _ (by decide), k.gpr _ (by decide)]
  · rw [g₃.other _ (by decide), g₂.other _ (by decide), g₁.gpr, k.gpr _ (by decide)]
  · rw [g₃.other _ (by decide), g₂.gpr, g₁.other _ (by decide), k.gpr _ (by decide)]
  · rw [g₃.gpr, g₂.other _ (by decide), g₁.other _ (by decide), k.gpr _ (by decide)]
  · rw [g₃.mem, g₂.mem, g₁.mem]
  · rw [g₃.rd, g₂.rd, g₁.rd, k.rd]
  · rw [g₃.wr, g₂.wr, g₁.wr, k.wr]
  · rw [g₃.sp, g₂.sp, g₁.sp, hu.sp]
  · have h1 : r ∉ clob := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h2 : r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [g₃.other _ h2.2.2, g₂.other _ h2.2.1, g₁.other _ h2.1, k.gpr _ h1]

theorem vpre (h66 : I.curve.len ≤ 66) {s u v : State} (hs : (hashR I K st).pre s)
    (hu : CPost I.curve.len wide s u) (hv : VFacts s u v) :
    (coreR I K st).pre (v.withRegions (rdV I K s) (wrV s)) ∧
      Covers (rdV I K s ++ wrV s) (v.rd ++ v.wr) ∧ Covers (wrV s) v.wr := by
  obtain ⟨hp, hk⟩ := hs
  have hrdS := hs_rd ⟨hp, hk⟩
  have hwr : s.wr = [⟨s.gpr .x4, Spec.Ecdsa.scratchWords * 8⟩, ⟨s.gpr .x5, 80⟩] := hp.wr
  obtain ⟨va0, va1, va2, va3, vmem, vrd, vwr, vsp, -, -, hsy'⟩ := hv
  have hL80 : I.curve.len ≤ 80 := by omega
  have f0 := hp.f0
  have f3 := hp.f3
  have f4 := hp.f4
  have f5 : (s.gpr .x5).toNat + 80 ≤ 2 ^ 64 := hp.f5
  have hcR : constRegs K v = constRegs K s := by simp only [constRegs, hsy']
  let rd' : List Region := rdV I K s
  let wr' : List Region := wrV s
  have hsc : (⟨s.gpr .x4, Spec.Ecdsa.scratchWords * 8⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  have hbf : (⟨s.gpr .x5, 80⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  have hstrip : stripConsts K (v.withRegions rd' wr') =
      (v.withRegions [⟨s.gpr .x0, 2 * I.curve.len + 1⟩, ⟨s.gpr .x5, I.curve.len⟩,
        ⟨s.gpr .x3, 2 * I.curve.len⟩] wr') := by
    simp only [stripConsts, State.withRegions_rd, State.withRegions_withRegions, State.withRegions_wr, rd']
    congr 1
    rw [List.length_append, length_constRegs, List.take_left' (by simp)]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hstrip]
    have hb := hp.below
    simp only [stripConsts_sp, stripConsts_gpr] at hb
    refine ⟨by rw [State.withRegions_sp, vsp]; exact hp.stk,
      by simp only [State.withRegions_rd, State.withRegions_gpr, va0, va1, va2],
      by simp only [State.withRegions_wr, State.withRegions_gpr, va3, wr'], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [State.withRegions_gpr, va0, va3]; exact hp.d04
    · simp only [State.withRegions_gpr, va1, va3]
      exact (hp.d45.sub_right (sub_prefix _ hL80)).symm
    · simp only [State.withRegions_gpr, va2, va3]; exact hp.d34
    · intro r hr
      simp only [State.withRegions_sp, vsp] at hr
      obtain ⟨b0, -, b3, b4, b5⟩ := hb r hr
      simp only [State.withRegions_gpr, va0, va1, va2, va3]
      exact ⟨b0, b5.sub_right (sub_prefix _ hL80), b3, b4⟩
    · simp only [State.withRegions_gpr, va0]; exact f0
    · simp only [State.withRegions_gpr, va1]; omega
    · simp only [State.withRegions_gpr, va2]; exact f3
    · simp only [State.withRegions_gpr, va3]; exact f4
  · have htab : ∀ t ∈ constRegs K s, t.base.toNat + t.len ≤ 2 ^ abi.ptrBits ∧ (∀ r ∈ s.wr, t.Disjoint r) ∧
        ∀ r ∈ abi.reserved st s, t.Disjoint r := hk.2.2.1
    refine ⟨?_, ?_, ?_, ?_⟩
    · show (rd'.drop (rd'.length - K.length)) = constRegs K v
      rw [hcR]
      simp only [rd', List.length_append, length_constRegs, List.length_cons, List.length_nil]
      rw [show 0 + 1 + 1 + 1 + K.length - K.length = 3 by omega, List.drop_left' (by simp)]
    · intro c hc i hi
      show v.mem.readW (v.syms c.1 + BitVec.ofNat 64 (8 * i)) 64 = c.2.getD i 0
      have ht : (⟨s.syms c.1, 8 * c.2.length⟩ : Region) ∈ constRegs K s :=
        List.mem_map_of_mem (f := fun c => (⟨s.syms c.1, 8 * c.2.length⟩ : Region)) hc
      have hfit : (s.syms c.1).toNat + 8 * c.2.length ≤ 2 ^ 64 := (htab _ ht).1
      rw [hsy', vmem, Frame.readW hu.frame (r := ⟨s.syms c.1, 8 * c.2.length⟩)
        (Offset.contains_base _ (by omega) (by omega))
        (fun r' hr' => by
          simp only [List.mem_singleton] at hr'; subst hr'
          exact (htab _ ht).2.1 _ hbf) (by decide)]
      exact hk.2.1 c hc i hi
    · intro t ht
      rw [show constRegs K (v.withRegions rd' wr') = constRegs K s from hcR] at ht
      obtain ⟨a, b, c⟩ := htab t ht
      refine ⟨a, fun r hr => b r ?_, fun r hr => c r ?_⟩
      · simp only [State.withRegions_wr, List.mem_singleton] at hr; subst hr; exact hsc
      · simpa [abi, State.withRegions_sp, vsp] using hr
    · intro t ht
      rw [show constRegs K (v.withRegions rd' wr') = constRegs K s from hcR] at ht
      exact hk.2.2.2 t ht
  · refine Covers.of_sub fun r hr => ?_
    rw [vrd, vwr]
    simp only [rdV, wrV, List.cons_append, List.nil_append, List.mem_cons, List.mem_append] at hr
    rcases hr with rfl | rfl | rfl | hr | hr
    · exact covers_self (by rw [hrdS]; simp)
    · exact ⟨_, List.mem_append_right _ hbf, 0, by simp, by simp; omega⟩
    · exact covers_self (by rw [hrdS]; simp)
    · exact covers_self (by rw [hrdS]; simp [hr])
    · simp only [List.not_mem_nil, or_false] at hr; subst hr
      exact covers_self (List.mem_append_right _ hsc)
  · refine Covers.of_sub fun r hr => ?_
    simp only [wrV, List.mem_singleton] at hr; subst hr
    rw [vwr]; exact covers_self hsc

theorem vpost {s u v : State}
    (hs : (hashR I K st).pre s) (hu : CPost I.curve.len wide s u) (hv : VFacts s u v) :
    Spec.Ecdsa.bytesAt v.mem (s.gpr .x5) I.curve.len = fixedDigest I.curve.len wide (hashOf s) ∧
      Spec.Ecdsa.bytesAt v.mem (s.gpr .x0) (2 * I.curve.len + 1) =
        Spec.Ecdsa.bytesAt s.mem (s.gpr .x0) (2 * I.curve.len + 1) ∧
      Spec.Ecdsa.bytesAt v.mem (s.gpr .x3) (2 * I.curve.len) =
        Spec.Ecdsa.bytesAt s.mem (s.gpr .x3) (2 * I.curve.len) := by
  have hp := hs.1
  have f0 := hp.f0
  have f3 := hp.f3
  refine ⟨bytesAt_ext (length_fixedDigest _ _ _) fun i hi => by rw [hv.mem]; exact hu.buf i hi, ?_, ?_⟩
  · rw [hv.mem]; exact bytesAt_frame hu.frame hp.d05 (by omega)
  · rw [hv.mem]; exact bytesAt_frame hu.frame hp.d35 (by omega)

end

theorem hashed_correct {wide : Bool} {K : List (String × List (BitVec 64))} {st : Nat} {core : Prog isa}
    (hL : 8 * I.curve.len = Spec.Ecdsa.nBits I.curve + if wide then 7 else 0) (h66 : I.curve.len ≤ 66)
    (hcv : ∀ s, (coreR I K st).pre s →
      ∃ t s', Exec isa core s t s' ∧ abiPreserved s s' ∧ (coreR I K st).post s s')
    (s : State) (hs : (hashR I K st).pre s) :
    ∃ t s', Exec isa (hashed I.curve.len wide core) s t s' ∧ abiPreserved s s' ∧ (hashR I K st).post s s' := by
  have hW : WP isa (hashed I.curve.len wide core) s fun s' => abiPreserved s s' ∧ (hashR I K st).post s s' := by
    unfold hashed
    refine WP.seq (WP.mono_syms (convert_ok wide (cpre_of hL h66 hs)) fun u hu hsy => ?_)
    refine WP.seq (WP.mono (args_ok hu hsy) fun v hv => ?_)
    obtain ⟨hpre, hc, hw⟩ := vpre h66 hs hu hv
    refine WP.mono (WP.narrowRun hcv hpre hc hw) fun s' ⟨habi, hpost⟩ =>
      ⟨⟨fun r hr => (habi.1 r hr).trans (hv.pres r hr), habi.2.1.trans hv.sp,
        fun r hr => (habi.2.2 r hr).trans (hv.vpres r hr)⟩, ?_⟩
    obtain ⟨e1, e2, e3⟩ := vpost hs hu hv
    have hq : (s'.gpr .x0).setWidth 32 = vres I v.mem (s.gpr .x0)
        (Spec.Ecdsa.hashToInt I.curve (Spec.Ecdsa.bytesAt v.mem (s.gpr .x5) I.curve.len)) (s.gpr .x3) := by
      have := hpost
      simp only [coreR, State.withRegions_gpr, State.withRegions_mem, hv.x0, hv.x1, hv.x2] at this
      exact this
    show (s'.gpr .x0).setWidth 32 = vres I s.mem (s.gpr .x0) (Spec.Ecdsa.hashToInt I.curve (hashOf s)) (s.gpr .x3)
    rw [hq, e1, hashToInt_fixedDigest hL]
    simp only [vres, e2, e3]
  obtain ⟨t, s', he, ha, hq⟩ := hW
  exact ⟨t, s', he, ha, hq⟩

/-! ## Constant time -/

/-- Inlined verified code: two runs, from states that narrow to ones its
contract relates, leak the same. -/
theorem RelCT.inlineV {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      k.pre (s₁.withRegions rd₁ wr₁) ∧ k.pre (s₂.withRegions rd₂ wr₂) ∧
      k.pub (s₁.withRegions rd₁ wr₁) (s₂.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (s₁.rd ++ s₁.wr) ∧ Covers wr₁ s₁.wr ∧
      Covers (rd₂ ++ wr₂) (s₂.rd ++ s₂.wr) ∧ Covers wr₂ s₂.wr) :
    RelCT isa P c fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨rd₁, wr₁, rd₂, wr₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂⟩ := hP _ _ hp
  obtain ⟨_, n₁⟩ := trace_narrow hv p₁ c₁ w₁ e₁
  obtain ⟨_, n₂⟩ := trace_narrow hv p₂ c₂ w₂ e₂
  exact ⟨hct _ _ _ _ _ _ p₁ p₂ hpub n₁ n₂, trivial⟩

/-- The arguments' moves leak nothing. -/
theorem args_taint : (taint.check (Taint.ofRegs [.x0, .x3, .x4, .x5]) (.block args)
    (.block [] 256)).isSome = true := by
  decide

section
variable {I} {wide : Bool} {K : List (String × List (BitVec 64))} {st : Nat}

/-- Two runs as `hashR` relates them. -/
abbrev HP (s₁ s₂ : State) : Prop := (hashR I K st).pre s₁ ∧ (hashR I K st).pre s₂ ∧ (hashR I K st).pub s₁ s₂

theorem hashed_ct {core : Prog isa}
    (hL : 8 * I.curve.len = Spec.Ecdsa.nBits I.curve + if wide then 7 else 0) (h66 : I.curve.len ≤ 66)
    (hcv : ∀ s, (coreR I K st).pre s →
      ∃ t s', Exec isa core s t s' ∧ abiPreserved s s' ∧ (coreR I K st).post s s')
    (hct : ConstantTime isa (coreR I K st).pre (coreR I K st).pub core) {hc : Taint.Hint taint.T}
    (htc : (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5]) (convert I.curve.len wide) hc).isSome = true) :
    ConstantTime isa (hashR I K st).pre (hashR I K st).pub (hashed I.curve.len wide core) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold hashed
  refine RelCT.seq (R := fun u₁ u₂ => ∃ σ₁ σ₂ x₁ x₂ : State, u₁ = x₁ ∧ u₂ = x₂ ∧ HP (I := I) (K := K) (st := st) σ₁ σ₂ ∧
      (CPost I.curve.len wide σ₁ x₁ ∧ x₁.syms = σ₁.syms) ∧ (CPost I.curve.len wide σ₂ x₂ ∧ x₂.syms = σ₂.syms))
    ?_ (RelCT.seq (R := fun v₁ v₂ => ∃ σ₁ σ₂ x₁ x₂ : State, HP (I := I) (K := K) (st := st) σ₁ σ₂ ∧
      CPost I.curve.len wide σ₁ x₁ ∧ VFacts σ₁ x₁ v₁ ∧ CPost I.curve.len wide σ₂ x₂ ∧ VFacts σ₂ x₂ v₂) ?_ ?_)
  · refine ((RelCT.taint (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5]) (fun s₁ s₂ h => ?_) htc).wpDep
      (F := fun (s t : State) => CPost I.curve.len wide s t ∧ t.syms = s.syms) fun s₁ s₂ h =>
        ⟨WP.mono_syms (convert_ok wide (cpre_of hL h66 h.1)) fun _ a sy => ⟨a, sy⟩,
          WP.mono_syms (convert_ok wide (cpre_of hL h66 h.2.1)) fun _ a sy => ⟨a, sy⟩⟩).mono (fun _ _ h => h)
      fun t₁ t₂ ⟨_, σ₁, σ₂, hp, a₁, a₂⟩ => ⟨σ₁, σ₂, t₁, t₂, rfl, rfl, hp, a₁, a₂⟩
    obtain ⟨-, -, psp, p0, p1, p2, p3, p4, p5, -⟩ := h
    refine ⟨psp, fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  · refine RelCT.exists_ fun σ₁ => RelCT.exists_ fun σ₂ => RelCT.exists_ fun x₁ => RelCT.exists_ fun x₂ => ?_
    refine ((RelCT.taint (A := taint) (Taint.ofRegs [.x0, .x3, .x4, .x5]) (fun s₁ s₂ h => ?_) args_taint).wp
      (F₁ := fun v => (HP (I := I) (K := K) (st := st) σ₁ σ₂ ∧ CPost I.curve.len wide σ₁ x₁ ∧
        CPost I.curve.len wide σ₂ x₂) ∧ VFacts σ₁ x₁ v) (F₂ := VFacts σ₂ x₂)
      fun u₁ u₂ ⟨e₁, e₂, hp, ⟨c₁, y₁⟩, ⟨c₂, y₂⟩⟩ => by
        subst e₁ e₂; exact ⟨WP.mono (args_ok c₁ y₁) fun _ h => ⟨⟨hp, c₁, c₂⟩, h⟩, args_ok c₂ y₂⟩).mono
      (fun _ _ h => h) fun v₁ v₂ ⟨_, ⟨⟨hp, c₁, c₂⟩, f₁⟩, f₂⟩ => ⟨σ₁, σ₂, x₁, x₂, hp, c₁, f₁, c₂, f₂⟩
    obtain ⟨e₁, e₂, ⟨-, -, psp, p0, -, -, p3, p4, p5, -⟩, ⟨c₁, -⟩, ⟨c₂, -⟩⟩ := h
    subst e₁ e₂
    have k₁ := c₁.keep
    have k₂ := c₂.keep
    refine ⟨by rw [c₁.sp, c₂.sp, psp], fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [k₁.gpr _ (by decide), k₂.gpr _ (by decide), p0]
    · rw [k₁.gpr _ (by decide), k₂.gpr _ (by decide), p3]
    · rw [k₁.gpr _ (by decide), k₂.gpr _ (by decide), p4]
    · rw [k₁.gpr _ (by decide), k₂.gpr _ (by decide), p5]
  · refine RelCT.inlineV hcv hct fun v₁ v₂ ⟨σ₁, σ₂, x₁, x₂, hp, c₁, f₁, c₂, f₂⟩ => ?_
    obtain ⟨q₁, cv₁, cw₁⟩ := vpre h66 hp.1 c₁ f₁
    obtain ⟨q₂, cv₂, cw₂⟩ := vpre h66 hp.2.1 c₂ f₂
    refine ⟨_, _, _, _, q₁, q₂, ?_, cv₁, cw₁, cv₂, cw₂⟩
    obtain ⟨psp, p0, p1, p2, p3, p4, p5, pl, psy⟩ := hp.2.2
    obtain ⟨b₁, k₁, g₁⟩ := vpost hp.1 c₁ f₁
    obtain ⟨b₂, k₂, g₂⟩ := vpost hp.2.1 c₂ f₂
    obtain ⟨ek, eh, eg⟩ := bytes_of_leak (by simp only [pkB, length_bytesAt])
      (by simp only [hashOf, length_bytesAt, p2]) pl
    refine ⟨by simp only [State.withRegions_sp, f₁.sp, f₂.sp, psp], by simp only [State.withRegions_gpr, f₁.x0, f₂.x0, p0],
      by simp only [State.withRegions_gpr, f₁.x1, f₂.x1, p5], by simp only [State.withRegions_gpr, f₁.x2, f₂.x2, p3],
      by simp only [State.withRegions_gpr, f₁.x3, f₂.x3, p4], ?_, fun c hc => ?_⟩
    · simp only [pkB, State.withRegions_mem, State.withRegions_gpr, f₁.x0, f₁.x1, f₁.x2, f₂.x0, f₂.x1, f₂.x2]
      rw [b₁, k₁, g₁, b₂, k₂, g₂]
      simp only [pkB] at ek
      rw [ek, eh, eg]
    · show v₁.syms c.1 = v₂.syms c.1
      rw [f₁.syms, f₂.syms]; exact psy c hc
end

/-! ## The contracts of `Spec/`, by register -/

section
variable {I}

theorem scratch_bytes : Spec.Ecdsa.scratchWords * 8 = 8192 := rfl

theorem stripConsts_nil (s : State) : stripConsts [] s = s := by
  simp [stripConsts, State.withRegions]

theorem constsOk_nil (st : Nat) (s : State) : ConstsOk [] st s := by
  simp [ConstsOk, constRegs, Abi.constRegions, Abi.constsHeld]

/-- The verification's precondition under `abi`, from `KPre`. -/
theorem core_pre {s : State} (h : KPre I 0 s) : (I.verifyContract abi 0).pre s := by
  sig_pre [Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig, Spec.Ecdsa.scratchWords,
    AArch64.abi, AArch64.argRegs]
  have hwr := h.wr
  rw [scratch_bytes] at hwr
  exact ⟨h.rd, hwr, h.d03, h.d13, h.d23, h.f0, h.f1, h.f2, h.f3⟩

theorem core_post {s s' : State} (h : (I.verifyContract abi 0).post s s') :
    (s'.gpr .x0).setWidth 32 = vres I s.mem (s.gpr .x0)
      (Spec.Ecdsa.hashToInt I.curve (Spec.Ecdsa.bytesAt s.mem (s.gpr .x1) I.curve.len)) (s.gpr .x2) := by
  sig_post [Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig, Spec.Ecdsa.scratchWords,
    AArch64.abi, AArch64.argRegs] at h
  exact h

theorem core_pub {s₁ s₂ : State} (h : s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧
    (pkB I s₁ ++ Spec.Ecdsa.bytesAt s₁.mem (s₁.gpr .x1) I.curve.len ++
        Spec.Ecdsa.bytesAt s₁.mem (s₁.gpr .x2) (2 * I.curve.len)).map (·.toNat) =
      (pkB I s₂ ++ Spec.Ecdsa.bytesAt s₂.mem (s₂.gpr .x1) I.curve.len ++
        Spec.Ecdsa.bytesAt s₂.mem (s₂.gpr .x2) (2 * I.curve.len)).map (·.toNat)) :
    (I.verifyContract abi 0).pub s₁ s₂ := by
  sig_pub [Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig, Spec.Ecdsa.scratchWords,
    AArch64.abi, AArch64.argRegs]
  obtain ⟨psp, p0, p1, p2, p3, pl⟩ := h
  exact ⟨psp, pl, p0, p1, p2, p3⟩

/-- The verification, run as `coreR` describes it, from its proof under `abi`. -/
theorem coreR_nil {core : Prog isa} (h : Verified target core (I.verifyContract abi 0)) :
    (∀ s, (coreR I [] 0).pre s → ∃ t s', Exec isa core s t s' ∧ abiPreserved s s' ∧ (coreR I [] 0).post s s') ∧
      ConstantTime isa (coreR I [] 0).pre (coreR I [] 0).pub core := by
  obtain ⟨hc, hct, -⟩ := h
  have hp : ∀ s, (coreR I [] 0).pre s → (I.verifyContract abi 0).pre s := fun s hs => by
    have := hs.1; rw [stripConsts_nil] at this; exact core_pre this
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_⟩
  · obtain ⟨t, s', he, ha, hq⟩ := hc s (hp s hs)
    exact ⟨t, s', he, ha, core_post hq⟩
  · obtain ⟨psp, p0, p1, p2, p3, pl, -⟩ := hpub
    exact hct _ _ _ _ _ _ (hp _ h₁) (hp _ h₂) (core_pub ⟨psp, p0, p1, p2, p3, pl⟩) e₁ e₂

/-- The same, from its proof under `abi.withConsts` of its tables. -/
theorem coreR_cons {c₀ : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}
    {core : Prog isa} (h : Verified target core (I.verifyContract (abi.withConsts (c₀ :: cs)) 0)) :
    (∀ s, (coreR I (c₀ :: cs) 0).pre s →
      ∃ t s', Exec isa core s t s' ∧ abiPreserved s s' ∧ (coreR I (c₀ :: cs) 0).post s s') ∧
      ConstantTime isa (coreR I (c₀ :: cs) 0).pre (coreR I (c₀ :: cs) 0).pub core := by
  obtain ⟨hc, hct, -⟩ := h
  have hp : ∀ s, (coreR I (c₀ :: cs) 0).pre s → (I.verifyContract (abi.withConsts (c₀ :: cs)) 0).pre s :=
    fun s hs => pre_consts.mpr ⟨core_pre hs.1, hs.2⟩
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_⟩
  · obtain ⟨t, s', he, ha, hq⟩ := hc s (hp s hs)
    exact ⟨t, s', he, ha, core_post (post_consts.mp hq)⟩
  · obtain ⟨psp, p0, p1, p2, p3, pl, psy⟩ := hpub
    exact hct _ _ _ _ _ _ (hp _ h₁) (hp _ h₂)
      (pub_consts.mpr ⟨core_pub ⟨psp, p0, p1, p2, p3, pl⟩, psy⟩)
      e₁ e₂

end

/-! ## `hashed`, under the contracts of `Spec/` -/

section
variable {I}

/-- `hashed`'s contract under `abi`, with the buffer as a last argument. -/
abbrev innerA : Contract isa :=
  Sig.scratchContract abi I.verifyHashSig "buf" .u8 80 (Curry.const (fun _ => True) _) (hPost I) true 0
    (some (hLeak I))

/-- The same under `abi.withConsts`. -/
abbrev innerK (c₀ : String × List (BitVec 64)) (cs : List (String × List (BitVec 64))) : Contract isa :=
  Sig.scratchContract (abi.withConsts (c₀ :: cs)) I.verifyHashSig "buf" .u8 80 (Curry.const (fun _ => True) _)
    (hPost I) true 0 (some (hLeak I))

theorem pre_leak {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
    {wa : Bool} {st : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {s : State} :
    (sig.contract abi pre post wa st leak).pre s ↔ (sig.contract abi pre post wa st none).pre s := Iff.rfl

theorem hashSig_words : ((I.verifyHashSig.withScratch "buf" .u8 80).words abi.ptrBits).length ≤ 8 := by
  simp [Spec.Ecdsa.Instance.verifyHashSig, Sig.withScratch, Sig.words, Param.words]

theorem inner_ipre {s : State} (h : (innerA (I := I)).pre s) : IPre I 0 s := by
  sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, hPost,
    Spec.Ecdsa.Instance.verifyHashSig, Spec.Ecdsa.scratchWords, AArch64.abi, AArch64.argRegs] at h
  obtain ⟨hrd, hwr, d04, d05, d14, d15, d34, d35, d45, f0, f1, f3, f4, f5⟩ := h
  exact ⟨.inl rfl, hrd, hwr, d04, d05, d14, d15, d34, d35, d45, by simp [stackBelow], f0, f1, f3, f4, f5⟩

theorem inner_post {s s' : State} (h : (hashR I [] 0).post s s') : (innerA (I := I)).post s s' := by
  sig_post [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, hPost,
    Spec.Ecdsa.Instance.verifyHashSig, Spec.Ecdsa.scratchWords, AArch64.abi, AArch64.argRegs]
  exact h

theorem inner_pub {K : List (String × List (BitVec 64))} {s₁ s₂ : State} (h : (innerA (I := I)).pub s₁ s₂)
    (hsy : ∀ c ∈ K, s₁.syms c.1 = s₂.syms c.1) : (hashR I K 0).pub s₁ s₂ := by
  sig_pub [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, hPost, hLeak, Option.map,
    Spec.Ecdsa.Instance.verifyHashSig, Spec.Ecdsa.scratchWords, AArch64.abi, AArch64.argRegs] at h
  obtain ⟨psp, pl, p0, p1, p2, p3, p4, p5⟩ := h
  exact ⟨psp, p0, p1, p2, p3, p4, p5, pl, hsy⟩

/-- `hashed` under `abi`. -/
theorem hashed_verified_nil {wide : Bool} {core : Prog isa}
    (hL : 8 * I.curve.len = Spec.Ecdsa.nBits I.curve + if wide then 7 else 0) (h66 : I.curve.len ≤ 66)
    (hcore : Verified target core (I.verifyContract abi 0)) {hc : Taint.Hint taint.T}
    (htc : (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5]) (convert I.curve.len wide) hc).isSome = true)
    (hsat : ∃ s, (innerA (I := I)).pre s) :
    Verified target (hashed I.curve.len wide core) (innerA (I := I)) := by
  obtain ⟨hcv, hct⟩ := coreR_nil hcore
  refine Verified.of_correct (T := target) (k := hashR I [] 0) (k' := innerA (I := I))
    (hashed_correct I hL h66 hcv) (hashed_ct hL h66 hcv hct htc)
    ⟨fun s hs => ⟨by rw [stripConsts_nil]; exact inner_ipre hs, constsOk_nil 0 s⟩,
      fun s s' _ h => inner_post h, fun s₁ s₂ _ _ h => inner_pub h fun _ h => absurd h List.not_mem_nil, hsat⟩

/-- `hashed` under `abi.withConsts` of the verification's tables. -/
theorem hashed_verified_cons {wide : Bool} {core : Prog isa} {c₀ : String × List (BitVec 64)}
    {cs : List (String × List (BitVec 64))}
    (hL : 8 * I.curve.len = Spec.Ecdsa.nBits I.curve + if wide then 7 else 0) (h66 : I.curve.len ≤ 66)
    (hcore : Verified target core (I.verifyContract (abi.withConsts (c₀ :: cs)) 0)) {hc : Taint.Hint taint.T}
    (htc : (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5]) (convert I.curve.len wide) hc).isSome = true)
    (hsat : ∃ s, (innerK (I := I) c₀ cs).pre s) :
    Verified target (hashed I.curve.len wide core) (innerK (I := I) c₀ cs) := by
  obtain ⟨hcv, hct⟩ := coreR_cons hcore
  refine Verified.of_correct (T := target) (k := hashR I (c₀ :: cs) 0) (k' := innerK (I := I) c₀ cs)
    (hashed_correct I hL h66 hcv) (hashed_ct hL h66 hcv hct htc) ⟨fun s hs => ?_,
      fun s s' _ h => post_consts.mpr (inner_post h), fun s₁ s₂ _ _ h => ?_, hsat⟩
  · obtain ⟨h₁, h₂⟩ := pre_consts.mp hs
    exact ⟨inner_ipre h₁, h₂⟩
  · obtain ⟨h₁, h₂⟩ := pub_consts.mp h
    exact inner_pub h₁ h₂

/-- `vg_ecdsa_<curve>_verify` under `abi`, from the verification of the `len` bytes. -/
theorem verifyHash_verified_nil {wide : Bool} {core : Prog isa}
    (hL : 8 * I.curve.len = Spec.Ecdsa.nBits I.curve + if wide then 7 else 0) (h66 : I.curve.len ≤ 66)
    (hcore : Verified target core (I.verifyContract abi 0)) {hc : Taint.Hint taint.T}
    (htc : (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5]) (convert I.curve.len wide) hc).isSome = true)
    (hsat : ∃ s, (I.verifyHashContract abi 80).pre s) :
    Verified target (verifyHash I.curve.len wide core) (I.verifyHashContract abi 80) := by
  obtain ⟨s₀, h₀⟩ := hsat
  have hk : (I.verifyHashSig.words abi.ptrBits).length < 8 := by
    simp [Spec.Ecdsa.Instance.verifyHashSig, Sig.words, Param.words]
  have hb : 0 < 80 ∧ 80 < 4096 ∧ 80 % 16 = 0 ∧ 80 * Elem.u8.size ≤ 80 := by decide
  exact Verified.stackScratch (sig := I.verifyHashSig) (nm := "buf") (e := .u8) (n := 80)
    (pre := Curry.const (fun _ => True) _) (post := hPost I) (wa := true) (stack := 0) (bytes := 80)
    (hashed_verified_nil hL h66 hcore htc ⟨_, narrow_pre (nm := "buf") hk hb h₀⟩) hk hb ⟨s₀, h₀⟩

/-- `vg_ecdsa_<curve>_verify` under `abi.withConsts`, from the verification of the `len` bytes. -/
theorem verifyHash_verified_cons {wide : Bool} {core : Prog isa} {c₀ : String × List (BitVec 64)}
    {cs : List (String × List (BitVec 64))}
    (hL : 8 * I.curve.len = Spec.Ecdsa.nBits I.curve + if wide then 7 else 0) (h66 : I.curve.len ≤ 66)
    (hcore : Verified target core (I.verifyContract (abi.withConsts (c₀ :: cs)) 0)) {hc : Taint.Hint taint.T}
    (htc : (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5]) (convert I.curve.len wide) hc).isSome = true)
    (hsat : ∃ s, (I.verifyHashContract (abi.withConsts (c₀ :: cs)) 80).pre s) :
    Verified target (verifyHash I.curve.len wide core) (I.verifyHashContract (abi.withConsts (c₀ :: cs)) 80) := by
  obtain ⟨s₀, h₀⟩ := hsat
  have hk : (I.verifyHashSig.words abi.ptrBits).length < 8 := by
    simp [Spec.Ecdsa.Instance.verifyHashSig, Sig.words, Param.words]
  have hb : 0 < 80 ∧ 80 < 4096 ∧ 80 % 16 = 0 ∧ 80 * Elem.u8.size ≤ 80 := by decide
  exact Verified.stackScratchC (sig := I.verifyHashSig) (nm := "buf") (e := .u8) (n := 80)
    (pre := Curry.const (fun _ => True) _) (post := hPost I) (wa := true) (stack := 0) (bytes := 80)
    (hashed_verified_cons hL h66 hcore htc ⟨_, narrowK_pre (nm := "buf") (post := hPost I) hk hb h₀⟩) hk hb
    ⟨s₀, h₀⟩

end

/-! ## Satisfiability -/

section
variable {I}

/-- `s₀`, for the verification of the `len` bytes, with `len` in `x2`, `sig`
in `x3` and `scratch` in `x4`: the hash is the `len` bytes. -/
def hashSatState (L : Nat) (s₀ : State) : State :=
  { s₀ with gpr := fun r => match r with
      | .x2 => BitVec.ofNat 64 L | .x3 => s₀.gpr .x2 | .x4 => s₀.gpr .x3 | r => s₀.gpr r }

theorem hashSat_abi (h66 : I.curve.len ≤ 66) {s₀ : State} (h₀ : (I.verifyContract abi 0).pre s₀)
    (hsp : 80 ≤ s₀.sp.toNat) (hd : ∀ r ∈ s₀.rd ++ s₀.wr, (⟨s₀.sp - 80#64, 80⟩ : Region).Disjoint r) :
    (I.verifyHashContract abi 80).pre (hashSatState I.curve.len s₀) := by
  sig_pre [Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig, Spec.Ecdsa.scratchWords,
    AArch64.abi, AArch64.argRegs] at h₀
  obtain ⟨hrd, hwr, d0, d1, d2, f0, f1, f2, f3⟩ := h₀
  sig_pre [Spec.Ecdsa.Instance.verifyHashContract, Spec.Ecdsa.Instance.verifyHashSig, Spec.Ecdsa.scratchWords,
    AArch64.abi, AArch64.argRegs, stackBelow]
  have hL : (BitVec.ofNat 64 I.curve.len).toNat = I.curve.len := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  simp only [hL]
  rw [hrd, hwr] at hd
  refine ⟨hsp, hrd, hwr, d0, d1, d2, hd _ (by simp), hd _ (by simp), hd _ (by simp), hd _ (by simp),
    f0, f1, f2, f3⟩

/-- A state satisfying `verifyHashContract`'s precondition under `abi`, from one of
the verification's whose 80 bytes below the stack pointer are free. -/
theorem hashSat_nil (h66 : I.curve.len ≤ 66) {s₀ : State} (h₀ : (I.verifyContract abi 0).pre s₀)
    (hsp : 80 ≤ s₀.sp.toNat) (hd : ∀ r ∈ s₀.rd ++ s₀.wr, (⟨s₀.sp - 80#64, 80⟩ : Region).Disjoint r) :
    ∃ s, (I.verifyHashContract abi 80).pre s :=
  ⟨_, hashSat_abi h66 h₀ hsp hd⟩

/-- The same under `abi.withConsts`. -/
theorem hashSat_cons {c₀ : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}
    (h66 : I.curve.len ≤ 66) {s₀ : State} (h₀ : (I.verifyContract (abi.withConsts (c₀ :: cs)) 0).pre s₀)
    (hsp : 80 ≤ s₀.sp.toNat) (hd : ∀ r ∈ s₀.rd ++ s₀.wr, (⟨s₀.sp - 80#64, 80⟩ : Region).Disjoint r) :
    ∃ s, (I.verifyHashContract (abi.withConsts (c₀ :: cs)) 80).pre s := by
  obtain ⟨h₁, hk⟩ := pre_consts.mp h₀
  refine ⟨hashSatState I.curve.len s₀, pre_consts.mpr ⟨?_, ?_⟩⟩
  · exact hashSat_abi h66 h₁ hsp fun r hr => hd r (by
      simp only [stripConsts, State.withRegions_rd, State.withRegions_wr, List.mem_append] at hr ⊢
      exact hr.imp (fun h => List.mem_of_mem_take h) id)
  · obtain ⟨k1, k2, k3, k4⟩ := hk
    refine ⟨k1, k2, fun t ht => ⟨(k3 t ht).1, (k3 t ht).2.1, fun r hr => ?_⟩, k4⟩
    have hr' : r = ⟨s₀.sp - 80#64, 80⟩ := by
      simpa [abi, stackBelow, hashSatState] using hr
    subst hr'
    have htd : t ∈ s₀.rd := by
      rw [← List.take_append_drop (s₀.rd.length - (c₀ :: cs).length) s₀.rd, k1]; exact List.mem_append_right _ ht
    exact (hd _ (List.mem_append_left _ htd)).symm

end

end VG.Proof.Ecdsa.Verify.AArch64.Hash
