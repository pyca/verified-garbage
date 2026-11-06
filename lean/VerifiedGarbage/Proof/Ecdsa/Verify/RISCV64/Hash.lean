module

public import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyHash
public import VerifiedGarbage.Proof.Ecdsa.Verify.Hash
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
public import VerifiedGarbage.Proof.Framework.RISCV64.StackScratchConsts
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Impl.Ecdsa.RISCV64.VerifyHash
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Loops
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# ECDSA verification of the hash function's output on RISC-V: the conversion

Untrusted: everything here is checked by Lean. `convert_ok`: `convert len
wide` writes `fixedDigest len wide` of the hash at `a1` (`a2` bytes) to the
first `len` bytes of the buffer at `a5`, changing only the buffer's 80 bytes
and the registers `t0`–`t2`, `a1` and `a2`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ecdsa.RISCV64.VerifyHash VG.Impl.Words.RISCV64

variable {len : Nat} {s : State}

/-- What `convert` needs of its state: the hash's bytes readable, the
buffer's 80 bytes writable and apart from them, neither wrapping around. -/
structure CPre (len : Nat) (s : State) : Prop where
  len1 : 0 < len
  len66 : len ≤ 66
  rd : ∀ i < (s.gpr .a2).toNat, InRegions (s.rd ++ s.wr) (s.gpr .a1 + BitVec.ofNat 64 i) 1
  wr : ∀ i < 80, InRegions s.wr (s.gpr .a5 + BitVec.ofNat 64 i) 1
  sep : (⟨s.gpr .a5, 80⟩ : Region).Disjoint ⟨s.gpr .a1, (s.gpr .a2).toNat⟩
  fitB : (s.gpr .a5).toNat + 80 ≤ 2 ^ 64
  fitD : (s.gpr .a1).toNat + (s.gpr .a2).toNat ≤ 2 ^ 64

/-- The hash. -/
abbrev hashOf (s : State) : List Byte := Spec.Ecdsa.bytesAt s.mem (s.gpr .a1) (s.gpr .a2).toNat

/-- What `convert` leaves. -/
structure CPost (len : Nat) (wide : Bool) (s t : State) : Prop where
  buf : ∀ i < len, t.mem (s.gpr .a5 + BitVec.ofNat 64 i) = (fixedDigest len wide (hashOf s)).getD i 0
  frame : Frame [⟨s.gpr .a5, 80⟩] s.mem t.mem
  keep : Keep [.t0, .t1, .t2, .a1, .a2] s t
  sp : t.sp = s.sp

/-! ## Bytes -/

/-! ## The cases -/

theorem hash_byte {i : Nat} (hi : i < (s.gpr .a2).toNat) :
    (hashOf s).getD i 0 = s.mem (s.gpr .a1 + BitVec.ofNat 64 i) :=
  bytesAt_getD _ _ _ _ hi

/-- A byte of the buffer is not one of the hash's. -/
theorem buf_not_hash (hp : CPre len s) {x : Addr} (hx : (⟨s.gpr .a5, 80⟩ : Region).Contains x 1) {i : Nat}
    (hi : i < (s.gpr .a2).toNat) : x ≠ s.gpr .a1 + BitVec.ofNat 64 i := by
  rintro rfl
  exact hp.sep _ hx (Offset.contains_base _ (by omega) (by omega))

/-- A hash of at least `len` bytes: its leftmost `len`. -/
theorem long_ok {len : Nat} (wide : Bool) {s s₁ : State} (hp : CPre len s)
    (hk : Keep [.t0] s s₁) (hsp : s₁.sp = s.sp) (hm : s₁.mem = s.mem)
    (hl : len ≤ (s.gpr .a2).toNat) :
    WP isa (.block (copyBytes .t1 .a1 .a5 0 0 len)) s₁ (CPost len wide s) := by
  have ha1 : s₁.gpr .a1 = s.gpr .a1 := hk.gpr (by decide)
  have ha5 : s₁.gpr .a5 = s.gpr .a5 := hk.gpr (by decide)
  have h66 := hp.len66
  refine WP.mono (Bytes.copyBytes_ok (s := s₁) (tmp := .t1) (src := .a1) (dst := .a5) (soff := 0)
    (doff := 0) (n := len) (by decide) (by decide) (by omega) (by omega) ?_ ?_ ?_) fun t ht => ?_
  · intro i hi; rw [hk.2.1, hk.2.2, ha1, Nat.zero_add]; exact hp.rd i (by omega)
  · intro i hi; rw [hk.2.2, ha5, Nat.zero_add]; exact hp.wr i (by omega)
  · intro i hi hc
    rw [ha5, ha1, Nat.zero_add, BitVec.add_zero] at hc
    exact buf_not_hash hp (contains_sub hc (by omega)) (i := i) (by omega) rfl
  · refine ⟨fun i hi => ?_, ?_, ?_, ?_⟩
    · have hc := ht.copied i hi
      simp only [ha5, ha1, Nat.zero_add, hm] at hc
      rw [hc, ← hash_byte (by omega), fixedDigest, ite_eq_left_of_eq_true _ _ (eq_true (by rw [length_bytesAt]; exact hl)),
        List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]
    · intro x hx
      rw [ht.frame x fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [ha5, BitVec.add_zero]
        intro hc; exact hx _ (List.mem_singleton_self _) (contains_sub hc (by omega)), hm]
    · refine ⟨fun r hr => ?_, by rw [ht.rd, hk.2.1], by rw [ht.wr, hk.2.2]⟩
      have h1 : r ≠ .t1 := fun e => hr (by rw [e]; simp)
      have h0 : r ∉ [Reg.t0] := fun e => hr (by simp at e; rw [e]; simp)
      rw [ht.gpr r h1, hk.gpr h0]
    · rw [ht.sp, hsp]

/-- The buffer's contents and what `convert` changes in memory. -/
structure MPost (len : Nat) (wide : Bool) (s t : State) : Prop where
  buf : ∀ i < len, t.mem (s.gpr .a5 + BitVec.ofNat 64 i) = (fixedDigest len wide (hashOf s)).getD i 0
  frame : Frame [⟨s.gpr .a5, 80⟩] s.mem t.mem

/-- The buffer holds the zeros and the hash (`tz`), in a state with the
entry's buffer pointer and permissions. -/
structure ZInv (len : Nat) (s u : State) : Prop where
  mem : ∀ j < 72, u.mem (s.gpr .a5 + BitVec.ofNat 64 j) = tz len (hashOf s) j
  frame : Frame [⟨s.gpr .a5, 80⟩] s.mem u.mem
  a5 : u.gpr .a5 = s.gpr .a5
  wr : u.wr = s.wr

/-- After `k` bytes of the shift. -/
structure SInv (len : Nat) (s : State) (k : Nat) (u : State) : Prop where
  mem : ∀ j < 72, u.mem (s.gpr .a5 + BitVec.ofNat 64 j) =
    if j < k then sh (tz len (hashOf s) j) (tz len (hashOf s) (j + 1)) else tz len (hashOf s) j
  frame : Frame [⟨s.gpr .a5, 80⟩] s.mem u.mem
  a5 : u.gpr .a5 = s.gpr .a5
  wr : u.wr = s.wr

theorem shift_ok (hp : CPre len s) (hl : (s.gpr .a2).toNat < len) {u : State} (hz : ZInv len s u) :
    WP isa (.block (shiftBytes len)) u (MPost len true s) := by
  have h66 := hp.len66
  have hB := hp.fitB
  refine WP.mono (wp_range_flatMap (M := isa) (SInv len s) (fun k u₁ hk h => ?_) len (Nat.le_refl _) u
    ⟨fun j hj => by simp only [Nat.not_lt_zero, ite_false]; exact hz.mem j hj, hz.frame, hz.a5, hz.wr⟩)
    fun t ht => ⟨fun i hi => ?_, ht.frame⟩
  · have hw : ∀ j < 80, InRegions u₁.wr (s.gpr .a5 + BitVec.ofNat 64 j) 1 := fun j hj => by
      rw [h.wr]; exact hp.wr j hj
    refine wp_lbu (a := s.gpr .a5 + BitVec.ofNat 64 k) (by omega) (by rw [h.a5])
      (inRegions_wr (hw k (by omega))) fun u₂ g₂ => ?_
    refine wp_lbu (a := s.gpr .a5 + BitVec.ofNat 64 (k + 1)) (by omega) (by rw [g₂.other _ (by decide), h.a5])
      (by rw [g₂.rd, g₂.wr]; exact inRegions_wr (hw (k + 1) (by omega))) fun u₃ g₃ => ?_
    refine wp_sll (by decide) fun u₄ g₄ => wp_srl (by decide) fun u₅ g₅ => wp_add fun u₆ g₆ => ?_
    refine wp_sb (a := s.gpr .a5 + BitVec.ofNat 64 k) (by omega)
      (by rw [g₆.other _ (by decide), g₅.other _ (by decide), g₄.other _ (by decide), g₃.other _ (by decide),
        g₂.other _ (by decide), h.a5])
      (by rw [g₆.wr, g₅.wr, g₄.wr, g₃.wr, g₂.wr]; exact hw k (by omega)) fun u₇ g₇ => WP.block_nil ?_
    have hv : (u₆.gpr .t1).setWidth 8 = sh (tz len (hashOf s) k) (tz len (hashOf s) (k + 1)) := by
      rw [g₆.gpr, g₅.other _ (by decide), g₅.gpr, g₄.gpr, g₄.other _ (by decide), g₃.gpr, g₃.other _ (by decide),
        g₂.gpr, g₂.mem, h.mem k (by omega), h.mem (k + 1) (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega)]
      exact shift_byte _ _
    have hm : u₇.mem = u₁.mem.writeW (s.gpr .a5 + BitVec.ofNat 64 k)
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
        g₃.other _ (by decide), g₂.other _ (by decide), h.a5]
    · rw [g₇.wr, g₆.wr, g₅.wr, g₄.wr, g₃.wr, g₂.wr, h.wr]
  · rw [ht.mem i (by omega), ite_eq_left hi, fixed_short (by rw [length_bytesAt]; exact hl) true hi]
    rfl


theorem tail_ok (wide : Bool) (hp : CPre len s) (hl : (s.gpr .a2).toNat < len) {u : State}
    (hz : ZInv len s u) :
    WP isa (.block (if wide then shiftBytes len else [])) u (MPost len wide s) := by
  cases wide with
  | true => exact shift_ok hp hl hz
  | false =>
    refine WP.block_nil ⟨fun i hi => ?_, hz.frame⟩
    rw [hz.mem i (by have := hp.len66; omega), fixed_short (by rw [length_bytesAt]; exact hl) false hi]
    rfl

theorem short_ok (wide : Bool) (hp : CPre len s) {s₁ : State} (hk : Keep [.t0] s s₁)
    (hm : s₁.mem = s.mem) (hl : (s.gpr .a2).toNat < len) :
    WP isa (short len wide) s₁ (MPost len wide s) := by
  have h66 := hp.len66
  have hB := hp.fitB
  have ha1 : s₁.gpr .a1 = s.gpr .a1 := hk.gpr (by decide)
  have ha2 : s₁.gpr .a2 = s.gpr .a2 := hk.gpr (by decide)
  have ha5 : s₁.gpr .a5 = s.gpr .a5 := hk.gpr (by decide)
  unfold short
  refine WP.seq (WP.block_append (WP.mono (Bytes.storeBytes_ok (s := s₁) (tmp := .t1) (dst := .a5)
    (doff := 0) (bs := List.replicate 72 0) (by decide) (fun i _ => by rw [replicate_getD]; decide) (by simp)
    (fun i hi => ?_)) fun s₂ h₂ => ?_))
  · rw [hk.2.2, ha5, Nat.zero_add]; exact hp.wr i (by simp at hi; omega)
  refine wp_addi (by omega) fun s₃ u₃ => wp_sub fun s₄ u₄ => WP.block_nil ?_
  have e1 : s₄.gpr .a1 = s.gpr .a1 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), h₂.gpr _ (by decide), ha1]
  have e2 : s₄.gpr .a2 = s.gpr .a2 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), h₂.gpr _ (by decide), ha2]
  have e5 : s₄.gpr .a5 = s.gpr .a5 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), h₂.gpr _ (by decide), ha5]
  have et2 : s₄.gpr .t2 = s.gpr .a5 + BitVec.ofNat 64 (len - (s.gpr .a2).toNat) := by
    rw [u₄.gpr, u₃.gpr, u₃.other .a2 (by decide), h₂.gpr .a5 (by decide), h₂.gpr .a2 (by decide), ha5, ha2]
    conv => lhs; rw [← ofNat_toNat64 (s.gpr .a2)]
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg, Offset.ofNat_sub_ofNat (by omega)]
  have em : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
  have ewr : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, h₂.wr, hk.2.2]
  have erd : s₄.rd = s.rd := by rw [u₄.rd, u₃.rd, h₂.rd, hk.2.1]
  have hz : ∀ j < 72, s₄.mem (s.gpr .a5 + BitVec.ofNat 64 j) = 0 := by
    intro j hj
    have := h₂.stored j (by simpa using hj)
    rw [ha5, Nat.zero_add] at this
    rw [em, this, replicate_getD]; rfl
  have hzf : Frame [⟨s.gpr .a5, 80⟩] s.mem s₄.mem := by
    intro x hx
    rw [em, h₂.frame x fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [ha5]
      intro hc; exact hx _ (List.mem_singleton_self _) (in_buf hc (by simp)), hm]
  have hdig : ∀ i < (s.gpr .a2).toNat, s₄.mem (s.gpr .a1 + BitVec.ofNat 64 i) =
      s.mem (s.gpr .a1 + BitVec.ofNat 64 i) := by
    intro i hi
    exact hzf _ fun r hr hc => by
      simp only [List.mem_singleton] at hr; subst hr
      exact buf_not_hash hp hc hi rfl
  refine WP.seq (WP.ite (s₄.gpr .a2 == 0) rfl (fun h0 => ?_) (fun h0 => ?_))
  · refine WP.block_nil (tail_ok wide hp hl ⟨fun j hj => ?_, hzf, e5, ewr⟩)
    have hd0 : (s.gpr .a2).toNat = 0 := by
      rw [← e2]; simp only [beq_iff_eq] at h0; rw [h0]; rfl
    rw [hz j hj, tz, ite_eq_right (by rw [length_bytesAt, hd0]; omega)]
  · have hd0 : (s.gpr .a2).toNat ≠ 0 := by
      intro e; rw [← e2] at e; simp only [beq_eq_false_iff_ne, ne_eq] at h0
      exact h0 (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    refine WP.mono (copyLoop_ok (tmp := .t1) (src := .a1) (dst := .t2) (cnt := .a2) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) s₄ (N := (s.gpr .a2).toNat) (by omega)
      (s.gpr .a2).isLt (by rw [e2, ofNat_toNat64]) (fun i hi => ?_) (fun i hi => ?_) ?_)
      fun t ⟨hc, hf, hkp⟩ => tail_ok wide hp hl ⟨fun j hj => ?_, ?_, ?_, ?_⟩
    · rw [erd, ewr, e1]; exact hp.rd i hi
    · rw [ewr, et2, Offset.add_add]; exact hp.wr _ (by omega)
    · intro x h1 h2
      rw [et2] at h1
      rw [e1] at h2
      exact hp.sep x (in_buf (off := len - (s.gpr .a2).toNat) (n := (s.gpr .a2).toNat)
        (by unfold Region.Contains; simp only; omega) (by omega)) (by unfold Region.Contains; simp only; omega)
    · by_cases hin : len - (s.gpr .a2).toNat ≤ j ∧ j < len
      · have e := hc (j - (len - (s.gpr .a2).toNat)) (by omega)
        rw [et2, e1, Offset.add_add, show len - (s.gpr .a2).toNat + (j - (len - (s.gpr .a2).toNat)) = j by
          omega, hdig _ (by omega)] at e
        rw [e, tz, ite_eq_left (by rw [length_bytesAt]; exact hin), length_bytesAt, hash_byte (by omega)]
      · rw [hf _ fun r hr hcon => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [et2] at hcon
          unfold Region.Contains at hcon
          simp only at hcon
          have := (Offset.lt_iff (s.gpr .a5 + BitVec.ofNat 64 j) (s.gpr .a5) (d := len - (s.gpr .a2).toNat)
            (n := (s.gpr .a2).toNat) (by omega)).mp (by omega)
          rw [Mem.sub_ofNat_toNat _ (by omega)] at this
          omega, hz j hj, tz, ite_eq_right (by rw [length_bytesAt]; exact hin)]
    · refine hzf.trans (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
      simp only [List.mem_singleton] at hr; subst hr
      rw [et2]; exact Offset.sub_base _ (by omega)
    · rw [hkp.gpr (by decide), e5]
    · rw [hkp.2.2, ewr]

theorem convert_writes (wide : Bool) : writesOnly [.t0, .t1, .t2, .a1, .a2] (convert len wide) = true := by
  cases wide <;>
  simp [writesOnly, Code.allInstrs_eq, instrs, convert, short, shiftBytes, copyBytes, storeBytes, copyLoop,
    List.all_flatMap, dstOf]

theorem convert_mem (wide : Bool) (hp : CPre len s) : WP isa (convert len wide) s (MPost len wide s) := by
  unfold convert
  refine WP.seq (wp_li (by have := hp.len66; omega) fun s₁ u₁ => WP.block_nil ?_)
  have hk : Keep [.t0] s s₁ := ⟨fun r hr => u₁.other r (by simpa using hr), u₁.rd, u₁.wr⟩
  have ha2 : s₁.gpr .a2 = s.gpr .a2 := u₁.other _ (by decide)
  have hlt : (s₁.gpr .a2 < s₁.gpr .t0) ↔ (s.gpr .a2).toNat < len := by
    rw [ha2, u₁.gpr, BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hp.len66; omega)]
  refine WP.ite (decide (s₁.gpr .a2 < s₁.gpr .t0)) rfl (fun h => short_ok wide hp hk u₁.mem ?_)
    (fun h => WP.mono (long_ok wide hp hk u₁.sp u₁.mem ?_) fun t ht => ⟨ht.buf, ht.frame⟩)
  · exact hlt.mp (of_decide_eq_true h)
  · exact Nat.le_of_not_lt fun h' => absurd (decide_eq_true (hlt.mpr h')) (by rw [h]; decide)

/-- `convert`: the buffer's first `len` bytes are `fixedDigest` of the hash,
and only the buffer and `t0`–`t2`, `a1`, `a2` change. -/
theorem convert_ok (wide : Bool) (hp : CPre len s) : WP isa (convert len wide) s (CPost len wide s) :=
  WP.mono (WP.rdwr (WP.keep [.t0, .t1, .t2, .a1, .a2] (convert_mem wide hp) (convert_writes wide)
    (by cases wide <;> rfl))) fun _ ⟨⟨hm, hk⟩, _, _, hsp⟩ => ⟨hm.buf, hm.frame, hk, hsp⟩

/-! ## The contracts, by register -/

variable (I : Spec.Ecdsa.Instance)

/-- The regions of `hashed`'s arguments. -/
structure IPre (st : Nat) (s : State) : Prop where
  spal : s.sp.toNat % 16 = 0
  stk : st = 0 ∨ st ≤ s.sp.toNat
  rd : s.rd = [⟨s.gpr .a0, 2 * I.curve.len + 1⟩, ⟨s.gpr .a1, (s.gpr .a2).toNat⟩, ⟨s.gpr .a3, 2 * I.curve.len⟩]
  wr : s.wr = [⟨s.gpr .a4, Spec.Ecdsa.scratchWords * 8⟩, ⟨s.gpr .a5, 80⟩]
  d04 : (⟨s.gpr .a0, 2 * I.curve.len + 1⟩ : Region).Disjoint ⟨s.gpr .a4, Spec.Ecdsa.scratchWords * 8⟩
  d05 : (⟨s.gpr .a0, 2 * I.curve.len + 1⟩ : Region).Disjoint ⟨s.gpr .a5, 80⟩
  d14 : (⟨s.gpr .a1, (s.gpr .a2).toNat⟩ : Region).Disjoint ⟨s.gpr .a4, Spec.Ecdsa.scratchWords * 8⟩
  d15 : (⟨s.gpr .a1, (s.gpr .a2).toNat⟩ : Region).Disjoint ⟨s.gpr .a5, 80⟩
  d34 : (⟨s.gpr .a3, 2 * I.curve.len⟩ : Region).Disjoint ⟨s.gpr .a4, Spec.Ecdsa.scratchWords * 8⟩
  d35 : (⟨s.gpr .a3, 2 * I.curve.len⟩ : Region).Disjoint ⟨s.gpr .a5, 80⟩
  d45 : (⟨s.gpr .a4, Spec.Ecdsa.scratchWords * 8⟩ : Region).Disjoint ⟨s.gpr .a5, 80⟩
  below : ∀ r ∈ stackBelow s.sp st,
    r.Disjoint ⟨s.gpr .a0, 2 * I.curve.len + 1⟩ ∧ r.Disjoint ⟨s.gpr .a1, (s.gpr .a2).toNat⟩ ∧
      r.Disjoint ⟨s.gpr .a3, 2 * I.curve.len⟩ ∧ r.Disjoint ⟨s.gpr .a4, Spec.Ecdsa.scratchWords * 8⟩ ∧
      r.Disjoint ⟨s.gpr .a5, 80⟩
  f0 : (s.gpr .a0).toNat + (2 * I.curve.len + 1) ≤ 2 ^ 64
  f1 : (s.gpr .a1).toNat + (s.gpr .a2).toNat ≤ 2 ^ 64
  f3 : (s.gpr .a3).toNat + 2 * I.curve.len ≤ 2 ^ 64
  f4 : (s.gpr .a4).toNat + Spec.Ecdsa.scratchWords * 8 ≤ 2 ^ 64
  f5 : (s.gpr .a5).toNat + 80 ≤ 2 ^ 64
  al4 : (s.gpr .a4).toNat % 8 = 0


theorem hashSig_words : ((I.verifyHashSig.withScratch "buf" .u8 80).words abi.ptrBits).length ≤ 8 := by
  simp [Spec.Ecdsa.Instance.verifyHashSig, Sig.withScratch, Sig.words, Param.words]

theorem coreSig_words : ((Proof.Ecdsa.verifySig I).words abi.ptrBits).length ≤ 8 := by
  simp [Proof.Ecdsa.verifySig, Sig.words, Param.words]

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
`public` in `a0`, the bytes in `a1`, `sig` in `a2`, `scratch` in `a3`. -/
structure KPre (st : Nat) (s : State) : Prop where
  spal : s.sp.toNat % 16 = 0
  stk : st = 0 ∨ st ≤ s.sp.toNat
  rd : s.rd = [⟨s.gpr .a0, 2 * I.curve.len + 1⟩, ⟨s.gpr .a1, I.curve.len⟩, ⟨s.gpr .a2, 2 * I.curve.len⟩]
  wr : s.wr = [⟨s.gpr .a3, Spec.Ecdsa.scratchWords * 8⟩]
  d03 : (⟨s.gpr .a0, 2 * I.curve.len + 1⟩ : Region).Disjoint ⟨s.gpr .a3, Spec.Ecdsa.scratchWords * 8⟩
  d13 : (⟨s.gpr .a1, I.curve.len⟩ : Region).Disjoint ⟨s.gpr .a3, Spec.Ecdsa.scratchWords * 8⟩
  d23 : (⟨s.gpr .a2, 2 * I.curve.len⟩ : Region).Disjoint ⟨s.gpr .a3, Spec.Ecdsa.scratchWords * 8⟩
  below : ∀ r ∈ stackBelow s.sp st,
    r.Disjoint ⟨s.gpr .a0, 2 * I.curve.len + 1⟩ ∧ r.Disjoint ⟨s.gpr .a1, I.curve.len⟩ ∧
      r.Disjoint ⟨s.gpr .a2, 2 * I.curve.len⟩ ∧ r.Disjoint ⟨s.gpr .a3, Spec.Ecdsa.scratchWords * 8⟩
  f0 : (s.gpr .a0).toNat + (2 * I.curve.len + 1) ≤ 2 ^ 64
  f1 : (s.gpr .a1).toNat + I.curve.len ≤ 2 ^ 64
  f2 : (s.gpr .a2).toNat + 2 * I.curve.len ≤ 2 ^ 64
  f3 : (s.gpr .a3).toNat + Spec.Ecdsa.scratchWords * 8 ≤ 2 ^ 64
  al3 : (s.gpr .a3).toNat % 8 = 0

/-- The key's and the signature's bytes, at `a0` and `p`. -/
abbrev pkB (s : State) : List Byte := Spec.Ecdsa.bytesAt s.mem (s.gpr .a0) (2 * I.curve.len + 1)

/-- The verification, of the bytes at `pk`, `e` and `sg`, as the function returns it. -/
abbrev vres (m : Mem) (pk : Addr) (e : Nat) (sg : Addr) : BitVec 32 :=
  if Spec.Ecdsa.verify I.curve (Spec.Ecdsa.bytesAt m pk (2 * I.curve.len + 1)) e
    (Spec.Ecdsa.bytesAt m sg (2 * I.curve.len)) then 1 else 0

/-- `hashed`'s contract, by register, with the tables `K`. -/
def hashR (K : List (String × List (BitVec 64))) (st : Nat) : Contract isa where
  pre s := IPre I st (stripConsts K s) ∧ ConstsOk K st s
  post s s' := (s'.gpr .a0).setWidth 32 =
    vres I s.mem (s.gpr .a0) (Spec.Ecdsa.hashToInt I.curve (hashOf s)) (s.gpr .a3)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧
    s₁.gpr .a5 = s₂.gpr .a5 ∧
    (pkB I s₁ ++ hashOf s₁ ++ Spec.Ecdsa.bytesAt s₁.mem (s₁.gpr .a3) (2 * I.curve.len)).map (·.toNat) =
      (pkB I s₂ ++ hashOf s₂ ++ Spec.Ecdsa.bytesAt s₂.mem (s₂.gpr .a3) (2 * I.curve.len)).map (·.toNat) ∧
    ∀ c ∈ K, s₁.syms c.1 = s₂.syms c.1

/-- The contract of the verification that takes the `len` bytes, by register. -/
def coreR (K : List (String × List (BitVec 64))) (st : Nat) : Contract isa where
  pre s := KPre I st (stripConsts K s) ∧ ConstsOk K st s
  post s s' := (s'.gpr .a0).setWidth 32 =
    vres I s.mem (s.gpr .a0)
      (Spec.Ecdsa.hashToInt I.curve (Spec.Ecdsa.bytesAt s.mem (s.gpr .a1) I.curve.len)) (s.gpr .a2)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3 ∧
    (pkB I s₁ ++ Spec.Ecdsa.bytesAt s₁.mem (s₁.gpr .a1) I.curve.len ++
        Spec.Ecdsa.bytesAt s₁.mem (s₁.gpr .a2) (2 * I.curve.len)).map (·.toNat) =
      (pkB I s₂ ++ Spec.Ecdsa.bytesAt s₂.mem (s₂.gpr .a1) I.curve.len ++
        Spec.Ecdsa.bytesAt s₂.mem (s₂.gpr .a2) (2 * I.curve.len)).map (·.toNat) ∧
    ∀ c ∈ K, s₁.syms c.1 = s₂.syms c.1

/-! ## Running the verification on the bytes -/

/-- Verified code run from `s` with narrower permissions: its run from `s`. -/
theorem WP.narrowRun {c : Prog isa} {P : State → Prop} {Q : State → State → Prop}
    (hv : ∀ s, P s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ Q s s') {s : State}
    {rd wr : List Region} (hpre : P (s.withRegions rd wr)) (hc : RISCV64.Covers (rd ++ wr) (s.rd ++ s.wr))
    (hw : RISCV64.Covers wr s.wr) :
    WP isa c s fun s' => abiPreserved s s' ∧ Q (s.withRegions rd wr) (s'.withRegions rd wr) := by
  obtain ⟨t, s₁, he, ha, hq⟩ := hv _ hpre
  obtain ⟨hr, hwr, -⟩ := Exec.rdwr he
  simp only [State.withRegions_rd, State.withRegions_wr] at hr hwr
  have he' := Exec.widen he (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
  simp only [State.withRegions_withRegions, State.withRegions_self] at he'
  have e : (s₁.withRegions s.rd s.wr).withRegions rd wr = s₁ := by
    rw [State.withRegions_withRegions, ← hr, ← hwr]; rfl
  refine ⟨t, _, he', ⟨fun r hr' => ?_, ?_, ?_⟩, by rw [e]; exact hq⟩
  · exact ha.1 r hr'
  · exact ha.2.1
  · exact ha.2.2

theorem length_constRegs (K : List (String × List (BitVec 64))) (s : State) :
    (constRegs K s).length = K.length := by simp [constRegs, Abi.constRegions]

theorem covers_self {r : Region} {rs : List Region} (h : r ∈ rs) :
    ∃ r' ∈ rs, ∃ off, r.base = r'.base + BitVec.ofNat 64 off ∧ off + r.len ≤ r'.len :=
  ⟨r, h, 0, by simp, by omega⟩

/-- The state after `convert` (`u`) and the moves of the arguments (`v`). -/
structure VFacts (s u v : State) : Prop where
  a0 : v.gpr .a0 = s.gpr .a0
  a1 : v.gpr .a1 = s.gpr .a5
  a2 : v.gpr .a2 = s.gpr .a3
  a3 : v.gpr .a3 = s.gpr .a4
  mem : v.mem = u.mem
  rd : v.rd = s.rd
  wr : v.wr = s.wr
  sp : v.sp = s.sp
  pres : ∀ r ∈ preserved, v.gpr r = s.gpr r
  ra : v.gpr .ra = s.gpr .ra
  syms : v.syms = s.syms

/-- The verification's readable regions: the key, the `len` bytes, the
signature, and the tables. -/
abbrev rdV (K : List (String × List (BitVec 64))) (s : State) : List Region :=
  [⟨s.gpr .a0, 2 * I.curve.len + 1⟩, ⟨s.gpr .a5, I.curve.len⟩, ⟨s.gpr .a3, 2 * I.curve.len⟩] ++ constRegs K s

/-- Its writable region: `scratch`. -/
abbrev wrV (s : State) : List Region := [⟨s.gpr .a4, Spec.Ecdsa.scratchWords * 8⟩]

section
variable {I} {wide : Bool} {K : List (String × List (BitVec 64))} {st : Nat}

theorem hs_rd {s : State} (hs : (hashR I K st).pre s) :
    s.rd = [⟨s.gpr .a0, 2 * I.curve.len + 1⟩, ⟨s.gpr .a1, (s.gpr .a2).toNat⟩,
      ⟨s.gpr .a3, 2 * I.curve.len⟩] ++ constRegs K s := by
  have e := hs.1.rd
  simp only [stripConsts, State.withRegions_rd, State.withRegions_gpr] at e
  rw [← List.take_append_drop (s.rd.length - K.length) s.rd, e, hs.2.1]

theorem cpre_of (hL : 8 * I.curve.len = Spec.Ecdsa.nBits I.curve + if wide then 7 else 0)
    (h66 : I.curve.len ≤ 66) {s : State} (hs : (hashR I K st).pre s) : CPre I.curve.len s := by
  have hp := hs.1
  have hn := nBits_pos I.curve
  have hwr : s.wr = [⟨s.gpr .a4, Spec.Ecdsa.scratchWords * 8⟩, ⟨s.gpr .a5, 80⟩] := hp.wr
  have f5 : (s.gpr .a5).toNat + 80 ≤ 2 ^ 64 := hp.f5
  have f1 : (s.gpr .a1).toNat + (s.gpr .a2).toNat ≤ 2 ^ 64 := hp.f1
  refine ⟨by split at hL <;> omega, h66,
    fun i hi => ⟨⟨s.gpr .a1, (s.gpr .a2).toNat⟩, ?_, Offset.contains_base _ (by omega) (by omega)⟩,
    fun i hi => ⟨⟨s.gpr .a5, 80⟩, ?_, Offset.contains_base _ (by omega) (by omega)⟩, hp.d15.symm, f5, f1⟩
  · rw [hs_rd hs]; simp
  · rw [hwr]; simp

theorem args_ok {s u : State} (hu : CPost I.curve.len wide s u) (hsy : u.syms = s.syms) :
    WP isa (.block args) u (VFacts s u) := by
  refine WP.mono_syms (Q := fun v => v.gpr .a0 = s.gpr .a0 ∧ v.gpr .a1 = s.gpr .a5 ∧
      v.gpr .a2 = s.gpr .a3 ∧ v.gpr .a3 = s.gpr .a4 ∧ v.mem = u.mem ∧ v.rd = s.rd ∧ v.wr = s.wr ∧
      v.sp = s.sp ∧ (∀ r ∈ preserved, v.gpr r = s.gpr r) ∧ v.gpr .ra = s.gpr .ra)
    (wp_mv fun v₁ g₁ => wp_mv fun v₂ g₂ => wp_mv fun v g₃ => WP.block_nil ?_) fun v hv hsv =>
      ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2.1, hv.2.2.2.2.2.1, hv.2.2.2.2.2.2.1,
        hv.2.2.2.2.2.2.2.1, hv.2.2.2.2.2.2.2.2.1, hv.2.2.2.2.2.2.2.2.2, hsv.trans hsy⟩
  · have k := hu.keep
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_⟩
    · rw [g₃.other _ (by decide), g₂.other _ (by decide), g₁.other _ (by decide), k.gpr (by decide)]
    · rw [g₃.other _ (by decide), g₂.other _ (by decide), g₁.gpr, k.gpr (by decide)]
    · rw [g₃.other _ (by decide), g₂.gpr, g₁.other _ (by decide), k.gpr (by decide)]
    · rw [g₃.gpr, g₂.other _ (by decide), g₁.other _ (by decide), k.gpr (by decide)]
    · rw [g₃.mem, g₂.mem, g₁.mem]
    · rw [g₃.rd, g₂.rd, g₁.rd, k.2.1]
    · rw [g₃.wr, g₂.wr, g₁.wr, k.2.2]
    · rw [g₃.sp, g₂.sp, g₁.sp, hu.sp]
    · have h1 : r ∉ [Reg.t0, .t1, .t2, .a1, .a2] := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have h2 : r ≠ .a1 ∧ r ≠ .a2 ∧ r ≠ .a3 := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [g₃.other _ h2.2.2, g₂.other _ h2.2.1, g₁.other _ h2.1, k.gpr h1]
    · rw [g₃.other _ (by decide), g₂.other _ (by decide), g₁.other _ (by decide), k.gpr (by decide)]

theorem vpre (h66 : I.curve.len ≤ 66) {s u v : State} (hs : (hashR I K st).pre s)
    (hu : CPost I.curve.len wide s u) (hv : VFacts s u v) :
    (coreR I K st).pre (v.withRegions (rdV I K s) (wrV s)) ∧
      RISCV64.Covers (rdV I K s ++ wrV s) (v.rd ++ v.wr) ∧ RISCV64.Covers (wrV s) v.wr := by
  obtain ⟨hp, hk⟩ := hs
  have hrdS := hs_rd ⟨hp, hk⟩
  have hwr : s.wr = [⟨s.gpr .a4, Spec.Ecdsa.scratchWords * 8⟩, ⟨s.gpr .a5, 80⟩] := hp.wr
  obtain ⟨va0, va1, va2, va3, vmem, vrd, vwr, vsp, -, -, hsy'⟩ := hv
  have hL80 : I.curve.len ≤ 80 := by omega
  have f0 := hp.f0
  have f3 := hp.f3
  have f4 := hp.f4
  have f5 : (s.gpr .a5).toNat + 80 ≤ 2 ^ 64 := hp.f5
  have hcR : constRegs K v = constRegs K s := by simp only [constRegs, hsy']
  let rd' : List Region := rdV I K s
  let wr' : List Region := wrV s
  have hsc : (⟨s.gpr .a4, Spec.Ecdsa.scratchWords * 8⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  have hbf : (⟨s.gpr .a5, 80⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  have hstrip : stripConsts K (v.withRegions rd' wr') =
      (v.withRegions [⟨s.gpr .a0, 2 * I.curve.len + 1⟩, ⟨s.gpr .a5, I.curve.len⟩,
        ⟨s.gpr .a3, 2 * I.curve.len⟩] wr') := by
    simp only [stripConsts, State.withRegions_rd, State.withRegions_withRegions, State.withRegions_wr, rd']
    congr 1
    rw [List.length_append, length_constRegs, List.take_left' (by simp)]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hstrip]
    have hb := hp.below
    simp only [stripConsts_sp, stripConsts_gpr] at hb
    refine ⟨by rw [State.withRegions_sp, vsp]; exact hp.spal, by rw [State.withRegions_sp, vsp]; exact hp.stk,
      by simp only [State.withRegions_rd, State.withRegions_gpr, va0, va1, va2],
      by simp only [State.withRegions_wr, State.withRegions_gpr, va3, wr'], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    · simp only [State.withRegions_gpr, va3]; exact hp.al4
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
  · refine RISCV64.Covers.of_sub fun r hr => ?_
    rw [vrd, vwr]
    simp only [rdV, wrV, List.cons_append, List.nil_append, List.mem_cons, List.mem_append] at hr
    rcases hr with rfl | rfl | rfl | hr | hr
    · exact covers_self (by rw [hrdS]; simp)
    · exact ⟨_, List.mem_append_right _ hbf, 0, by simp, by simp; omega⟩
    · exact covers_self (by rw [hrdS]; simp)
    · exact covers_self (by rw [hrdS]; simp [hr])
    · simp only [List.not_mem_nil, or_false] at hr; subst hr
      exact covers_self (List.mem_append_right _ hsc)
  · refine RISCV64.Covers.of_sub fun r hr => ?_
    simp only [wrV, List.mem_singleton] at hr; subst hr
    rw [vwr]; exact covers_self hsc

theorem vpost {s u v : State}
    (hs : (hashR I K st).pre s) (hu : CPost I.curve.len wide s u) (hv : VFacts s u v) :
    Spec.Ecdsa.bytesAt v.mem (s.gpr .a5) I.curve.len = fixedDigest I.curve.len wide (hashOf s) ∧
      Spec.Ecdsa.bytesAt v.mem (s.gpr .a0) (2 * I.curve.len + 1) =
        Spec.Ecdsa.bytesAt s.mem (s.gpr .a0) (2 * I.curve.len + 1) ∧
      Spec.Ecdsa.bytesAt v.mem (s.gpr .a3) (2 * I.curve.len) =
        Spec.Ecdsa.bytesAt s.mem (s.gpr .a3) (2 * I.curve.len) := by
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
      ⟨⟨fun r hr => (habi.1 r hr).trans (hv.pres r hr), habi.2.1.trans hv.sp, habi.2.2.trans hv.ra⟩, ?_⟩
    obtain ⟨e1, e2, e3⟩ := vpost hs hu hv
    have hq : (s'.gpr .a0).setWidth 32 = vres I v.mem (s.gpr .a0)
        (Spec.Ecdsa.hashToInt I.curve (Spec.Ecdsa.bytesAt v.mem (s.gpr .a5) I.curve.len)) (s.gpr .a3) := by
      have := hpost
      simp only [coreR, State.withRegions_gpr, State.withRegions_mem, hv.a0, hv.a1, hv.a2] at this
      exact this
    show (s'.gpr .a0).setWidth 32 = vres I s.mem (s.gpr .a0) (Spec.Ecdsa.hashToInt I.curve (hashOf s)) (s.gpr .a3)
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
      RISCV64.Covers (rd₁ ++ wr₁) (s₁.rd ++ s₁.wr) ∧ RISCV64.Covers wr₁ s₁.wr ∧
      RISCV64.Covers (rd₂ ++ wr₂) (s₂.rd ++ s₂.wr) ∧ RISCV64.Covers wr₂ s₂.wr) :
    RelCT isa P c fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨rd₁, wr₁, rd₂, wr₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂⟩ := hP _ _ hp
  obtain ⟨_, n₁⟩ := trace_narrow hv p₁ c₁ w₁ e₁
  obtain ⟨_, n₂⟩ := trace_narrow hv p₂ c₂ w₂ e₂
  exact ⟨hct _ _ _ _ _ _ p₁ p₂ hpub n₁ n₂, trivial⟩

/-- The arguments' moves leak nothing. -/
theorem args_taint : (taint.check (Taint.ofRegs [.a0, .a3, .a4, .a5]) (.block args)
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
    (htc : (taint.check (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5]) (convert I.curve.len wide) hc).isSome = true) :
    ConstantTime isa (hashR I K st).pre (hashR I K st).pub (hashed I.curve.len wide core) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold hashed
  refine RelCT.seq (R := fun u₁ u₂ => ∃ σ₁ σ₂ x₁ x₂ : State, u₁ = x₁ ∧ u₂ = x₂ ∧ HP (I := I) (K := K) (st := st) σ₁ σ₂ ∧
      (CPost I.curve.len wide σ₁ x₁ ∧ x₁.syms = σ₁.syms) ∧ (CPost I.curve.len wide σ₂ x₂ ∧ x₂.syms = σ₂.syms))
    ?_ (RelCT.seq (R := fun v₁ v₂ => ∃ σ₁ σ₂ x₁ x₂ : State, HP (I := I) (K := K) (st := st) σ₁ σ₂ ∧
      CPost I.curve.len wide σ₁ x₁ ∧ VFacts σ₁ x₁ v₁ ∧ CPost I.curve.len wide σ₂ x₂ ∧ VFacts σ₂ x₂ v₂) ?_ ?_)
  · refine ((RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5]) (fun s₁ s₂ h => ?_) htc).wpDep
      (F := fun (s t : State) => CPost I.curve.len wide s t ∧ t.syms = s.syms) fun s₁ s₂ h =>
        ⟨WP.mono_syms (convert_ok wide (cpre_of hL h66 h.1)) fun _ a sy => ⟨a, sy⟩,
          WP.mono_syms (convert_ok wide (cpre_of hL h66 h.2.1)) fun _ a sy => ⟨a, sy⟩⟩).mono (fun _ _ h => h)
      fun t₁ t₂ ⟨_, σ₁, σ₂, hp, a₁, a₂⟩ => ⟨σ₁, σ₂, t₁, t₂, rfl, rfl, hp, a₁, a₂⟩
    obtain ⟨-, -, psp, p0, p1, p2, p3, p4, p5, -⟩ := h
    refine ⟨psp, fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  · refine RelCT.exists_ fun σ₁ => RelCT.exists_ fun σ₂ => RelCT.exists_ fun x₁ => RelCT.exists_ fun x₂ => ?_
    refine ((RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a3, .a4, .a5]) (fun s₁ s₂ h => ?_) args_taint).wp
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
    · rw [k₁.gpr (by decide), k₂.gpr (by decide), p0]
    · rw [k₁.gpr (by decide), k₂.gpr (by decide), p3]
    · rw [k₁.gpr (by decide), k₂.gpr (by decide), p4]
    · rw [k₁.gpr (by decide), k₂.gpr (by decide), p5]
  · refine RelCT.inlineV hcv hct fun v₁ v₂ ⟨σ₁, σ₂, x₁, x₂, hp, c₁, f₁, c₂, f₂⟩ => ?_
    obtain ⟨q₁, cv₁, cw₁⟩ := vpre h66 hp.1 c₁ f₁
    obtain ⟨q₂, cv₂, cw₂⟩ := vpre h66 hp.2.1 c₂ f₂
    refine ⟨_, _, _, _, q₁, q₂, ?_, cv₁, cw₁, cv₂, cw₂⟩
    obtain ⟨psp, p0, p1, p2, p3, p4, p5, pl, psy⟩ := hp.2.2
    obtain ⟨b₁, k₁, g₁⟩ := vpost hp.1 c₁ f₁
    obtain ⟨b₂, k₂, g₂⟩ := vpost hp.2.1 c₂ f₂
    obtain ⟨ek, eh, eg⟩ := bytes_of_leak (by simp only [pkB, length_bytesAt])
      (by simp only [hashOf, length_bytesAt, p2]) pl
    refine ⟨by simp only [State.withRegions_sp, f₁.sp, f₂.sp, psp], by simp only [State.withRegions_gpr, f₁.a0, f₂.a0, p0],
      by simp only [State.withRegions_gpr, f₁.a1, f₂.a1, p5], by simp only [State.withRegions_gpr, f₁.a2, f₂.a2, p3],
      by simp only [State.withRegions_gpr, f₁.a3, f₂.a3, p4], ?_, fun c hc => ?_⟩
    · simp only [pkB, State.withRegions_mem, State.withRegions_gpr, f₁.a0, f₁.a1, f₁.a2, f₂.a0, f₂.a1, f₂.a2]
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
theorem core_pre {s : State} (h : KPre I 0 s) : (Proof.Ecdsa.verifyContract I abi 0).pre s := by
  sig_pre [Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig, Spec.Ecdsa.scratchWords,
    RISCV64.abi, RISCV64.argRegs]
  have hwr := h.wr
  rw [scratch_bytes] at hwr
  exact ⟨h.spal, h.rd, hwr, h.d03, h.d13, h.d23, h.f0, h.f1, h.f2, h.f3, h.al3⟩

theorem core_post {s s' : State} (h : (Proof.Ecdsa.verifyContract I abi 0).post s s') :
    (s'.gpr .a0).setWidth 32 = vres I s.mem (s.gpr .a0)
      (Spec.Ecdsa.hashToInt I.curve (Spec.Ecdsa.bytesAt s.mem (s.gpr .a1) I.curve.len)) (s.gpr .a2) := by
  sig_post [Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig, Spec.Ecdsa.scratchWords,
    RISCV64.abi, RISCV64.argRegs] at h
  exact h

theorem core_pub {s₁ s₂ : State} (h : s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3 ∧
    (pkB I s₁ ++ Spec.Ecdsa.bytesAt s₁.mem (s₁.gpr .a1) I.curve.len ++
        Spec.Ecdsa.bytesAt s₁.mem (s₁.gpr .a2) (2 * I.curve.len)).map (·.toNat) =
      (pkB I s₂ ++ Spec.Ecdsa.bytesAt s₂.mem (s₂.gpr .a1) I.curve.len ++
        Spec.Ecdsa.bytesAt s₂.mem (s₂.gpr .a2) (2 * I.curve.len)).map (·.toNat)) :
    (Proof.Ecdsa.verifyContract I abi 0).pub s₁ s₂ := by
  sig_pub [Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig, Spec.Ecdsa.scratchWords,
    RISCV64.abi, RISCV64.argRegs]
  obtain ⟨psp, p0, p1, p2, p3, pl⟩ := h
  exact ⟨psp, pl, p0, p1, p2, p3⟩

/-- The verification, run as `coreR` describes it, from its proof under `abi`. -/
theorem coreR_nil {core : Prog isa} (h : Verified target core (Proof.Ecdsa.verifyContract I abi 0)) :
    (∀ s, (coreR I [] 0).pre s → ∃ t s', Exec isa core s t s' ∧ abiPreserved s s' ∧ (coreR I [] 0).post s s') ∧
      ConstantTime isa (coreR I [] 0).pre (coreR I [] 0).pub core := by
  obtain ⟨hc, hct, -⟩ := h
  have hp : ∀ s, (coreR I [] 0).pre s → (Proof.Ecdsa.verifyContract I abi 0).pre s := fun s hs => by
    have := hs.1; rw [stripConsts_nil] at this; exact core_pre this
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_⟩
  · obtain ⟨t, s', he, ha, hq⟩ := hc s (hp s hs)
    exact ⟨t, s', he, ha, core_post hq⟩
  · obtain ⟨psp, p0, p1, p2, p3, pl, -⟩ := hpub
    exact hct _ _ _ _ _ _ (hp _ h₁) (hp _ h₂) (core_pub ⟨psp, p0, p1, p2, p3, pl⟩) e₁ e₂

/-- The same, from its proof under `abi.withConsts` of its tables. -/
theorem coreR_cons {c₀ : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}
    {core : Prog isa} (h : Verified target core (Proof.Ecdsa.verifyContract I (abi.withConsts (c₀ :: cs)) 0)) :
    (∀ s, (coreR I (c₀ :: cs) 0).pre s →
      ∃ t s', Exec isa core s t s' ∧ abiPreserved s s' ∧ (coreR I (c₀ :: cs) 0).post s s') ∧
      ConstantTime isa (coreR I (c₀ :: cs) 0).pre (coreR I (c₀ :: cs) 0).pub core := by
  obtain ⟨hc, hct, -⟩ := h
  have hp : ∀ s, (coreR I (c₀ :: cs) 0).pre s → (Proof.Ecdsa.verifyContract I (abi.withConsts (c₀ :: cs)) 0).pre s :=
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

theorem inner_ipre {s : State} (h : (innerA (I := I)).pre s) : IPre I 0 s := by
  have h' := (pre_regs (hashSig_words I) rfl).mp (pre_leak.mp h)
  simp only [Spec.Ecdsa.Instance.verifyHashSig, Sig.withScratch, Sig.bufs, regArgs, argRegs, Sig.words,
    Param.words, Sig.alignedBufs, Elem.size, Elem.align, List.pairwise_cons, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append, List.length_cons,
    List.length_nil, List.take, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil] at h'
  simp at h'
  obtain ⟨hal, hrd, hwr, ⟨⟨d04, d05⟩, ⟨d14, d15⟩, ⟨d34, d35⟩, d45⟩, hb, ⟨f0, f1, f3, f4, f5⟩, -, al4⟩ := h'
  exact ⟨hal, .inl rfl, hrd, hwr, d04, d05, d14, d15, d34, d35, d45, hb, f0, f1, f3, f4, by omega, al4⟩

theorem inner_post {s s' : State} (h : (hashR I [] 0).post s s') : (innerA (I := I)).post s s' := by
  sig_post [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, hPost,
    Spec.Ecdsa.Instance.verifyHashSig, Spec.Ecdsa.scratchWords, RISCV64.abi, RISCV64.argRegs]
  exact h

theorem inner_pub {K : List (String × List (BitVec 64))} {s₁ s₂ : State} (h : (innerA (I := I)).pub s₁ s₂)
    (hsy : ∀ c ∈ K, s₁.syms c.1 = s₂.syms c.1) : (hashR I K 0).pub s₁ s₂ := by
  sig_pub [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, hPost, hLeak, Option.map,
    Spec.Ecdsa.Instance.verifyHashSig, Spec.Ecdsa.scratchWords, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨psp, pl, p0, p1, p2, p3, p4, p5⟩ := h
  exact ⟨psp, p0, p1, p2, p3, p4, p5, pl, hsy⟩

/-- `hashed` under `abi`. -/
theorem hashed_verified_nil {wide : Bool} {core : Prog isa}
    (hL : 8 * I.curve.len = Spec.Ecdsa.nBits I.curve + if wide then 7 else 0) (h66 : I.curve.len ≤ 66)
    (hcore : Verified target core (Proof.Ecdsa.verifyContract I abi 0)) {hc : Taint.Hint taint.T}
    (htc : (taint.check (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5]) (convert I.curve.len wide) hc).isSome = true)
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
    (hcore : Verified target core (Proof.Ecdsa.verifyContract I (abi.withConsts (c₀ :: cs)) 0)) {hc : Taint.Hint taint.T}
    (htc : (taint.check (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5]) (convert I.curve.len wide) hc).isSome = true)
    (hsat : ∃ s, (innerK (I := I) c₀ cs).pre s) :
    Verified target (hashed I.curve.len wide core) (innerK (I := I) c₀ cs) := by
  obtain ⟨hcv, hct⟩ := coreR_cons hcore
  refine Verified.of_correct (T := target) (k := hashR I (c₀ :: cs) 0) (k' := innerK (I := I) c₀ cs) (hashed_correct I hL h66 hcv)
    (hashed_ct hL h66 hcv hct htc) ⟨fun s hs => ?_, fun s s' _ h => post_consts.mpr (inner_post h),
      fun s₁ s₂ _ _ h => ?_, hsat⟩
  · obtain ⟨h₁, h₂⟩ := pre_consts.mp hs
    exact ⟨inner_ipre h₁, h₂⟩
  · obtain ⟨h₁, h₂⟩ := pub_consts.mp h
    exact inner_pub h₁ h₂

/-- `vg_ecdsa_<curve>_verify` under `abi`, from the verification of the `len` bytes. -/
theorem verifyHash_verified_nil {wide : Bool} {core : Prog isa}
    (hL : 8 * I.curve.len = Spec.Ecdsa.nBits I.curve + if wide then 7 else 0) (h66 : I.curve.len ≤ 66)
    (hcore : Verified target core (Proof.Ecdsa.verifyContract I abi 0)) {hc : Taint.Hint taint.T}
    (htc : (taint.check (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5]) (convert I.curve.len wide) hc).isSome = true)
    (hsat : ∃ s, (I.verifyHashContract abi 80).pre s) :
    Verified target (verifyHash I.curve.len wide core) (I.verifyHashContract abi 80) := by
  obtain ⟨s₀, h₀⟩ := hsat
  have hk : (I.verifyHashSig.words abi.ptrBits).length < 8 := by
    simp [Spec.Ecdsa.Instance.verifyHashSig, Sig.words, Param.words]
  have hb : 0 < 80 ∧ 80 ≤ 4064 ∧ 80 % 16 = 0 ∧ 80 * Elem.u8.size ≤ 80 := by decide
  exact Verified.stackScratchL (sig := I.verifyHashSig) (nm := "buf") (e := .u8) (n := 80)
    (pre := Curry.const (fun _ => True) _) (post := hPost I) (wa := true) (stack := 0) (bytes := 80)
    (hashed_verified_nil hL h66 hcore htc ⟨_, narrow_pre (nm := "buf") hk hb (pre_leak.mp h₀) rfl⟩) hk hb
    ⟨s₀, h₀⟩ rfl

/-- `vg_ecdsa_<curve>_verify` under `abi.withConsts`, from the verification of the `len` bytes. -/
theorem verifyHash_verified_cons {wide : Bool} {core : Prog isa} {c₀ : String × List (BitVec 64)}
    {cs : List (String × List (BitVec 64))}
    (hL : 8 * I.curve.len = Spec.Ecdsa.nBits I.curve + if wide then 7 else 0) (h66 : I.curve.len ≤ 66)
    (hcore : Verified target core (Proof.Ecdsa.verifyContract I (abi.withConsts (c₀ :: cs)) 0)) {hc : Taint.Hint taint.T}
    (htc : (taint.check (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5]) (convert I.curve.len wide) hc).isSome = true)
    (hsat : ∃ s, (I.verifyHashContract (abi.withConsts (c₀ :: cs)) 80).pre s) :
    Verified target (verifyHash I.curve.len wide core) (I.verifyHashContract (abi.withConsts (c₀ :: cs)) 80) := by
  obtain ⟨s₀, h₀⟩ := hsat
  have hk : (I.verifyHashSig.words abi.ptrBits).length < 8 := by
    simp [Spec.Ecdsa.Instance.verifyHashSig, Sig.words, Param.words]
  have hb : 0 < 80 ∧ 80 ≤ 4064 ∧ 80 % 16 = 0 ∧ 80 * Elem.u8.size ≤ 80 := by decide
  exact Verified.stackScratchLC (sig := I.verifyHashSig) (nm := "buf") (e := .u8) (n := 80)
    (pre := Curry.const (fun _ => True) _) (post := hPost I) (wa := true) (stack := 0) (bytes := 80)
    (hashed_verified_cons hL h66 hcore htc ⟨_, narrowK_pre (nm := "buf") (post := hPost I) hk hb rfl h₀⟩) hk hb
    ⟨s₀, h₀⟩ rfl

end

/-! ## Satisfiability -/

section
variable {I}

/-- `s₀`, for the verification of the `len` bytes, with `len` in `a2`, `sig`
in `a3` and `scratch` in `a4`: the hash is the `len` bytes. -/
def hashSatState (L : Nat) (s₀ : State) : State :=
  { s₀ with gpr := fun r => match r with
      | .a2 => BitVec.ofNat 64 L | .a3 => s₀.gpr .a2 | .a4 => s₀.gpr .a3 | r => s₀.gpr r }

theorem hashSat_abi (h66 : I.curve.len ≤ 66) {s₀ : State} (h₀ : (Proof.Ecdsa.verifyContract I abi 0).pre s₀)
    (hsp : 80 ≤ s₀.sp.toNat) (hd : ∀ r ∈ s₀.rd ++ s₀.wr, (⟨s₀.sp - 80#64, 80⟩ : Region).Disjoint r) :
    (I.verifyHashContract abi 80).pre (hashSatState I.curve.len s₀) := by
  sig_pre [Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig, Spec.Ecdsa.scratchWords,
    RISCV64.abi, RISCV64.argRegs] at h₀
  obtain ⟨hal, hrd, hwr, d0, d1, d2, f0, f1, f2, f3, al⟩ := h₀
  sig_pre [Spec.Ecdsa.Instance.verifyHashContract, Spec.Ecdsa.Instance.verifyHashSig, Spec.Ecdsa.scratchWords,
    RISCV64.abi, RISCV64.argRegs, stackBelow]
  have hL : (BitVec.ofNat 64 I.curve.len).toNat = I.curve.len := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  simp only [hL]
  rw [hrd, hwr] at hd
  refine ⟨hal, hsp, hrd, hwr, d0, d1, d2, hd _ (by simp), hd _ (by simp), hd _ (by simp), hd _ (by simp),
    f0, f1, f2, f3, al⟩

/-- A state satisfying `verifyHashContract`'s precondition under `abi`, from one of
the verification's whose 80 bytes below the stack pointer are free. -/
theorem hashSat_nil (h66 : I.curve.len ≤ 66) {s₀ : State} (h₀ : (Proof.Ecdsa.verifyContract I abi 0).pre s₀)
    (hsp : 80 ≤ s₀.sp.toNat) (hd : ∀ r ∈ s₀.rd ++ s₀.wr, (⟨s₀.sp - 80#64, 80⟩ : Region).Disjoint r) :
    ∃ s, (I.verifyHashContract abi 80).pre s :=
  ⟨_, hashSat_abi h66 h₀ hsp hd⟩

/-- The same under `abi.withConsts`. -/
theorem hashSat_cons {c₀ : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}
    (h66 : I.curve.len ≤ 66) {s₀ : State} (h₀ : (Proof.Ecdsa.verifyContract I (abi.withConsts (c₀ :: cs)) 0).pre s₀)
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

end VG.Proof.Ecdsa.Verify.RISCV64
