module

public import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.Proof.Ecdsa.Verify.Hash
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Arm.Syms
public import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.RelCT
public meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
public import VerifiedGarbage.Proof.Framework.Arm.StackScratch
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
public import VerifiedGarbage.Spec.Ecdsa.Generic
import VerifiedGarbage.Proof.AesGcm.Arm.Loops
import VerifiedGarbage.Spec.Aes
import VerifiedGarbage.Proof.AesGcm.Arm.Run
import VerifiedGarbage.Proof.AesGcm.Arm.Env
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Arm.Bytes

/-!
# ECDSA verification of the hash function's output on 32-bit ARM

Untrusted: everything here is checked by Lean. As on RISC-V
(`Proof/Ecdsa/Verify/RISCV64/Hash.lean`), for every curve:

* `convert_ok`: `convert len wide` writes `fixedDigest len wide` of the hash
  at `r1` (`r2` bytes) to the first `len` bytes of the buffer whose address
  is the second stack argument (`bf`), and `sig` (`r3`) to its word at
  `sigOff`, changing only the buffer's 80 bytes, the registers `r1`–`r3` and
  `r12`, and the flags;
* `hashed_correct`, `hashed_ct`: `hashed`, the conversion, the loads of the
  verification's arguments and the verification inlined, by register
  (`hashR`), from the verification's `Verified` (`coreR_nil`, `coreR_cons`);
  constant time by taint tracking for the conversion and the loads (the
  stack arguments are public: `argTaint`), and the verification's own
  constant time for the rest;
* `verifyHash_verified_nil`, `verifyHash_verified_cons`: under the contracts
  of `Spec/`, with the buffer in a frame on the stack
  (`Verified.stackScratchL`, and `Verified.stackScratchC` for a verification
  with tables), from a state satisfying the verification's precondition
  (`hashSat_nil`, `hashSat_cons`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Ecdsa.Verify.Arm.Hash

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Ecdsa.Arm.VerifyHash VG.WriteBytes
open VG.Impl.AesGcm.Arm (imm copyLoop)
open VG.Proof.AesGcm.Arm (withMem LoopPre LoopOut copyLoop_ok)

variable {len : Nat} {s : State}

/-- The buffer's 32-bit address: the second stack argument. -/
abbrev bf (s : State) : BitVec 32 := stackArg s 1

/-- The buffer's address. -/
abbrev bufA (s : State) : Addr := State.addr (bf s)

/-- The hash. -/
abbrev hashOf (s : State) : List Byte :=
  Spec.Ecdsa.bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat

/-- What `convert` needs of its state: the stack arguments and the hash's
bytes readable, the buffer's 80 bytes writable and apart from them, none of
them wrapping around. -/
structure CPre (len : Nat) (s : State) : Prop where
  len1 : 0 < len
  len66 : len ≤ 66
  spfit : s.sp.toNat + 8 ≤ 2 ^ 32
  args : Covers [⟨State.addr s.sp, 8⟩] (s.rd ++ s.wr)
  rd : Covers [⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩] (s.rd ++ s.wr)
  wr : Covers [⟨bufA s, 80⟩] s.wr
  sep : (⟨bufA s, 80⟩ : Region).Disjoint ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩
  stk : (⟨bufA s, 80⟩ : Region).Disjoint ⟨State.addr s.sp, 8⟩
  fitB : (bf s).toNat + 80 ≤ 2 ^ 32
  fitD : (s.gpr .r1).toNat + (s.gpr .r2).toNat ≤ 2 ^ 32

/-- The registers but `r1`–`r3` and `r12` are kept. -/
abbrev Regs (s u : State) : Prop := ∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → u.gpr r = s.gpr r

/-- What `convert` leaves. -/
structure CPost (len : Nat) (wide : Bool) (s t : State) : Prop where
  buf : ∀ i < len, t.mem (bufA s + BitVec.ofNat 64 i) = (fixedDigest len wide (hashOf s)).getD i 0
  sigw : t.mem.readW (State.addr (bf s + BitVec.ofNat 32 sigOff)) 32 = s.gpr .r3
  frame : Frame [⟨bufA s, 80⟩] s.mem t.mem
  regs : Regs s t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

/-! ## Bytes -/

theorem ite_t {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

theorem ite_f {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) : (if c then a else b) = b := by
  simp [h]

theorem ite_of_iff {α : Sort _} {c d : Prop} [Decidable c] [Decidable d] {a b : α} (h : c ↔ d) :
    (if c then a else b) = if d then a else b := by
  by_cases hc : c
  · rw [ite_t hc, ite_t (h.mp hc)]
  · rw [ite_f hc, ite_f (fun hd => hc (h.mpr hd))]

theorem ofNat_toNat32 (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by simp

private theorem aes_bytesAt_getD (m : Mem) (p : Addr) (n i : Nat) (hi : i < n) :
    (Spec.Aes.bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Aes.bytesAt, hi]

/-- The value `shiftBytes` stores. -/
theorem shift_byte32 (b c : Byte) :
    ((b.setWidth 32 <<< 7) + (c.setWidth 32 >>> 1)).setWidth 8 = sh b c := by
  apply BitVec.eq_of_toNat_eq
  have hb := b.isLt
  have hc := c.isLt
  rw [sh_toNat, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_shiftLeft,
    BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  simp only [Nat.reducePow]
  omega

theorem fixed_long {len : Nat} {H : List Byte} (hl : len ≤ H.length) (wide : Bool) {i : Nat}
    (hi : i < len) : (fixedDigest len wide H).getD i 0 = H.getD i 0 := by
  rw [fixedDigest, ite_eq_left_of_eq_true _ _ (eq_true hl), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt hi]

/-! ## Addresses -/

section
variable (hp : CPre len s)
include hp

theorem bufA_add {i : Nat} (hi : i < 80) :
    State.addr (bf s + BitVec.ofNat 32 i) = bufA s + BitVec.ofNat 64 i :=
  addr_add (by have := hp.fitB; omega)

theorem hashA_add {i : Nat} (hi : i < (s.gpr .r2).toNat) :
    State.addr (s.gpr .r1 + BitVec.ofNat 32 i) = State.addr (s.gpr .r1) + BitVec.ofNat 64 i :=
  addr_add (by have := hp.fitD; omega)

theorem spA_add {i : Nat} (hi : i < 8) :
    State.addr (s.sp + BitVec.ofNat 32 i) = State.addr s.sp + BitVec.ofNat 64 i :=
  addr_add (by have := hp.spfit; omega)

theorem buf_in {d n : Nat} (h : d + n ≤ 80) : InRegions s.wr (bufA s + BitVec.ofNat 64 d) n :=
  VG.Proof.AesGcm.Arm.in_off hp.wr h (by decide)

/-- A byte of the buffer is not one of the hash's. -/
theorem buf_ne_hash {j i : Nat} (hj : j < 80) (hi : i < (s.gpr .r2).toNat) :
    bufA s + BitVec.ofNat 64 j ≠ State.addr (s.gpr .r1) + BitVec.ofNat 64 i := by
  intro e
  have h₁ : (⟨bufA s, 80⟩ : Region).Contains (bufA s + BitVec.ofNat 64 j) 1 :=
    Offset.contains_base _ (by omega) (by omega)
  have h₂ : (⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩ : Region).Contains
      (State.addr (s.gpr .r1) + BitVec.ofNat 64 i) 1 := Offset.contains_base _ (by omega) (by omega)
  rw [← e] at h₂
  exact hp.sep _ h₁ h₂

omit hp in
/-- Nothing outside the buffer is in it. -/
theorem out_buf {x : Addr} (hx : ¬ (⟨bufA s, 80⟩ : Region).Contains x 1) {j : Nat} (hj : j < 80) :
    x ≠ bufA s + BitVec.ofNat 64 j := by
  rintro rfl
  exact hx (Offset.contains_base _ (by omega) (by omega))

end

/-! ## The head -/

/-- What `head` leaves. -/
structure HPost (len : Nat) (s s₁ : State) : Prop where
  r12 : s₁.gpr .r12 = bf s
  mem : s₁.mem = s.mem.writeW (State.addr (bf s + BitVec.ofNat 32 sigOff)) (s.gpr .r3)
  z : s₁.z = decide ((s.gpr .r2).toNat < len)
  regs : ∀ r, r ≠ .r3 → r ≠ .r12 → s₁.gpr r = s.gpr r
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr
  sp : s₁.sp = s.sp

/-- `Z` after `mov r3, #0; adc r3, r3, #0; cmp r3, #0`, from the carry of
`cmp a, b` (`b ≤ a`). -/
theorem adc_z (a b : Nat) :
    ((0#32 + 0#32 + if decide (b ≤ a) = true then 1 else 0 : BitVec 32) - 0#32 == 0) = decide (a < b) := by
  by_cases h : b ≤ a
  · rw [decide_eq_true h, decide_eq_false (by omega)]; decide
  · rw [decide_eq_false h, decide_eq_true (by omega)]; decide

/-- An immediate below 256 is encodable (rotation 0). -/
theorem encodable_lt {n : Nat} (h : n < 256) : encodable (BitVec.ofNat 32 n) = true :=
  List.any_eq_true.2 ⟨0, by simp, by
    have h0 : (BitVec.ofNat 32 n).rotateLeft (2 * 0) = BitVec.ofNat 32 n := by ext i; simp
    rw [h0, BitVec.toNat_ofNat]; exact decide_eq_true (by omega)⟩

theorem head_ok (hp : CPre len s) : WP isa (.block (head len)) s (HPost len s) := by
  have h66 := hp.len66
  have hst : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 4)) 4 := by
    rw [spA_add hp (by decide)]; exact VG.Proof.AesGcm.Arm.in_off hp.args (by decide) (by decide)
  have e12 : s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 4)) 32 = bf s := rfl
  have hsw : InRegions s.wr (State.addr (bf s + BitVec.ofNat 32 76)) 4 := by
    rw [bufA_add hp (by decide)]; exact buf_in hp (by decide)
  have hen := encodable_lt (n := len) (by omega)
  refine WP.of_runBlock ⟨_, by arun [head, sigOff, hst, e12, hsw, hen], ?_⟩
  have hl : (BitVec.ofNat 32 len).toNat = len := by rw [BitVec.toNat_ofNat]; omega
  refine ⟨?_, ?_, ?_, fun r h3 h12 => ?_, rfl, rfl, rfl⟩
  · simp only [VG.Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, VG.Proof.AesGcm.Arm.gpr_store]; rfl
  · rfl
  · simp only [VG.Proof.AesGcm.Arm.z_subFlags, hl, adc_z]
  · simp [VG.Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, h3, h12]

/-! ## Memory -/

theorem byte_writeW_other (m : Mem) {a x : Addr} (b : Byte) (h : x ≠ a) : (m.writeW a b) x = m x := by
  simp only [WriteBytes.writeW8_apply, h, ite_false]

/-- What the conversion keeps after the head (`s₁`): it writes only the
buffer's first 72 bytes. -/
structure After (s s₁ u : State) : Prop where
  frame : Frame [⟨bufA s, 72⟩] s₁.mem u.mem
  regs : Regs s u
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  sp : u.sp = s.sp

theorem After.refl {s s₁ : State} (h : HPost len s s₁) : After s s₁ s₁ :=
  ⟨Frame.refl _ _, fun r _ _ h3 h12 => h.regs r h3 h12, h.rd, h.wr, h.sp⟩

section
variable {s₁ : State} (hp : CPre len s) (hh : HPost len s s₁)
include hp hh

/-- The head writes only the buffer's word at `sigOff`. -/
theorem head_frame : Frame [⟨bufA s, 80⟩] s.mem s₁.mem := by
  rw [hh.mem]
  refine (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_
  rw [bufA_add hp (by decide)]
  exact Offset.contains_base _ (by decide) (by decide)

theorem head_low {j : Nat} (hj : j < 76) :
    s₁.mem (bufA s + BitVec.ofNat 64 j) = s.mem (bufA s + BitVec.ofNat 64 j) := by
  rw [hh.mem, bufA_add hp (by decide : sigOff < 80)]
  exact VG.Arm.writeW32_other _ (VG.Arm.off_disjoint _ (by simp only [sigOff]; omega) (by omega) (by decide))

/-- A byte outside the buffer, in a state after the head. -/
theorem out_after {u : State} (ha : After s s₁ u) {x : Addr} (hx : ¬ (⟨bufA s, 80⟩ : Region).Contains x 1) :
    u.mem x = s.mem x := by
  rw [ha.frame _ fun r hr hc => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hx (Offset.sub_base _ (by omega : 0 + 72 ≤ 80) _ (by simpa using hc))]
  exact head_frame hp hh _ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hx

/-- A byte of the hash, in a state after the head. -/
theorem hash_after {u : State} (ha : After s s₁ u) {i : Nat} (hi : i < (s.gpr .r2).toNat) :
    u.mem (State.addr (s.gpr .r1) + BitVec.ofNat 64 i) = (hashOf s).getD i 0 := by
  rw [bytesAt_getD _ _ _ _ hi]
  exact out_after hp hh ha fun hc => hp.sep _ hc (Offset.contains_base _ (by omega) (by have := hp.fitD; omega))

end

/-- What the rest of the conversion leaves, after the head (`s₁`). -/
structure MPost (len : Nat) (wide : Bool) (s s₁ t : State) : Prop where
  after : After s s₁ t
  buf : ∀ i < len, t.mem (bufA s + BitVec.ofNat 64 i) = (fixedDigest len wide (hashOf s)).getD i 0

section
variable {s₁ : State} (hp : CPre len s) (hh : HPost len s s₁)
include hp hh

omit hh in
/-- A step of the copies into the buffer: byte `k` written with `b`. -/
theorem after_write {u : State} (ha : After s s₁ u) {k : Nat} (hk : k < 72) (b : Byte) :
    Frame [⟨bufA s, 72⟩] s₁.mem (u.mem.writeW (State.addr (bf s + BitVec.ofNat 32 k)) b) := by
  rw [bufA_add hp (by omega)]
  exact ha.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))

/-! ## A hash of at least `len` bytes -/

/-- After `k` bytes of `long`. -/
structure LInv (s s₁ : State) (k : Nat) (u : State) : Prop where
  after : After s s₁ u
  r1 : u.gpr .r1 = s.gpr .r1
  r12 : u.gpr .r12 = bf s
  buf : ∀ j < k, u.mem (bufA s + BitVec.ofNat 64 j) = (hashOf s).getD j 0

theorem long_ok (wide : Bool) (hl : len ≤ (s.gpr .r2).toNat) :
    WP isa (.block (long len)) s₁ (MPost len wide s s₁) := by
  have h66 := hp.len66
  refine WP.mono (wp_range_flatMap (M := isa) (LInv s s₁) (fun k u hk h => ?_) len (Nat.le_refl _) s₁
    ⟨After.refl hh, by rw [hh.regs _ (by decide) (by decide)], hh.r12, fun j hj => absurd hj (Nat.not_lt_zero _)⟩)
    fun t ht => ⟨ht.after, fun i hi => by rw [ht.buf i hi, fixed_long (by rw [length_bytesAt]; exact hl) wide hi]⟩
  have ha := h.after
  have hk2 : k < (s.gpr .r2).toNat := by omega
  have hrd : InRegions (u.rd ++ u.wr) (State.addr (s.gpr .r1 + BitVec.ofNat 32 k)) 1 := by
    rw [ha.rd, ha.wr, hashA_add hp hk2]; exact VG.Proof.AesGcm.Arm.in_off hp.rd (by omega) (by omega)
  have hwr : InRegions u.wr (State.addr (bf s + BitVec.ofNat 32 k)) 1 := by
    rw [ha.wr, bufA_add hp (by omega)]; exact buf_in hp (by omega)
  have hr1 := h.r1
  have hr12 := h.r12
  have hk4 : k < 4096 := by omega
  refine WP.of_runBlock ⟨_, by arun [hr1, hr12, hrd, hwr, hk4], ?_⟩
  have hv : u.mem (State.addr (s.gpr .r1 + BitVec.ofNat 32 k)) = (hashOf s).getD k 0 := by
    rw [hashA_add hp hk2]; exact hash_after hp hh ha hk2
  refine ⟨⟨after_write hp ha (by omega) _, fun r h1 h2 h3 h12 => ?_, ha.rd, ha.wr, ha.sp⟩, ?_, ?_, fun j hj => ?_⟩
  · simp only [VG.Proof.AesGcm.Arm.gpr_store, gpr_setReg, h3, ite_false]; exact ha.regs r h1 h2 h3 h12
  · simp only [VG.Proof.AesGcm.Arm.gpr_store, gpr_setReg]; simpa using hr1
  · simp only [VG.Proof.AesGcm.Arm.gpr_store, gpr_setReg]; simpa using hr12
  · simp only [VG.Proof.AesGcm.Arm.mem_store, VG.Proof.AesGcm.Arm.setWidth8_32, bufA_add hp (by omega : k < 80)]
    by_cases e : j = k
    · subst e; rw [byte_writeW_eq, hv]
    · rw [byte_writeW_ne' _ _ _ (by omega) (by omega) e, h.buf j (by omega)]

end

section
variable {s₁ : State} (hp : CPre len s) (hh : HPost len s s₁)
include hp hh

/-! ## A shorter hash: the zeros -/

/-- After `k` of the zeros. -/
structure ZInv (s s₁ : State) (k : Nat) (u : State) : Prop where
  after : After s s₁ u
  r1 : u.gpr .r1 = s.gpr .r1
  r2 : u.gpr .r2 = s.gpr .r2
  r3 : u.gpr .r3 = 0
  r12 : u.gpr .r12 = bf s
  buf : ∀ j < k, u.mem (bufA s + BitVec.ofNat 64 j) = 0

omit hh in
theorem zeros_stores {u : State} (hz : ZInv s s₁ 0 u) :
    WP isa (.block ((List.range 72).flatMap fun i => [.strb .r3 .r12 i])) u (ZInv s s₁ 72) := by
  refine wp_range_flatMap (M := isa) (ZInv s s₁) (fun k u hk h => ?_) 72 (Nat.le_refl _) u hz
  have ha := h.after
  have hwr : InRegions u.wr (State.addr (bf s + BitVec.ofNat 32 k)) 1 := by
    rw [ha.wr, bufA_add hp (by omega)]; exact buf_in hp (by omega)
  have hr3 := h.r3
  have hr12 := h.r12
  have hk4 : k < 4096 := by omega
  refine WP.of_runBlock ⟨_, by arun [hr3, hr12, hwr, hk4], ?_⟩
  refine ⟨⟨after_write hp ha (by omega) _, ha.regs, ha.rd, ha.wr, ha.sp⟩, h.r1, h.r2, hr3, hr12,
    fun j hj => ?_⟩
  simp only [VG.Proof.AesGcm.Arm.mem_store, bufA_add hp (by omega : k < 80)]
  by_cases e : j = k
  · subst e; rw [byte_writeW_eq]; rfl
  · rw [byte_writeW_ne' _ _ _ (by omega) (by omega) e, h.buf j (by omega)]

/-- What `zeros` leaves: the count in `r3`, where the hash goes in `r2`, and
`Z` set iff the hash is empty. -/
structure ZPost (s s₁ : State) (u : State) : Prop where
  after : After s s₁ u
  r1 : u.gpr .r1 = s.gpr .r1
  r2 : u.gpr .r2 = bf s + BitVec.ofNat 32 len - s.gpr .r2
  r3 : u.gpr .r3 = s.gpr .r2
  z : u.z = (s.gpr .r2 == 0)
  buf : ∀ j < 72, u.mem (bufA s + BitVec.ofNat 64 j) = 0

theorem zeros_ok : WP isa (.block (zeros len)) s₁ (ZPost (len := len) s s₁) := by
  have h66 := hp.len66
  rw [show zeros len = [.mov .r3 (imm 0)] ++ (((List.range 72).flatMap fun i => [.strb .r3 .r12 i]) ++
      [.mov .r3 (.reg .r2), .dp .add .r2 .r12 (imm len), .dp .sub .r2 .r2 (.reg .r3), .cmp .r3 (imm 0)]) from rfl,
    WP.block_append_iff]
  refine WP.block_cons_iff.mpr ⟨s₁.setReg .r3 0, rfl, WP.block_nil ?_⟩
  rw [WP.block_append_iff]
  refine WP.mono (zeros_stores (s₁ := s₁) hp ⟨?_, ?_, ?_, ?_, ?_, fun j hj => absurd hj (Nat.not_lt_zero _)⟩)
    fun u h => ?_
  · exact ⟨Frame.refl _ _, fun r _ _ h3 h12 => by
      rw [gpr_setReg]; simp only [h3, ite_false]; exact hh.regs r h3 h12, hh.rd, hh.wr, hh.sp⟩
  · rw [gpr_setReg]; simp only [reduceCtorEq, ite_false]; exact hh.regs _ (by decide) (by decide)
  · rw [gpr_setReg]; simp only [reduceCtorEq, ite_false]; exact hh.regs _ (by decide) (by decide)
  · rw [gpr_setReg]; simp only [ite_true]
  · rw [gpr_setReg]; simp only [reduceCtorEq, ite_false]; exact hh.r12
  have ha := h.after
  have hr2 := h.r2
  have hr12 := h.r12
  have hen := encodable_lt (n := len) (by omega)
  refine WP.of_runBlock ⟨_, by arun [hr2, hr12, hen], ?_⟩
  refine ⟨⟨ha.frame, fun r h1 h2 h3 h12 => ?_, ha.rd, ha.wr, ha.sp⟩, ?_, ?_, ?_, ?_, h.buf⟩
  · simp only [VG.Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, h2, h3, ite_false]; exact ha.regs r h1 h2 h3 h12
  · simp only [VG.Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg]; simpa using h.r1
  · simp only [VG.Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg]; simp
  · simp only [VG.Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg]; simp
  · simp only [VG.Proof.AesGcm.Arm.z_subFlags, gpr_setReg]; simp

end

section
variable {s₁ : State} (hp : CPre len s) (hh : HPost len s s₁)
include hp hh

/-! ## A shorter hash: the copy -/

/-- The buffer holds the zeros and the hash (`tz`). -/
structure TInv (s s₁ : State) (u : State) : Prop where
  after : After s s₁ u
  buf : ∀ j < 72, u.mem (bufA s + BitVec.ofNat 64 j) = tz len (hashOf s) j

theorem copy_ok (hl : (s.gpr .r2).toNat < len) {u : State} (hz : ZPost (len := len) s s₁ u) :
    WP isa (.ite .eq (.block []) copyLoop) u (TInv (len := len) s s₁) := by
  have h66 := hp.len66
  have hB := hp.fitB
  have hD := hp.fitD
  have ha := hz.after
  refine WP.ite u.z rfl (fun h0 => WP.block_nil ⟨ha, fun j hj => ?_⟩) (fun h0 => ?_)
  · have hd0 : (s.gpr .r2).toNat = 0 := by
      rw [hz.z] at h0; simp only [beq_iff_eq] at h0; rw [h0]; rfl
    rw [hz.buf j hj, tz, ite_f (by rw [length_bytesAt, hd0]; omega)]
  have hd0 : (s.gpr .r2).toNat ≠ 0 := by
    intro e; rw [hz.z] at h0; simp only [beq_eq_false_iff_ne, ne_eq] at h0
    exact h0 (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
  generalize hn : (s.gpr .r2).toNat = n at hl hd0
  have hD' : (s.gpr .r1).toNat + n ≤ 2 ^ 32 := by rw [← hn]; exact hD
  have eD : u.gpr .r2 = bf s + BitVec.ofNat 32 (len - n) := by
    rw [hz.r2, ← ofNat_toNat32 (s.gpr .r2), hn, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      ← BitVec.sub_eq_add_neg, VG.Proof.AesGcm.Arm.ofNat_sub32 (by omega) (by omega)]
  have aD : State.addr (bf s + BitVec.ofNat 32 (len - n)) = bufA s + BitVec.ofNat 64 (len - n) :=
    bufA_add hp (by omega)
  have hpre : LoopPre u (s.gpr .r1) (bf s + BitVec.ofNat 32 (len - n)) n := by
    refine ⟨hz.r1, eD, by rw [hz.r3, ← hn, ofNat_toNat32], by omega, by omega, hD', ?_, ?_, ?_, ?_⟩
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := len - n) (by omega),
        Nat.mod_eq_of_lt (by omega)]; omega
    · rw [ha.rd, ha.wr, ← hn]; exact hp.rd
    · rw [ha.wr, aD]; exact VG.Proof.AesGcm.Arm.covers_off hp.wr (by omega) (by decide)
    · rw [aD]
      exact (hp.sep.symm.sub_left (by rw [← hn]; exact Region.sub_prefix (Nat.le_refl _))).sub_right
        (Offset.sub_base _ (by omega))
  refine WP.mono (WP.gpr (copyLoop_ok u hpre) (r := .r0) (by decide)) fun t ⟨⟨hm, ho⟩, h0⟩ => ?_
  have hfr : Frame [⟨bufA s, 72⟩] u.mem t.mem := by
    rw [hm, aD]
    exact writeBytes_frame _ _ _ (by
      rw [show (Spec.Aes.bytesAt u.mem (State.addr (s.gpr .r1)) n).length = n by simp [Spec.Aes.bytesAt]]
      exact Offset.contains_base _ (by omega) (by omega))
  refine ⟨⟨ha.frame.trans hfr, fun r h1 h2 h3 h12 => ?_, by rw [ho.rd, ha.rd], by rw [ho.wr, ha.wr],
    by rw [ho.sp, ha.sp]⟩, fun j hj => ?_⟩
  · by_cases e : r = .r0
    · subst e; rw [h0]; exact ha.regs _ h1 h2 h3 h12
    · rw [ho.other r e h1 h2 h3 h12]; exact ha.regs _ h1 h2 h3 h12
  · have hH : (hashOf s).length = n := by rw [length_bytesAt, hn]
    have hlen : (Spec.Aes.bytesAt u.mem (State.addr (s.gpr .r1)) n).length = n := by simp [Spec.Aes.bytesAt]
    rw [hm, aD]
    simp only [writeBytes]
    rw [Offset.sub_toNat' _ (by omega) (by omega), hlen]
    unfold tz
    rw [hH]
    by_cases hin : len - n ≤ j ∧ j < len
    · rw [ite_t hin.1, ite_t (show j - (len - n) < n by omega), ite_t hin]
      rw [aes_bytesAt_getD u.mem (State.addr (s.gpr .r1)) n (j - (len - n)) (by omega)]
      exact hash_after hp hh ha (by omega)
    · rw [ite_f hin, hz.buf j hj]
      by_cases h1 : len - n ≤ j
      · rw [ite_t h1, ite_f (by omega)]
      · rw [ite_f h1, ite_f (by omega)]

end

section
variable {s₁ : State} (hp : CPre len s) (hh : HPost len s s₁)
include hp hh

/-- The stack arguments, in a state after the head. -/
theorem stack_after {u : State} (ha : After s s₁ u) {i : Nat} (hi : i < 2) :
    u.mem.readW (State.addr (s.sp + BitVec.ofNat 32 (4 * i))) 32 = stackArg s i := by
  rw [stackArg, stackArgAddr]
  refine Mem.readW_congr fun k hk => ?_
  rw [spA_add hp (by omega), Offset.add_add]
  exact out_after hp hh ha fun hc => hp.stk _ hc (Offset.contains_base _ (by omega) (by omega))

/-! ## A shorter hash: the shift -/

/-- After `k` bytes of the shift. -/
structure SInv (s s₁ : State) (k : Nat) (u : State) : Prop where
  after : After s s₁ u
  r12 : u.gpr .r12 = bf s
  buf : ∀ j < 72, u.mem (bufA s + BitVec.ofNat 64 j) =
    if j < k then sh (tz len (hashOf s) j) (tz len (hashOf s) (j + 1)) else tz len (hashOf s) j

theorem shift_ok (hl : (s.gpr .r2).toNat < len) {u : State} (hz : TInv (len := len) s s₁ u) :
    WP isa (.block (.ldrSp .r12 4 :: shiftBytes len)) u (MPost len true s s₁) := by
  have h66 := hp.len66
  have ha := hz.after
  rw [show (.ldrSp .r12 4 :: shiftBytes len : List Instr) = [.ldrSp .r12 4] ++ shiftBytes len from rfl,
    WP.block_append_iff]
  have hst : InRegions (u.rd ++ u.wr) (State.addr (s.sp + BitVec.ofNat 32 4)) 4 := by
    rw [ha.rd, ha.wr, spA_add hp (by decide)]; exact VG.Proof.AesGcm.Arm.in_off hp.args (by decide) (by decide)
  have hsp := ha.sp
  have e12 : u.mem.readW (State.addr (s.sp + BitVec.ofNat 32 4)) 32 = bf s := stack_after hp hh ha (i := 1) (by decide)
  refine WP.of_runBlock ⟨_, by arun [hsp, hst, e12], ?_⟩
  refine WP.mono (wp_range_flatMap (M := isa) (SInv (len := len) s s₁) (fun k u₁ hk h => ?_) len (Nat.le_refl _) _
    ⟨⟨ha.frame, fun r h1 h2 h3 h12 => ?_, ha.rd, ha.wr, ha.sp⟩, ?_, fun j hj => ?_⟩)
    fun t ht => ⟨ht.after, fun i hi => ?_⟩
  · have ha₁ := h.after
    have hr12 := h.r12
    have hr0 : InRegions (u₁.rd ++ u₁.wr) (State.addr (bf s + BitVec.ofNat 32 k)) 1 := by
      rw [ha₁.rd, ha₁.wr, bufA_add hp (by omega)]; exact VG.Proof.AesGcm.Arm.in_left (buf_in hp (by omega))
    have hr1 : InRegions (u₁.rd ++ u₁.wr) (State.addr (bf s + BitVec.ofNat 32 (k + 1))) 1 := by
      rw [ha₁.rd, ha₁.wr, bufA_add hp (by omega)]; exact VG.Proof.AesGcm.Arm.in_left (buf_in hp (by omega))
    have hwr : InRegions u₁.wr (State.addr (bf s + BitVec.ofNat 32 k)) 1 := by
      rw [ha₁.wr, bufA_add hp (by omega)]; exact buf_in hp (by omega)
    have hk4 : k < 4096 := by omega
    have hk4' : k + 1 < 4096 := by omega
    refine WP.of_runBlock ⟨_, by arun [hr12, hr0, hr1, hwr, hk4, hk4'], ?_⟩
    refine ⟨⟨after_write hp ha₁ (by omega) _, fun r h1 h2 h3 h12 => ?_, ha₁.rd, ha₁.wr, ha₁.sp⟩, ?_,
      fun j hj => ?_⟩
    · simp only [VG.Proof.AesGcm.Arm.gpr_store, gpr_setReg, h1, h2, ite_false]; exact ha₁.regs r h1 h2 h3 h12
    · simp only [VG.Proof.AesGcm.Arm.gpr_store, gpr_setReg]; simpa using hr12
    · simp only [VG.Proof.AesGcm.Arm.mem_store, bufA_add hp (by omega : k < 80), bufA_add hp (by omega : k + 1 < 80)]
      rw [shift_byte32]
      by_cases e : j = k
      · subst e
        rw [byte_writeW_eq, h.buf j (by omega), h.buf (j + 1) (by omega), ite_f (Nat.lt_irrefl _),
          ite_f (by omega), ite_t (by omega)]
      · rw [byte_writeW_ne' _ _ _ (by omega) (by omega) e, h.buf j hj]
        by_cases hjk : j < k
        · rw [ite_t hjk, ite_t (by omega)]
        · rw [ite_f hjk, ite_f (by omega)]
  · simp only [gpr_setReg, h12, ite_false]; exact ha.regs r h1 h2 h3 h12
  · simp only [gpr_setReg, ite_true]
  · simp only [Nat.not_lt_zero, ite_false]; exact hz.buf j hj
  · rw [ht.buf i (by omega), ite_t hi, fixed_short (by rw [length_bytesAt]; exact hl) true hi]; rfl

end

section
variable {s₁ : State} (hp : CPre len s) (hh : HPost len s s₁)
include hp hh

theorem tail_ok (wide : Bool) (hl : (s.gpr .r2).toNat < len) {u : State} (hz : TInv (len := len) s s₁ u) :
    WP isa (.block (if wide then .ldrSp .r12 4 :: shiftBytes len else [])) u (MPost len wide s s₁) := by
  cases wide with
  | true => exact shift_ok hp hh hl hz
  | false =>
    refine WP.block_nil ⟨hz.after, fun i hi => ?_⟩
    rw [hz.buf i (by have := hp.len66; omega), fixed_short (by rw [length_bytesAt]; exact hl) false hi]
    rfl

theorem short_ok (wide : Bool) (hl : (s.gpr .r2).toNat < len) :
    WP isa (short len wide) s₁ (MPost len wide s s₁) :=
  WP.seq (WP.mono (zeros_ok hp hh) fun _ hz =>
    WP.seq (WP.mono (copy_ok hp hh hl hz) fun _ hv => tail_ok hp hh wide hl hv))

/-- The rest of the conversion's result, as `CPost` states it. -/
theorem cpost_of {wide : Bool} {t : State} (hm : MPost len wide s s₁ t) : CPost len wide s t := by
  have ha := hm.after
  have hB := hp.fitB
  refine ⟨hm.buf, ?_, ?_, ha.regs, ha.rd, ha.wr, ha.sp⟩
  · rw [bufA_add hp (by decide : sigOff < 80)]
    have hd : (⟨bufA s + BitVec.ofNat 64 sigOff, 4⟩ : Region).Disjoint ⟨bufA s, 72⟩ := by
      have := VG.Arm.off_disjoint (bufA s) (x := 76) (lx := 4) (y := 0) (ly := 72) (by omega) (by omega) (by omega)
      simpa [sigOff] using this
    rw [ha.frame.readW (r := ⟨bufA s + BitVec.ofNat 64 sigOff, 4⟩) (Region.contains_self _ _)
      (fun r' hr' => by simp only [List.mem_singleton] at hr'; subst hr'; exact hd) (by decide), hh.mem,
      bufA_add hp (by decide : sigOff < 80), Mem.readW_writeW_self32]
  · refine (head_frame hp hh).trans (ha.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    simp only [List.mem_singleton] at hr; subst hr
    exact Region.sub_prefix (by omega)

end

/-- `convert`: the buffer's first `len` bytes are `fixedDigest` of the hash
and its word at `sigOff` is `sig`, and only the buffer, `r1`–`r3` and `r12`
change. -/
theorem convert_ok (wide : Bool) (hp : CPre len s) : WP isa (convert len wide) s (CPost len wide s) := by
  unfold convert
  refine WP.seq (WP.mono (head_ok hp) fun s₁ hh => ?_)
  refine WP.ite s₁.z rfl (fun h => WP.mono (short_ok hp hh wide ?_) fun t ht => cpost_of hp hh ht)
    (fun h => WP.mono (long_ok hp hh wide ?_) fun t ht => cpost_of hp hh ht)
  · rw [hh.z] at h; exact of_decide_eq_true h
  · rw [hh.z] at h; exact Nat.le_of_not_lt (of_decide_eq_false h)

/-! ## The contracts, by register -/

section
variable (I : Spec.Ecdsa.Instance)

/-- The regions of `hashed`'s arguments: `public`, `digest` and `sig` in
`r0`, `r1` (`r2` bytes) and `r3`, `scratch` and the buffer the first two
stack arguments. -/
structure IPre (s : State) : Prop where
  spfit : s.sp.toNat + 8 ≤ 2 ^ 32
  rd : s.rd = [⟨State.addr (s.gpr .r0), 2 * I.curve.len + 1⟩, ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩,
    ⟨State.addr (s.gpr .r3), 2 * I.curve.len⟩, ⟨stackArgAddr s 0, 8⟩]
  wr : s.wr = [⟨State.addr (stackArg s 0), Spec.Ecdsa.scratchWords * 8⟩, ⟨bufA s, 80⟩]
  d0c : (⟨State.addr (s.gpr .r0), 2 * I.curve.len + 1⟩ : Region).Disjoint
    ⟨State.addr (stackArg s 0), Spec.Ecdsa.scratchWords * 8⟩
  d0b : (⟨State.addr (s.gpr .r0), 2 * I.curve.len + 1⟩ : Region).Disjoint ⟨bufA s, 80⟩
  d1c : (⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩ : Region).Disjoint
    ⟨State.addr (stackArg s 0), Spec.Ecdsa.scratchWords * 8⟩
  d1b : (⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩ : Region).Disjoint ⟨bufA s, 80⟩
  d3c : (⟨State.addr (s.gpr .r3), 2 * I.curve.len⟩ : Region).Disjoint
    ⟨State.addr (stackArg s 0), Spec.Ecdsa.scratchWords * 8⟩
  d3b : (⟨State.addr (s.gpr .r3), 2 * I.curve.len⟩ : Region).Disjoint ⟨bufA s, 80⟩
  dcb : (⟨State.addr (stackArg s 0), Spec.Ecdsa.scratchWords * 8⟩ : Region).Disjoint ⟨bufA s, 80⟩
  dca : (⟨State.addr (stackArg s 0), Spec.Ecdsa.scratchWords * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 8⟩
  dba : (⟨bufA s, 80⟩ : Region).Disjoint ⟨stackArgAddr s 0, 8⟩
  f0 : (s.gpr .r0).toNat + (2 * I.curve.len + 1) ≤ 2 ^ 32
  f1 : (s.gpr .r1).toNat + (s.gpr .r2).toNat ≤ 2 ^ 32
  f3 : (s.gpr .r3).toNat + 2 * I.curve.len ≤ 2 ^ 32
  fc : (stackArg s 0).toNat + Spec.Ecdsa.scratchWords * 8 ≤ 2 ^ 32
  fb : (stackArg s 1).toNat + 80 ≤ 2 ^ 32

/-- What the verification that takes the `len` bytes needs, by register:
`public` in `r0`, the bytes in `r1`, `sig` in `r2`, `scratch` in `r3`. -/
structure KPre (s : State) : Prop where
  rd : s.rd = [⟨State.addr (s.gpr .r0), 2 * I.curve.len + 1⟩, ⟨State.addr (s.gpr .r1), I.curve.len⟩,
    ⟨State.addr (s.gpr .r2), 2 * I.curve.len⟩]
  wr : s.wr = [⟨State.addr (s.gpr .r3), Spec.Ecdsa.scratchWords * 8⟩]
  d03 : (⟨State.addr (s.gpr .r0), 2 * I.curve.len + 1⟩ : Region).Disjoint
    ⟨State.addr (s.gpr .r3), Spec.Ecdsa.scratchWords * 8⟩
  d13 : (⟨State.addr (s.gpr .r1), I.curve.len⟩ : Region).Disjoint
    ⟨State.addr (s.gpr .r3), Spec.Ecdsa.scratchWords * 8⟩
  d23 : (⟨State.addr (s.gpr .r2), 2 * I.curve.len⟩ : Region).Disjoint
    ⟨State.addr (s.gpr .r3), Spec.Ecdsa.scratchWords * 8⟩
  f0 : (s.gpr .r0).toNat + (2 * I.curve.len + 1) ≤ 2 ^ 32
  f1 : (s.gpr .r1).toNat + I.curve.len ≤ 2 ^ 32
  f2 : (s.gpr .r2).toNat + 2 * I.curve.len ≤ 2 ^ 32
  f3 : (s.gpr .r3).toNat + Spec.Ecdsa.scratchWords * 8 ≤ 2 ^ 32

/-- The key's bytes, at `r0`. -/
abbrev pkB (s : State) : List Byte := Spec.Ecdsa.bytesAt s.mem (State.addr (s.gpr .r0)) (2 * I.curve.len + 1)

/-- The verification, of the bytes at `pk`, `e` and `sg`, as the function returns it. -/
abbrev vres (m : Mem) (pk : Addr) (e : Nat) (sg : Addr) : BitVec 32 :=
  if Spec.Ecdsa.verify I.curve (Spec.Ecdsa.bytesAt m pk (2 * I.curve.len + 1)) e
    (Spec.Ecdsa.bytesAt m sg (2 * I.curve.len)) then 1 else 0

/-- `hashed`'s contract, by register, with the tables `K`. -/
def hashR (K : List (String × List (BitVec 64))) : Contract isa where
  pre s := IPre I (stripConsts K s) ∧ ConstsOk K 0 s
  post s s' := s'.gpr .r0 =
    vres I s.mem (State.addr (s.gpr .r0)) (Spec.Ecdsa.hashToInt I.curve (hashOf s)) (State.addr (s.gpr .r3))
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
    stackArg s₁ 1 = stackArg s₂ 1 ∧
    (pkB I s₁ ++ hashOf s₁ ++ Spec.Ecdsa.bytesAt s₁.mem (State.addr (s₁.gpr .r3)) (2 * I.curve.len)).map (·.toNat) =
      (pkB I s₂ ++ hashOf s₂ ++ Spec.Ecdsa.bytesAt s₂.mem (State.addr (s₂.gpr .r3)) (2 * I.curve.len)).map (·.toNat) ∧
    ∀ c ∈ K, s₁.syms c.1 = s₂.syms c.1

/-- The contract of the verification that takes the `len` bytes, by register. -/
def coreR (K : List (String × List (BitVec 64))) : Contract isa where
  pre s := KPre I (stripConsts K s) ∧ ConstsOk K 0 s
  post s s' := s'.gpr .r0 =
    vres I s.mem (State.addr (s.gpr .r0))
      (Spec.Ecdsa.hashToInt I.curve (Spec.Ecdsa.bytesAt s.mem (State.addr (s.gpr .r1)) I.curve.len))
      (State.addr (s.gpr .r2))
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    (pkB I s₁ ++ Spec.Ecdsa.bytesAt s₁.mem (State.addr (s₁.gpr .r1)) I.curve.len ++
        Spec.Ecdsa.bytesAt s₁.mem (State.addr (s₁.gpr .r2)) (2 * I.curve.len)).map (·.toNat) =
      (pkB I s₂ ++ Spec.Ecdsa.bytesAt s₂.mem (State.addr (s₂.gpr .r1)) I.curve.len ++
        Spec.Ecdsa.bytesAt s₂.mem (State.addr (s₂.gpr .r2)) (2 * I.curve.len)).map (·.toNat) ∧
    ∀ c ∈ K, s₁.syms c.1 = s₂.syms c.1

end

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
  refine ⟨t, _, he', ⟨fun r hr' => ?_, ?_⟩, by rw [e]; exact hq⟩
  · exact ha.1 r hr'
  · exact ha.2

theorem length_constRegs (K : List (String × List (BitVec 64))) (s : State) :
    (constRegs K s).length = K.length := by simp [constRegs, Abi.constRegions]

theorem covers_self {r : Region} {rs : List Region} (h : r ∈ rs) :
    ∃ r' ∈ rs, ∃ off, r.base = r'.base + BitVec.ofNat 64 off ∧ off + r.len ≤ r'.len :=
  ⟨r, h, 0, by simp, by omega⟩

theorem stackArgAddr_zero (s : State) : stackArgAddr s 0 = State.addr s.sp := by
  simp [stackArgAddr]

/-- The state after `convert` (`u`) and the arguments' loads (`v`). -/
structure VFacts (s u v : State) : Prop where
  r0 : v.gpr .r0 = s.gpr .r0
  r1 : v.gpr .r1 = bf s
  r2 : v.gpr .r2 = s.gpr .r3
  r3 : v.gpr .r3 = stackArg s 0
  mem : v.mem = u.mem
  rd : v.rd = s.rd
  wr : v.wr = s.wr
  sp : v.sp = s.sp
  pres : ∀ r ∈ preserved, v.gpr r = s.gpr r
  syms : v.syms = s.syms

/-- The verification's readable regions: the key, the `len` bytes, the
signature, and the tables. -/
abbrev rdV (I : Spec.Ecdsa.Instance) (K : List (String × List (BitVec 64))) (s : State) : List Region :=
  [⟨State.addr (s.gpr .r0), 2 * I.curve.len + 1⟩, ⟨bufA s, I.curve.len⟩,
    ⟨State.addr (s.gpr .r3), 2 * I.curve.len⟩] ++ constRegs K s

/-- Its writable region: `scratch`. -/
abbrev wrV (s : State) : List Region := [⟨State.addr (stackArg s 0), Spec.Ecdsa.scratchWords * 8⟩]

section
variable {I : Spec.Ecdsa.Instance} {wide : Bool} {K : List (String × List (BitVec 64))}

theorem hs_rd {s : State} (hs : (hashR I K).pre s) :
    s.rd = [⟨State.addr (s.gpr .r0), 2 * I.curve.len + 1⟩, ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩,
      ⟨State.addr (s.gpr .r3), 2 * I.curve.len⟩, ⟨stackArgAddr s 0, 8⟩] ++ constRegs K s := by
  have e := hs.1.rd
  simp only [stripConsts, State.withRegions_rd, State.withRegions_gpr] at e
  rw [← List.take_append_drop (s.rd.length - K.length) s.rd, e, hs.2.1]
  rfl

theorem cpre_of (hL : 8 * I.curve.len = Spec.Ecdsa.nBits I.curve + if wide then 7 else 0)
    (h66 : I.curve.len ≤ 66) {s : State} (hs : (hashR I K).pre s) : CPre I.curve.len s := by
  have hp := hs.1
  have hn := nBits_pos I.curve
  have hwr : s.wr = [⟨State.addr (stackArg s 0), Spec.Ecdsa.scratchWords * 8⟩, ⟨bufA s, 80⟩] := hp.wr
  have hrd := hs_rd hs
  have f1 : (s.gpr .r1).toNat + (s.gpr .r2).toNat ≤ 2 ^ 32 := hp.f1
  refine ⟨by split at hL <;> omega, h66, hp.spfit, ?_, ?_, ?_, hp.d1b.symm, ?_, hp.fb, f1⟩
  · rw [← stackArgAddr_zero]; exact Covers.left (Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hrd]; simp)
  · exact Covers.left (Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [hrd]; simp)
  · exact Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [hwr]; simp
  · rw [← stackArgAddr_zero]; exact hp.dba

end

section
variable {I : Spec.Ecdsa.Instance} {wide : Bool} {K : List (String × List (BitVec 64))}

/-- The stack arguments, after the conversion. -/
theorem stack_post {s u : State} (hp : CPre len s) (hu : CPost len wide s u) {i : Nat} (hi : i < 2) :
    u.mem.readW (State.addr (s.sp + BitVec.ofNat 32 (4 * i))) 32 = stackArg s i := by
  rw [stackArg, stackArgAddr]
  refine Mem.readW_congr fun k hk => ?_
  rw [spA_add hp (by omega), Offset.add_add]
  exact hu.frame _ fun r hr hc => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.stk _ hc (Offset.contains_base _ (by omega) (by omega))

theorem args_ok {s u : State} (hp : CPre len s) (hu : CPost len wide s u) (hsy : u.syms = s.syms) :
    WP isa (.block args) u (VFacts s u) := by
  have h4 : InRegions (u.rd ++ u.wr) (State.addr (s.sp + BitVec.ofNat 32 4)) 4 := by
    rw [hu.rd, hu.wr, spA_add hp (by decide)]; exact VG.Proof.AesGcm.Arm.in_off hp.args (by decide) (by decide)
  have h0 : InRegions (u.rd ++ u.wr) (State.addr (s.sp + BitVec.ofNat 32 0)) 4 := by
    rw [hu.rd, hu.wr, spA_add hp (by decide)]; exact VG.Proof.AesGcm.Arm.in_off hp.args (by decide) (by decide)
  have hb : InRegions (u.rd ++ u.wr) (State.addr (bf s + BitVec.ofNat 32 76)) 4 := by
    rw [hu.rd, hu.wr, bufA_add hp (by decide)]; exact VG.Proof.AesGcm.Arm.in_left (buf_in hp (by decide))
  have e4 : u.mem.readW (State.addr (s.sp + BitVec.ofNat 32 4)) 32 = bf s := stack_post hp hu (i := 1) (by decide)
  have e0 : u.mem.readW (State.addr (s.sp + BitVec.ofNat 32 0)) 32 = stackArg s 0 :=
    stack_post hp hu (i := 0) (by decide)
  have eb : u.mem.readW (State.addr (bf s + BitVec.ofNat 32 76)) 32 = s.gpr .r3 := hu.sigw
  have hsp := hu.sp
  refine WP.mono_syms (Q := fun v => v.gpr .r0 = s.gpr .r0 ∧ v.gpr .r1 = bf s ∧ v.gpr .r2 = s.gpr .r3 ∧
      v.gpr .r3 = stackArg s 0 ∧ v.mem = u.mem ∧ v.rd = s.rd ∧ v.wr = s.wr ∧ v.sp = s.sp ∧
      ∀ r ∈ preserved, v.gpr r = s.gpr r)
    (WP.of_runBlock ⟨_, by arun [args, sigOff, hsp, h4, h0, hb, e4, e0, eb], ?_⟩) ?_
  · refine ⟨?_, ?_, ?_, ?_, rfl, hu.rd, hu.wr, hu.sp, fun r hr => ?_⟩
    · simp only [gpr_setReg]; simpa using hu.regs .r0 (by decide) (by decide) (by decide) (by decide)
    · simp only [gpr_setReg]; simp
    · simp only [gpr_setReg]; simp
    · simp only [gpr_setReg]; simp
    · have h1 : r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simp only [gpr_setReg, h1.1, h1.2.1, h1.2.2.1, ite_false]
      exact hu.regs r h1.1 h1.2.1 h1.2.2.1 h1.2.2.2
  · intro v ⟨a0, a1, a2, a3, am, ard, awr, asp, apr⟩ hsv
    exact ⟨a0, a1, a2, a3, am, ard, awr, asp, apr, hsv.trans hsy⟩

end

section
variable {I : Spec.Ecdsa.Instance} {wide : Bool} {K : List (String × List (BitVec 64))}

theorem vpre (h66 : I.curve.len ≤ 66) {s u v : State} (hs : (hashR I K).pre s)
    (hu : CPost I.curve.len wide s u) (hv : VFacts s u v) :
    (coreR I K).pre (v.withRegions (rdV I K s) (wrV s)) ∧
      Covers (rdV I K s ++ wrV s) (v.rd ++ v.wr) ∧ Covers (wrV s) v.wr := by
  obtain ⟨hp, hk⟩ := hs
  have hrdS := hs_rd (K := K) ⟨hp, hk⟩
  have hwr : s.wr = [⟨State.addr (stackArg s 0), Spec.Ecdsa.scratchWords * 8⟩, ⟨bufA s, 80⟩] := hp.wr
  obtain ⟨va0, va1, va2, va3, vmem, vrd, vwr, vsp, -, hsy'⟩ := hv
  have hL80 : I.curve.len ≤ 80 := by omega
  have fb : (bf s).toNat + 80 ≤ 2 ^ 32 := hp.fb
  have hcR : constRegs K v = constRegs K s := by
    simp only [constRegs]; rw [show symAddr v = symAddr s from funext fun n => by simp only [symAddr, hsy']]
  have hsc : (⟨State.addr (stackArg s 0), Spec.Ecdsa.scratchWords * 8⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  have hbf : (⟨bufA s, 80⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  have hstrip : stripConsts K (v.withRegions (rdV I K s) (wrV s)) =
      (v.withRegions [⟨State.addr (s.gpr .r0), 2 * I.curve.len + 1⟩, ⟨bufA s, I.curve.len⟩,
        ⟨State.addr (s.gpr .r3), 2 * I.curve.len⟩] (wrV s)) := by
    simp only [stripConsts, State.withRegions_rd, State.withRegions_withRegions, State.withRegions_wr]
    congr 1
    rw [List.length_append, length_constRegs, List.take_left' (by simp)]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hstrip]
    refine ⟨by simp only [State.withRegions_rd, State.withRegions_gpr, va0, va1, va2],
      by simp only [State.withRegions_wr, State.withRegions_gpr, va3], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [State.withRegions_gpr, va0, va3]; exact hp.d0c
    · simp only [State.withRegions_gpr, va1, va3]
      exact (hp.dcb.sub_right (Region.sub_prefix hL80)).symm
    · simp only [State.withRegions_gpr, va2, va3]; exact hp.d3c
    · simp only [State.withRegions_gpr, va0]; exact hp.f0
    · simp only [State.withRegions_gpr, va1]; omega
    · simp only [State.withRegions_gpr, va2]; exact hp.f3
    · simp only [State.withRegions_gpr, va3]; exact hp.fc
  · have htab : ∀ t ∈ constRegs K s, t.base.toNat + t.len ≤ 2 ^ abi.ptrBits ∧ (∀ r ∈ s.wr, t.Disjoint r) ∧
        ∀ r ∈ abi.reserved 0 s, t.Disjoint r := hk.2.2.1
    refine ⟨?_, ?_, ?_, ?_⟩
    · show ((rdV I K s).drop ((rdV I K s).length - K.length)) = constRegs K v
      rw [hcR]
      simp only [rdV, List.length_append, length_constRegs, List.length_cons, List.length_nil]
      rw [show 0 + 1 + 1 + 1 + K.length - K.length = 3 by omega, List.drop_left' (by simp)]
    · intro c hc i hi
      show v.mem.readW (symAddr v c.1 + BitVec.ofNat 64 (8 * i)) 64 = c.2.getD i 0
      have ht : (⟨symAddr s c.1, 8 * c.2.length⟩ : Region) ∈ constRegs K s :=
        List.mem_map_of_mem (f := fun c => (⟨symAddr s c.1, 8 * c.2.length⟩ : Region)) hc
      have hfit : (symAddr s c.1).toNat + 8 * c.2.length ≤ 2 ^ 32 := (htab _ ht).1
      rw [show symAddr v c.1 = symAddr s c.1 by simp only [symAddr, hsy'], vmem,
        Frame.readW hu.frame (r := ⟨symAddr s c.1, 8 * c.2.length⟩)
        (Offset.contains_base _ (by omega) (by omega))
        (fun r' hr' => by
          simp only [List.mem_singleton] at hr'; subst hr'
          exact (htab _ ht).2.1 _ hbf) (by decide)]
      exact hk.2.1 c hc i hi
    · intro t ht
      rw [show constRegs K (v.withRegions (rdV I K s) (wrV s)) = constRegs K s from hcR] at ht
      obtain ⟨a, b, c⟩ := htab t ht
      refine ⟨a, fun r hr => b r ?_, fun r hr => c r ?_⟩
      · simp only [State.withRegions_wr, List.mem_singleton] at hr; subst hr; exact hsc
      · simp [abi, stackBelow] at hr
    · intro t ht
      rw [show constRegs K (v.withRegions (rdV I K s) (wrV s)) = constRegs K s from hcR] at ht
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
    (hs : (hashR I K).pre s) (hu : CPost I.curve.len wide s u) (hv : VFacts s u v) :
    Spec.Ecdsa.bytesAt v.mem (bufA s) I.curve.len = fixedDigest I.curve.len wide (hashOf s) ∧
      Spec.Ecdsa.bytesAt v.mem (State.addr (s.gpr .r0)) (2 * I.curve.len + 1) =
        Spec.Ecdsa.bytesAt s.mem (State.addr (s.gpr .r0)) (2 * I.curve.len + 1) ∧
      Spec.Ecdsa.bytesAt v.mem (State.addr (s.gpr .r3)) (2 * I.curve.len) =
        Spec.Ecdsa.bytesAt s.mem (State.addr (s.gpr .r3)) (2 * I.curve.len) := by
  have hp := hs.1
  have f0 := hp.f0
  have f3 := hp.f3
  refine ⟨bytesAt_ext (length_fixedDigest _ _ _) fun i hi => by rw [hv.mem]; exact hu.buf i hi, ?_, ?_⟩
  · rw [hv.mem]; exact bytesAt_frame hu.frame hp.d0b (by omega)
  · rw [hv.mem]; exact bytesAt_frame hu.frame hp.d3b (by omega)

end

theorem hashed_correct (I : Spec.Ecdsa.Instance) {wide : Bool} {K : List (String × List (BitVec 64))}
    {core : Prog isa}
    (hL : 8 * I.curve.len = Spec.Ecdsa.nBits I.curve + if wide then 7 else 0) (h66 : I.curve.len ≤ 66)
    (hcv : ∀ s, (coreR I K).pre s →
      ∃ t s', Exec isa core s t s' ∧ abiPreserved s s' ∧ (coreR I K).post s s')
    (s : State) (hs : (hashR I K).pre s) :
    ∃ t s', Exec isa (hashed I.curve.len wide core) s t s' ∧ abiPreserved s s' ∧ (hashR I K).post s s' := by
  have hW : WP isa (hashed I.curve.len wide core) s fun s' => abiPreserved s s' ∧ (hashR I K).post s s' := by
    unfold hashed
    have hc := cpre_of hL h66 hs
    refine WP.seq (WP.mono_syms (convert_ok wide hc) fun u hu hsy => ?_)
    refine WP.seq (WP.mono (args_ok hc hu hsy) fun v hv => ?_)
    obtain ⟨hpre, hcov, hw⟩ := vpre h66 hs hu hv
    refine WP.mono (WP.narrowRun hcv hpre hcov hw) fun s' ⟨habi, hpost⟩ =>
      ⟨⟨fun r hr => (habi.1 r hr).trans (hv.pres r hr), habi.2.trans hv.sp⟩, ?_⟩
    obtain ⟨e1, e2, e3⟩ := vpost hs hu hv
    have hq : s'.gpr .r0 = vres I v.mem (State.addr (s.gpr .r0))
        (Spec.Ecdsa.hashToInt I.curve (Spec.Ecdsa.bytesAt v.mem (bufA s) I.curve.len)) (State.addr (s.gpr .r3)) := by
      have := hpost
      simp only [coreR, State.withRegions_gpr, State.withRegions_mem, hv.r0, hv.r1, hv.r2] at this
      exact this
    show s'.gpr .r0 = vres I s.mem (State.addr (s.gpr .r0)) (Spec.Ecdsa.hashToInt I.curve (hashOf s))
      (State.addr (s.gpr .r3))
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

/-- The arguments' loads leak only public addresses. -/
theorem args_taint : ∃ hc, (VG.Taint.check taint (argTaint [.r0] 8) (.block args) hc).isSome = true :=
  ⟨_, by taint_decide⟩

section
variable {I : Spec.Ecdsa.Instance} {wide : Bool} {K : List (String × List (BitVec 64))}

/-- Two runs as `hashR` relates them. -/
abbrev HP (s₁ s₂ : State) : Prop := (hashR I K).pre s₁ ∧ (hashR I K).pre s₂ ∧ (hashR I K).pub s₁ s₂

/-- The stack arguments are apart from the writable regions. -/
theorem args_apart {s : State} (hs : (hashR I K).pre s) :
    s.sp.toNat + 8 ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, 8⟩ r := by
  have hp := hs.1
  have hwr : s.wr = [⟨State.addr (stackArg s 0), Spec.Ecdsa.scratchWords * 8⟩, ⟨bufA s, 80⟩] := hp.wr
  refine ⟨hp.spfit, fun r hr => ?_⟩
  rw [hwr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [← stackArgAddr_zero]
  rcases hr with rfl | rfl
  · exact hp.dca.symm
  · exact hp.dba.symm

theorem hashed_ct {core : Prog isa}
    (hL : 8 * I.curve.len = Spec.Ecdsa.nBits I.curve + if wide then 7 else 0) (h66 : I.curve.len ≤ 66)
    (hcv : ∀ s, (coreR I K).pre s →
      ∃ t s', Exec isa core s t s' ∧ abiPreserved s s' ∧ (coreR I K).post s s')
    (hct : ConstantTime isa (coreR I K).pre (coreR I K).pub core)
    (htc : ∃ hc, (VG.Taint.check taint (argTaint [.r0, .r1, .r2, .r3] 8) (convert I.curve.len wide) hc).isSome = true) :
    ConstantTime isa (hashR I K).pre (hashR I K).pub (hashed I.curve.len wide core) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold hashed
  obtain ⟨hc, htc⟩ := htc
  refine RelCT.seq (R := fun u₁ u₂ => ∃ σ₁ σ₂ x₁ x₂ : State, u₁ = x₁ ∧ u₂ = x₂ ∧ HP (I := I) (K := K) σ₁ σ₂ ∧
      (CPost I.curve.len wide σ₁ x₁ ∧ x₁.syms = σ₁.syms) ∧ (CPost I.curve.len wide σ₂ x₂ ∧ x₂.syms = σ₂.syms))
    ?_ (RelCT.seq (R := fun v₁ v₂ => ∃ σ₁ σ₂ x₁ x₂ : State, HP (I := I) (K := K) σ₁ σ₂ ∧
      CPost I.curve.len wide σ₁ x₁ ∧ VFacts σ₁ x₁ v₁ ∧ CPost I.curve.len wide σ₂ x₂ ∧ VFacts σ₂ x₂ v₂) ?_ ?_)
  · refine ((RelCT.taint (A := taint) (argTaint [.r0, .r1, .r2, .r3] 8) (fun s₁ s₂ h => ?_) htc).wpDep
      (F := fun (s t : State) => CPost I.curve.len wide s t ∧ t.syms = s.syms) fun s₁ s₂ h =>
        ⟨WP.mono_syms (convert_ok wide (cpre_of hL h66 h.1)) fun _ a sy => ⟨a, sy⟩,
          WP.mono_syms (convert_ok wide (cpre_of hL h66 h.2.1)) fun _ a sy => ⟨a, sy⟩⟩).mono (fun _ _ h => h)
      fun t₁ t₂ ⟨_, σ₁, σ₂, hp, a₁, a₂⟩ => ⟨σ₁, σ₂, t₁, t₂, rfl, rfl, hp, a₁, a₂⟩
    obtain ⟨h₁, h₂, psp, p0, p1, p2, p3, pa0, pa1, -⟩ := h
    refine agree_argTaint (fun r hr => ?_) psp (args_apart h₁) (args_apart h₂)
      (argMem_of (j := 2) psp (h₁.1.spfit) fun i hi => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
    · rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
      · exact pa0
      · exact pa1
  · refine RelCT.exists_ fun σ₁ => RelCT.exists_ fun σ₂ => RelCT.exists_ fun x₁ => RelCT.exists_ fun x₂ => ?_
    obtain ⟨_, hta⟩ := args_taint
    refine ((RelCT.taint (A := taint) (argTaint [.r0] 8) (fun s₁ s₂ h => ?_) hta).wp
      (F₁ := fun v => (HP (I := I) (K := K) σ₁ σ₂ ∧ CPost I.curve.len wide σ₁ x₁ ∧
        CPost I.curve.len wide σ₂ x₂) ∧ VFacts σ₁ x₁ v) (F₂ := VFacts σ₂ x₂)
      fun u₁ u₂ ⟨e₁, e₂, hp, ⟨c₁, y₁⟩, ⟨c₂, y₂⟩⟩ => by
        subst e₁ e₂
        exact ⟨WP.mono (args_ok (cpre_of hL h66 hp.1) c₁ y₁) fun _ h => ⟨⟨hp, c₁, c₂⟩, h⟩,
          args_ok (cpre_of hL h66 hp.2.1) c₂ y₂⟩).mono
      (fun _ _ h => h) fun v₁ v₂ ⟨_, ⟨⟨hp, c₁, c₂⟩, f₁⟩, f₂⟩ => ⟨σ₁, σ₂, x₁, x₂, hp, c₁, f₁, c₂, f₂⟩
    obtain ⟨e₁, e₂, ⟨h₁, h₂, psp, p0, -, -, -, pa0, pa1, -⟩, ⟨c₁, -⟩, ⟨c₂, -⟩⟩ := h
    subst e₁ e₂
    have q₁ := cpre_of hL h66 h₁
    have q₂ := cpre_of hL h66 h₂
    refine agree_argTaint (fun r hr => ?_) (by rw [c₁.sp, c₂.sp, psp]) ?_ ?_
      (argMem_of (j := 2) (by rw [c₁.sp, c₂.sp, psp]) (by rw [c₁.sp]; exact h₁.1.spfit) fun i hi => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [c₁.regs _ (by decide) (by decide) (by decide) (by decide),
        c₂.regs _ (by decide) (by decide) (by decide) (by decide), p0]
    · rw [c₁.sp, c₁.wr]; exact args_apart h₁
    · rw [c₂.sp, c₂.wr]; exact args_apart h₂
    · have e₁ : stackArg s₁ i = stackArg σ₁ i := by
        rw [stackArg, stackArgAddr, c₁.sp]; exact stack_post q₁ c₁ hi
      have e₂ : stackArg s₂ i = stackArg σ₂ i := by
        rw [stackArg, stackArgAddr, c₂.sp]; exact stack_post q₂ c₂ hi
      rw [e₁, e₂]
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
      · exact pa0
      · exact pa1
  · refine RelCT.inlineV hcv hct fun v₁ v₂ ⟨σ₁, σ₂, x₁, x₂, hp, c₁, f₁, c₂, f₂⟩ => ?_
    obtain ⟨q₁, cv₁, cw₁⟩ := vpre h66 hp.1 c₁ f₁
    obtain ⟨q₂, cv₂, cw₂⟩ := vpre h66 hp.2.1 c₂ f₂
    refine ⟨_, _, _, _, q₁, q₂, ?_, cv₁, cw₁, cv₂, cw₂⟩
    obtain ⟨psp, p0, p1, p2, p3, pa0, pa1, pl, psy⟩ := hp.2.2
    obtain ⟨b₁, k₁, g₁⟩ := vpost hp.1 c₁ f₁
    obtain ⟨b₂, k₂, g₂⟩ := vpost hp.2.1 c₂ f₂
    obtain ⟨ek, eh, eg⟩ := bytes_of_leak (by simp only [pkB, length_bytesAt])
      (by simp only [hashOf, length_bytesAt, p2]) pl
    refine ⟨by simp only [State.withRegions_sp, f₁.sp, f₂.sp, psp],
      by simp only [State.withRegions_gpr, f₁.r0, f₂.r0, p0],
      by simp only [State.withRegions_gpr, f₁.r1, f₂.r1, bf, pa1],
      by simp only [State.withRegions_gpr, f₁.r2, f₂.r2, p3],
      by simp only [State.withRegions_gpr, f₁.r3, f₂.r3, pa0], ?_, fun c hc => ?_⟩
    · simp only [pkB, State.withRegions_mem, State.withRegions_gpr, f₁.r0, f₁.r1, f₁.r2, f₂.r0, f₂.r1, f₂.r2]
      rw [b₁, k₁, g₁, b₂, k₂, g₂]
      simp only [pkB] at ek
      rw [ek, eh, eg]
    · show v₁.syms c.1 = v₂.syms c.1
      rw [f₁.syms, f₂.syms]; exact psy c hc

end

/-! ## The contracts of `Spec/`, by register -/

section
variable {I : Spec.Ecdsa.Instance}

theorem scratch_bytes : Spec.Ecdsa.scratchWords * 8 = 8192 := rfl

theorem stripConsts_nil (s : State) : stripConsts [] s = s := by
  simp [stripConsts, State.withRegions]

theorem constsOk_nil (s : State) : ConstsOk [] 0 s := by
  simp [ConstsOk, constRegs, Abi.constRegions, Abi.constsHeld]

/-- The verification's precondition under `abi`, from `KPre`. -/
theorem core_pre {s : State} (h : KPre I s) : (Proof.Ecdsa.verifyContract I abi 0).pre s := by
  sig_pre [Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig, Spec.Ecdsa.scratchWords,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
  have hwr := h.wr
  rw [scratch_bytes] at hwr
  exact ⟨Nat.le_of_lt s.sp.isLt, h.rd, hwr, h.d03, h.d13, h.d23, h.f0, h.f1, h.f2, h.f3⟩

theorem core_post {s s' : State} (h : (Proof.Ecdsa.verifyContract I abi 0).post s s') :
    s'.gpr .r0 = vres I s.mem (State.addr (s.gpr .r0))
      (Spec.Ecdsa.hashToInt I.curve (Spec.Ecdsa.bytesAt s.mem (State.addr (s.gpr .r1)) I.curve.len))
      (State.addr (s.gpr .r2)) := by
  sig_post [Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig, Spec.Ecdsa.scratchWords,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at h
  rw [BitVec.setWidth_append_eq_right] at h
  exact h

theorem core_pub {s₁ s₂ : State} (h : s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    (pkB I s₁ ++ Spec.Ecdsa.bytesAt s₁.mem (State.addr (s₁.gpr .r1)) I.curve.len ++
        Spec.Ecdsa.bytesAt s₁.mem (State.addr (s₁.gpr .r2)) (2 * I.curve.len)).map (·.toNat) =
      (pkB I s₂ ++ Spec.Ecdsa.bytesAt s₂.mem (State.addr (s₂.gpr .r1)) I.curve.len ++
        Spec.Ecdsa.bytesAt s₂.mem (State.addr (s₂.gpr .r2)) (2 * I.curve.len)).map (·.toNat)) :
    (Proof.Ecdsa.verifyContract I abi 0).pub s₁ s₂ := by
  sig_pub [Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig, Spec.Ecdsa.scratchWords,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
  obtain ⟨psp, p0, p1, p2, p3, pl⟩ := h
  exact ⟨psp, pl, p0, p1, p2, p3⟩

/-- The verification, run as `coreR` describes it, from its proof under `abi`. -/
theorem coreR_nil {core : Prog isa} (h : Verified target core (Proof.Ecdsa.verifyContract I abi 0)) :
    (∀ s, (coreR I []).pre s → ∃ t s', Exec isa core s t s' ∧ abiPreserved s s' ∧ (coreR I []).post s s') ∧
      ConstantTime isa (coreR I []).pre (coreR I []).pub core := by
  obtain ⟨hc, hct, -⟩ := h
  have hp : ∀ s, (coreR I []).pre s → (Proof.Ecdsa.verifyContract I abi 0).pre s := fun s hs => by
    have := hs.1; rw [stripConsts_nil] at this; exact core_pre this
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_⟩
  · obtain ⟨t, s', he, ha, hq⟩ := hc s (hp s hs)
    exact ⟨t, s', he, ha, core_post hq⟩
  · obtain ⟨psp, p0, p1, p2, p3, pl, -⟩ := hpub
    exact hct _ _ _ _ _ _ (hp _ h₁) (hp _ h₂) (core_pub ⟨psp, p0, p1, p2, p3, pl⟩) e₁ e₂

/-- The same, from its proof under `abi.withConsts` of its tables. -/
theorem coreR_cons {c₀ : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}
    {core : Prog isa} (h : Verified target core (Proof.Ecdsa.verifyContract I (abi.withConsts (c₀ :: cs)) 0)) :
    (∀ s, (coreR I (c₀ :: cs)).pre s →
      ∃ t s', Exec isa core s t s' ∧ abiPreserved s s' ∧ (coreR I (c₀ :: cs)).post s s') ∧
      ConstantTime isa (coreR I (c₀ :: cs)).pre (coreR I (c₀ :: cs)).pub core := by
  obtain ⟨hc, hct, -⟩ := h
  have hp : ∀ s, (coreR I (c₀ :: cs)).pre s → (Proof.Ecdsa.verifyContract I (abi.withConsts (c₀ :: cs)) 0).pre s :=
    fun s hs => pre_consts.mpr ⟨core_pre hs.1, hs.2⟩
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_⟩
  · obtain ⟨t, s', he, ha, hq⟩ := hc s (hp s hs)
    exact ⟨t, s', he, ha, core_post (post_consts.mp hq)⟩
  · obtain ⟨psp, p0, p1, p2, p3, pl, psy⟩ := hpub
    exact hct _ _ _ _ _ _ (hp _ h₁) (hp _ h₂)
      (pub_consts.mpr ⟨core_pub ⟨psp, p0, p1, p2, p3, pl⟩, fun c hc => by rw [symAddr, symAddr, psy c hc]⟩)
      e₁ e₂

end

/-! ## `hashed`, under the contracts of `Spec/` -/

section
variable {I : Spec.Ecdsa.Instance}

/-- `verifyHashContract`'s postcondition. -/
abbrev hPost (I : Spec.Ecdsa.Instance) : I.verifyHashSig.Post abi.ptrBits :=
  fun pk digest digestLen sig _scratch m _m' r =>
    r = if Spec.Ecdsa.verify I.curve (Spec.Ecdsa.bytesAt m pk (2 * I.curve.len + 1))
        (Spec.Ecdsa.hashToInt I.curve (Spec.Ecdsa.bytesAt m digest digestLen.toNat))
        (Spec.Ecdsa.bytesAt m sig (2 * I.curve.len))
      then 1 else 0

/-- `verifyHashContract`'s leak. -/
abbrev hLeak (I : Spec.Ecdsa.Instance) : Curry (I.verifyHashSig.words abi.ptrBits) (Mem → List Nat) :=
  fun pk digest digestLen sig _scratch m =>
    (Spec.Ecdsa.bytesAt m pk (2 * I.curve.len + 1) ++ Spec.Ecdsa.bytesAt m digest digestLen.toNat ++
      Spec.Ecdsa.bytesAt m sig (2 * I.curve.len)).map (·.toNat)

/-- `hashed`'s contract under `abi`, with the buffer as a last argument. -/
abbrev innerA (I : Spec.Ecdsa.Instance) : Contract isa :=
  Sig.scratchContract abi I.verifyHashSig "buf" .u8 80 (Curry.const (fun _ => True) _) (hPost I) true 0
    (some (hLeak I))

/-- The same under `abi.withConsts`. -/
abbrev innerK (I : Spec.Ecdsa.Instance) (c₀ : String × List (BitVec 64)) (cs : List (String × List (BitVec 64))) :
    Contract isa :=
  Sig.scratchContract (abi.withConsts (c₀ :: cs)) I.verifyHashSig "buf" .u8 80 (Curry.const (fun _ => True) _)
    (hPost I) true 0 (some (hLeak I))

theorem inner_ipre {s : State} (h : (innerA I).pre s) : IPre I s := by
  sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
    Spec.Ecdsa.Instance.verifyHashSig, Spec.Ecdsa.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr, stackBelow] at h
  obtain ⟨spfit, rd, wr, d0c, d0b, d1c, d1b, d3c, d3b, dcb, dca, dba, f0, f1, f3, fc, fb⟩ := h
  exact ⟨spfit, rd, wr, d0c, d0b, d1c, d1b, d3c, d3b, dcb, dca, dba, f0, f1, f3, fc, fb⟩

theorem inner_post {K : List (String × List (BitVec 64))} {s s' : State} (h : (hashR I K).post s s') :
    (innerA I).post s s' := by
  sig_post [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, hPost,
    Spec.Ecdsa.Instance.verifyHashSig, Spec.Ecdsa.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr]
  rw [BitVec.setWidth_append_eq_right]
  exact h

theorem inner_pub {K : List (String × List (BitVec 64))} {s₁ s₂ : State} (h : (innerA I).pub s₁ s₂)
    (hsy : ∀ c ∈ K, s₁.syms c.1 = s₂.syms c.1) : (hashR I K).pub s₁ s₂ := by
  sig_pub [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, hPost, hLeak, Option.map,
    Spec.Ecdsa.Instance.verifyHashSig, Spec.Ecdsa.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] at h
  obtain ⟨psp, pl, p0, p1, p2, p3, pa0, pa1⟩ := h
  exact ⟨psp, p0, p1, p2, p3, pa0, pa1, pl, hsy⟩

/-- `hashed` under `abi`. -/
theorem hashed_verified_nil {wide : Bool} {core : Prog isa}
    (hL : 8 * I.curve.len = Spec.Ecdsa.nBits I.curve + if wide then 7 else 0) (h66 : I.curve.len ≤ 66)
    (hcore : Verified target core (Proof.Ecdsa.verifyContract I abi 0))
    (htc : ∃ hc, (VG.Taint.check taint (argTaint [.r0, .r1, .r2, .r3] 8) (convert I.curve.len wide) hc).isSome = true)
    (hsat : ∃ s, (innerA I).pre s) :
    Verified target (hashed I.curve.len wide core) (innerA I) := by
  obtain ⟨hcv, hct⟩ := coreR_nil hcore
  refine Verified.of_correct (T := target) (k := hashR I []) (k' := innerA I)
    (hashed_correct I hL h66 hcv) (hashed_ct hL h66 hcv hct htc)
    ⟨fun s hs => ⟨by rw [stripConsts_nil]; exact inner_ipre hs, constsOk_nil s⟩,
      fun s s' _ h => inner_post h, fun s₁ s₂ _ _ h => inner_pub h fun _ h => absurd h List.not_mem_nil, hsat⟩

/-- `hashed` under `abi.withConsts` of the verification's tables. -/
theorem hashed_verified_cons {wide : Bool} {core : Prog isa} {c₀ : String × List (BitVec 64)}
    {cs : List (String × List (BitVec 64))}
    (hL : 8 * I.curve.len = Spec.Ecdsa.nBits I.curve + if wide then 7 else 0) (h66 : I.curve.len ≤ 66)
    (hcore : Verified target core (Proof.Ecdsa.verifyContract I (abi.withConsts (c₀ :: cs)) 0))
    (htc : ∃ hc, (VG.Taint.check taint (argTaint [.r0, .r1, .r2, .r3] 8) (convert I.curve.len wide) hc).isSome = true)
    (hsat : ∃ s, (innerK I c₀ cs).pre s) :
    Verified target (hashed I.curve.len wide core) (innerK I c₀ cs) := by
  obtain ⟨hcv, hct⟩ := coreR_cons hcore
  refine Verified.of_correct (T := target) (k := hashR I (c₀ :: cs)) (k' := innerK I c₀ cs)
    (hashed_correct I hL h66 hcv) (hashed_ct hL h66 hcv hct htc) ⟨fun s hs => ?_,
      fun s s' _ h => post_consts.mpr (inner_post h), fun s₁ s₂ _ _ h => ?_, hsat⟩
  · obtain ⟨h₁, h₂⟩ := pre_consts.mp hs
    exact ⟨inner_ipre h₁, h₂⟩
  · obtain ⟨h₁, h₂⟩ := pub_consts.mp h
    exact inner_pub h₁ fun c hc => symAddr_eq_iff.mp (h₂ c hc)

end

/-! ## `vg_ecdsa_<curve>_verify`, with the buffer on the stack -/

/-- The bytes of a region at `p` read from two memories that agree on the
`n` bytes from `p`. -/
theorem bytesAt_local {m₁ m₂ : Mem} {p : Addr} {n k : Nat}
    (h : ∀ a, (⟨p, n⟩ : Region).Contains a 1 → m₁ a = m₂ a) (hk : k ≤ n) :
    Spec.Ecdsa.bytesAt m₁ p k = Spec.Ecdsa.bytesAt m₂ p k := by
  simp only [Spec.Ecdsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi : i < k := by simpa using hi
  refine h _ ?_
  simp only [Region.Contains]
  rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  have := Nat.mod_le i (2 ^ 64)
  omega

/-- `verifyHashContract`'s postcondition reads memory only within the buffers. -/
theorem post_local (I : Spec.Ecdsa.Instance) : ∀ vs m₁ m₂ m' r, vs.length = (I.verifyHashSig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs I.verifyHashSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (I.verifyHashSig.words abi.ptrBits) (hPost I) vs m₁ m' r →
        Curry.apply (I.verifyHashSig.words abi.ptrBits) (hPost I) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨pk, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 4) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dg, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨sg, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [Spec.Ecdsa.Instance.verifyHashSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.addr] (hPost I) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.addr] (hPost I) _ m₂ m' r
  simp only [Curry.apply, hPost, ArgWord.ofRaw] at h ⊢
  have hdl : Spec.Ecdsa.bytesAt m₁ dg (@BitVec.toNat abi.ptrBits (dl.setWidth 32)) =
      Spec.Ecdsa.bytesAt m₂ dg (@BitVec.toNat abi.ptrBits (dl.setWidth 32)) :=
    bytesAt_local hb.2.1 (by show (dl.setWidth 32).toNat ≤ _; rw [BitVec.toNat_setWidth]; exact Nat.mod_le _ _)
  refine h.trans (ite_of_iff ?_)
  simp only [bytesAt_local hb.1 (Nat.le_refl _), hdl, bytesAt_local hb.2.2.1 (Nat.le_refl _)]

/-- So does its leak. -/
theorem leak_local (I : Spec.Ecdsa.Instance) : Sig.LeakLocalL abi.ptrBits I.verifyHashSig (some (hLeak I)) := by
  intro vs m₁ m₂ hlen hb _
  obtain ⟨pk, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 4) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dg, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dl, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨sg, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨sc, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [Spec.Ecdsa.Instance.verifyHashSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.addr] (hLeak I) _ m₁ =
    Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.addr] (hLeak I) _ m₂
  simp only [Curry.apply, hLeak, ArgWord.ofRaw]
  have hdl : Spec.Ecdsa.bytesAt m₁ dg (@BitVec.toNat abi.ptrBits (dl.setWidth 32)) =
      Spec.Ecdsa.bytesAt m₂ dg (@BitVec.toNat abi.ptrBits (dl.setWidth 32)) :=
    bytesAt_local hb.2.1 (by show (dl.setWidth 32).toNat ≤ _; rw [BitVec.toNat_setWidth]; exact Nat.mod_le _ _)
  simp only [bytesAt_local hb.1 (Nat.le_refl _), hdl, bytesAt_local hb.2.2.1 (Nat.le_refl _)]

/-- The precondition of `verifyHashContract` asks nothing of memory. -/
theorem pre_local (I : Spec.Ecdsa.Instance) : ∀ vs (m₁ m₂ : Mem), vs.length = (I.verifyHashSig.words abi.ptrBits).length →
    (∀ b ∈ Sig.bufs I.verifyHashSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    (∀ r ∈ Sig.lists abi.ptrBits m₁ I.verifyHashSig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (I.verifyHashSig.words abi.ptrBits) (Curry.const (fun _ => True) _) vs m₁ →
      Curry.apply (I.verifyHashSig.words abi.ptrBits) (Curry.const (fun _ => True) _) vs m₂ := by
  intro vs m₁ m₂ _ _ _ _
  rw [Curry.apply_const]
  trivial

theorem pre_leak {A : Abi isa} {sig : Sig} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)} {post : sig.Post A.ptrBits}
    {wa : Bool} {st : Nat} {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}
    {s : State} :
    (sig.contract A pre post wa st leak).pre s ↔ (sig.contract A pre post wa st none).pre s := Iff.rfl

theorem hash_scratchOnStack (I : Spec.Ecdsa.Instance) : ScratchOnStack I.verifyHashSig := rfl
theorem hash_nsaa (I : Spec.Ecdsa.Instance) : nsaa I.verifyHashSig = 4 * 1 := rfl
theorem hash_locs (I : Spec.Ecdsa.Instance) : (locs I.verifyHashSig).all (Loc.ok (4 * 1)) = true := rfl
theorem hash_fits : Fits 1 frameBytes .u8 80 := by decide

/-- `vg_ecdsa_<curve>_verify` under `abi`, from the verification of the `len` bytes. -/
theorem verifyHash_verified_nil {I : Spec.Ecdsa.Instance} {wide : Bool} {core : Prog isa}
    (hL : 8 * I.curve.len = Spec.Ecdsa.nBits I.curve + if wide then 7 else 0) (h66 : I.curve.len ≤ 66)
    (hcore : Verified target core (Proof.Ecdsa.verifyContract I abi 0))
    (htc : ∃ hc, (VG.Taint.check taint (argTaint [.r0, .r1, .r2, .r3] 8) (convert I.curve.len wide) hc).isSome = true)
    (hsat : ∃ s, (I.verifyHashContract abi 96).pre s) :
    Verified target (verifyHash I.curve.len wide core) (I.verifyHashContract abi 96) := by
  obtain ⟨s₀, h₀⟩ := hsat
  exact Verified.stackScratchL (sig := I.verifyHashSig) (nm := "buf") (e := .u8) (n := 80) (m := 1)
    (bytes := frameBytes) (pre := Curry.const (fun _ => True) _) (post := hPost I) (wa := true) (stack := 0)
    (hashed_verified_nil hL h66 hcore htc ⟨_, narrow_pre (hash_scratchOnStack I) (hash_nsaa I) (hash_locs I)
      hash_fits (pre_local I) h₀⟩)
    (hash_scratchOnStack I) (hash_nsaa I) (hash_locs I) hash_fits (pre_local I)
    (fun vs m₁ m₂ m' r hl hb _ => post_local I vs m₁ m₂ m' r hl hb) ⟨s₀, pre_leak.mp h₀⟩ (leak_local I)

section
variable {sig : Sig} {nm : String} {e : Elem} {n : Nat} {c₀ : String × List (BitVec 64)}
  {cs : List (String × List (BitVec 64))} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
  {post : sig.Post abi.ptrBits} {wa : Bool} {stack bytes m : Nat}
  {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- `Verified.stackScratchL` under `abi.withConsts (c₀ :: cs)`, for a
signature without lists of slices: as `Verified.stackScratchWipedC`, without
the wipe. -/
theorem Verified.stackScratchC {c : Prog isa}
    (h : Verified target c (Sig.scratchContract (abi.withConsts (c₀ :: cs)) sig nm e n pre post wa stack leak))
    (hcl : ScratchOnStack sig) (hN : nsaa sig = 4 * m)
    (hloc : (locs sig).all (Loc.ok (4 * m)) = true) (hb : Fits m bytes e n)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      (∀ r ∈ Sig.lists abi.ptrBits m₁ sig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' r →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' r)
    (hsat : ∃ s, (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes)).pre s)
    (hl : Sig.noLists sig.params = true)
    (hleak : Sig.LeakLocalL abi.ptrBits sig leak) :
    Verified target (Impl.StackScratch.Arm.withStackScratch bytes m c)
      (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes) leak) := by
  obtain ⟨hcor, hct, -⟩ := h
  have hlen := armArgs_length sig
  have hrun : ∀ s, (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes) leak).pre s →
      ∃ t s₃, Exec isa c (narrowC sig e n bytes m (c₀ :: cs) s) t s₃ ∧
      (Sig.scratchContract (abi.withConsts (c₀ :: cs)) sig nm e n pre post wa stack leak).post
        (narrowC sig e n bytes m (c₀ :: cs) s) s₃ ∧
      Exec isa (Impl.StackScratch.Arm.withStackScratch bytes m c) s
        (setArgsTrace bytes (s.sp - BitVec.ofNat 32 bytes) m ++ t) (popState bytes s s₃) ∧
      abiPreserved s (popState bytes s s₃) ∧ (popState bytes s s₃).mem = s₃.mem ∧
      (popState bytes s s₃).gpr = s₃.gpr := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrowC_pre hcl hN hloc hb hpre hs)
    exact ⟨t, s₃, he, hq, withStackScratchC_run hcl hN hloc hb hs he ha⟩
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, -, hq, hex, ha, hm, hg⟩ := hrun s hs
    refine ⟨_, _, hex, ha, ?_⟩
    rw [post_consts, post_arm]
    have hq' := (post_arm (sig := sig.withScratch nm e n)
      (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
      (post := Curry.withScratch abi.ptrBits nm e n sig.params post)).mp (post_consts.mp hq)
    obtain ⟨-, -, hargs, -⟩ := narrow_facts (nm := nm) (e := e) (n := n) hcl hN hloc hb (pre_consts.mp hs).1
    simp only [armArgs_stripConsts, stripConsts_sp] at hargs
    rw [armArgs_narrowC, hargs, narrowC_mem] at hq'
    rw [hm, hg]
    have h₃ := Eq.mp (congrFun (congrFun (congrFun (Curry.apply_withScratch abi.ptrBits nm e n
      sig.params post _ _ (hlen s)) _) s₃.mem) _) hq'
    have hag := narrow_agree hcl hN hloc hb (pre_consts.mp hs).1
    simp only [armArgs_stripConsts, stripConsts_mem] at hag
    exact hpost _ _ _ _ _ (hlen s) hag h₃
  · obtain ⟨u₁, _, f₁, _, x₁, _⟩ := hrun s₁ h₁
    obtain ⟨u₂, _, f₂, _, x₂, _⟩ := hrun s₂ h₂
    obtain ⟨hp', hsy⟩ := pub_consts.mp hp
    have hpub : (Sig.scratchContract (abi.withConsts (c₀ :: cs)) sig nm e n pre post wa stack leak).pub
        (narrowC sig e n bytes m (c₀ :: cs) s₁) (narrowC sig e n bytes m (c₀ :: cs) s₂) := by
      refine pub_consts.mpr ⟨(pubL_withRegions _ _ _ _).mpr
        (narrow_pub hcl hN hloc hb (pre_consts.mp h₁).1 (pre_consts.mp h₂).1
          ((pubL_withRegions _ _ _ _).mpr hp') hleak), ?_⟩
      rw [symAddr_congr (narrowC_syms ..), symAddr_congr (narrowC_syms ..)]
      exact hsy
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1, ((pubL_arm hl).mp (pub_consts.mp hp).1).1.1,
      hct _ _ _ _ _ _ (narrowC_pre hcl hN hloc hb hpre h₁) (narrowC_pre hcl hN hloc hb hpre h₂) hpub f₁ f₂]

end

/-- `vg_ecdsa_<curve>_verify` under `abi.withConsts`, from the verification of the `len` bytes. -/
theorem verifyHash_verified_cons {I : Spec.Ecdsa.Instance} {wide : Bool} {core : Prog isa}
    {c₀ : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}
    (hL : 8 * I.curve.len = Spec.Ecdsa.nBits I.curve + if wide then 7 else 0) (h66 : I.curve.len ≤ 66)
    (hcore : Verified target core (Proof.Ecdsa.verifyContract I (abi.withConsts (c₀ :: cs)) 0))
    (htc : ∃ hc, (VG.Taint.check taint (argTaint [.r0, .r1, .r2, .r3] 8) (convert I.curve.len wide) hc).isSome = true)
    (hsat : ∃ s, (I.verifyHashContract (abi.withConsts (c₀ :: cs)) 96).pre s) :
    Verified target (verifyHash I.curve.len wide core) (I.verifyHashContract (abi.withConsts (c₀ :: cs)) 96) := by
  obtain ⟨s₀, h₀⟩ := hsat
  exact Verified.stackScratchC (sig := I.verifyHashSig) (nm := "buf") (e := .u8) (n := 80) (m := 1)
    (bytes := frameBytes) (pre := Curry.const (fun _ => True) _) (post := hPost I) (wa := true) (stack := 0)
    (hashed_verified_cons hL h66 hcore htc ⟨_, narrowC_pre (hash_scratchOnStack I) (hash_nsaa I) (hash_locs I)
      hash_fits (pre_local I) h₀⟩)
    (hash_scratchOnStack I) (hash_nsaa I) (hash_locs I) hash_fits (pre_local I)
    (fun vs m₁ m₂ m' r hl hb => post_local I vs m₁ m₂ m' r hl hb) ⟨s₀, pre_leak.mp h₀⟩ rfl (leak_local I)

/-! ## Satisfiability -/

/-- `s₀`, a state for the verification of the `len` bytes, as one for the
function taking the hash: `len` in `r2`, `sig` in `r3`, `scratch` stored at
`sp`, which may be read. -/
def hashSatState (L : Nat) (s₀ : State) : State :=
  { s₀ with
    gpr := fun r => match r with
      | .r2 => BitVec.ofNat 32 L | .r3 => s₀.gpr .r2 | r => s₀.gpr r
    mem := s₀.mem.writeW (State.addr s₀.sp) (s₀.gpr .r3)
    rd := s₀.rd.take 3 ++ [⟨State.addr s₀.sp, 4⟩] ++ s₀.rd.drop 3 }

section
variable {s₀ : State} (hsp : 96 ≤ s₀.sp.toNat) (hsp4 : s₀.sp.toNat + 4 ≤ 2 ^ 32)
  (hd : ∀ r ∈ s₀.rd ++ s₀.wr, (⟨State.addr s₀.sp - 96#64, 100⟩ : Region).Disjoint r)

theorem addr_sp_toNat (s : State) : (State.addr s.sp).toNat = s.sp.toNat := by
  have := s.sp.isLt
  simp only [State.addr, BitVec.toNat_setWidth]
  omega

include hsp hsp4 in
theorem sat_below_args : (⟨State.addr s₀.sp - 96#64, 96⟩ : Region).Disjoint ⟨State.addr s₀.sp, 4⟩ := by
  have e := VG.Arm.toNat_sub64 (a := State.addr s₀.sp) (k := 96) (by rw [addr_sp_toNat]; exact hsp)
  rw [addr_sp_toNat] at e
  refine Region.disjoint_of_le (.inl ?_) ?_ ?_ <;> simp only [addr_sp_toNat] <;>
    first | (rw [show (96#64 : Addr) = BitVec.ofNat 64 96 from rfl, e]; omega) | omega

theorem sat_args_sub : Region.Sub ⟨State.addr s₀.sp, 4⟩ ⟨State.addr s₀.sp - 96#64, 100⟩ := by
  have h := Offset.sub_base (State.addr s₀.sp - 96#64) (d := 96) (n := 4) (k := 100) (by omega)
  rwa [BitVec.sub_add_cancel] at h

theorem sat_below_sub : Region.Sub ⟨State.addr s₀.sp - 96#64, 96⟩ ⟨State.addr s₀.sp - 96#64, 100⟩ :=
  Region.sub_prefix (by omega)

theorem sat_stackArg {L : Nat} : stackArg (hashSatState L s₀) 0 = s₀.gpr .r3 := by
  simp only [stackArg, stackArgAddr, hashSatState, Nat.mul_zero, BitVec.add_zero]
  exact Mem.readW_writeW_self32 _ _ _

end

section
variable {I : Spec.Ecdsa.Instance}

theorem hashSat_abi (h66 : I.curve.len ≤ 66) {s₀ : State} (h₀ : (Proof.Ecdsa.verifyContract I abi 0).pre s₀)
    (hsp : 96 ≤ s₀.sp.toNat) (hsp4 : s₀.sp.toNat + 4 ≤ 2 ^ 32)
    (hd : ∀ r ∈ s₀.rd ++ s₀.wr, (⟨State.addr s₀.sp - 96#64, 100⟩ : Region).Disjoint r) :
    (I.verifyHashContract abi 96).pre (hashSatState I.curve.len s₀) := by
  sig_pre [Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig, Spec.Ecdsa.scratchWords,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at h₀
  obtain ⟨-, hrd, hwr, d0, d1, d2, f0, f1, f2, f3⟩ := h₀
  have hsa := sat_stackArg (L := I.curve.len) (s₀ := s₀)
  have hA : stackArgAddr (hashSatState I.curve.len s₀) 0 = State.addr s₀.sp := by
    simp [stackArgAddr, hashSatState]
  sig_pre [Spec.Ecdsa.Instance.verifyHashContract, Spec.Ecdsa.Instance.verifyHashSig, Spec.Ecdsa.scratchWords,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, stackBelow]
  have hL : (BitVec.ofNat 32 I.curve.len).toNat = I.curve.len := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  simp only [hashSatState, hL, hsa, hA] at *
  have hdr : ∀ r ∈ s₀.rd, (⟨State.addr s₀.sp - 96#64, 100⟩ : Region).Disjoint r :=
    fun r hr => hd r (List.mem_append_left _ hr)
  have hdw : ∀ r ∈ s₀.wr, (⟨State.addr s₀.sp - 96#64, 100⟩ : Region).Disjoint r :=
    fun r hr => hd r (List.mem_append_right _ hr)
  rw [hrd] at hdr
  rw [hwr] at hdw
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hdr hdw
  refine ⟨hsp, hsp4, by rw [hrd]; rfl, hwr, d0, d1, d2, ?_, ?_, ?_, ?_, ?_, ?_, f0, f1, f2, f3⟩
  · exact (hdw.sub_left sat_args_sub).symm
  · exact (hdr.1.sub_left sat_below_sub)
  · exact (hdr.2.1.sub_left sat_below_sub)
  · exact (hdr.2.2.sub_left sat_below_sub)
  · exact (hdw.sub_left sat_below_sub)
  · exact sat_below_args hsp hsp4

/-- A state satisfying `verifyHashContract`'s precondition under `abi`, from one of
the verification's whose 100 bytes below `sp + 4` are free. -/
theorem hashSat_nil (h66 : I.curve.len ≤ 66) {s₀ : State} (h₀ : (Proof.Ecdsa.verifyContract I abi 0).pre s₀)
    (hsp : 96 ≤ s₀.sp.toNat) (hsp4 : s₀.sp.toNat + 4 ≤ 2 ^ 32)
    (hd : ∀ r ∈ s₀.rd ++ s₀.wr, (⟨State.addr s₀.sp - 96#64, 100⟩ : Region).Disjoint r) :
    ∃ s, (I.verifyHashContract abi 96).pre s :=
  ⟨_, hashSat_abi h66 h₀ hsp hsp4 hd⟩

end

section
variable {I : Spec.Ecdsa.Instance}

/-- The same under `abi.withConsts`. -/
theorem hashSat_cons {c₀ : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}
    (h66 : I.curve.len ≤ 66) {s₀ : State} (h₀ : (Proof.Ecdsa.verifyContract I (abi.withConsts (c₀ :: cs)) 0).pre s₀)
    (hsp : 96 ≤ s₀.sp.toNat) (hsp4 : s₀.sp.toNat + 4 ≤ 2 ^ 32)
    (hd : ∀ r ∈ s₀.rd ++ s₀.wr, (⟨State.addr s₀.sp - 96#64, 100⟩ : Region).Disjoint r) :
    ∃ s, (I.verifyHashContract (abi.withConsts (c₀ :: cs)) 96).pre s := by
  obtain ⟨h₁, hk⟩ := pre_consts.mp h₀
  have h₁' := h₁
  sig_pre [Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig, Spec.Ecdsa.scratchWords,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at h₁'
  obtain ⟨-, hrd₀, -⟩ := h₁'
  have hrd₁ : s₀.rd.take (s₀.rd.length - (c₀ :: cs).length) =
      [⟨State.addr (s₀.gpr .r0), 2 * I.curve.len + 1⟩, ⟨State.addr (s₀.gpr .r1), I.curve.len⟩,
        ⟨State.addr (s₀.gpr .r2), 2 * I.curve.len⟩] := hrd₀
  have hrd : s₀.rd = [⟨State.addr (s₀.gpr .r0), 2 * I.curve.len + 1⟩, ⟨State.addr (s₀.gpr .r1), I.curve.len⟩,
      ⟨State.addr (s₀.gpr .r2), 2 * I.curve.len⟩] ++ constRegs (c₀ :: cs) s₀ := by
    rw [← List.take_append_drop (s₀.rd.length - (c₀ :: cs).length) s₀.rd, hrd₁, hk.1]
  have hsy : (hashSatState I.curve.len s₀).syms = s₀.syms := rfl
  have hcR : constRegs (c₀ :: cs) (hashSatState I.curve.len s₀) = constRegs (c₀ :: cs) s₀ := by
    simp only [constRegs]; rw [show symAddr (hashSatState I.curve.len s₀) = symAddr s₀ from rfl]
  have htrd : (hashSatState I.curve.len s₀).rd =
      [⟨State.addr (s₀.gpr .r0), 2 * I.curve.len + 1⟩, ⟨State.addr (s₀.gpr .r1), I.curve.len⟩,
        ⟨State.addr (s₀.gpr .r2), 2 * I.curve.len⟩, ⟨State.addr s₀.sp, 4⟩] ++ constRegs (c₀ :: cs) s₀ := by
    simp only [hashSatState, hrd]; simp
  have hstrip : stripConsts (c₀ :: cs) (hashSatState I.curve.len s₀) =
      hashSatState I.curve.len (stripConsts (c₀ :: cs) s₀) := by
    have e1 : (hashSatState I.curve.len s₀).rd.take
        ((hashSatState I.curve.len s₀).rd.length - (c₀ :: cs).length) =
        (hashSatState I.curve.len (stripConsts (c₀ :: cs) s₀)).rd := by
      rw [htrd]
      simp only [hashSatState, stripConsts, State.withRegions_rd, hrd₁]
      rw [List.length_append, length_constRegs, List.take_left' (by simp)]
      simp
    simp only [stripConsts] at e1 ⊢
    rw [e1]
    rfl
  have hdr : ∀ r ∈ s₀.rd, (⟨State.addr s₀.sp - 96#64, 100⟩ : Region).Disjoint r :=
    fun r hr => hd r (List.mem_append_left _ hr)
  have hdw : ∀ r ∈ s₀.wr, (⟨State.addr s₀.sp - 96#64, 100⟩ : Region).Disjoint r :=
    fun r hr => hd r (List.mem_append_right _ hr)
  refine ⟨hashSatState I.curve.len s₀, pre_consts.mpr ⟨?_, ?_⟩⟩
  · rw [hstrip]
    refine hashSat_abi h66 h₁ hsp hsp4 fun r hr => ?_
    simp only [stripConsts, State.withRegions_rd, State.withRegions_wr, List.mem_append] at hr
    rcases hr with hr | hr
    · exact hdr r (List.mem_of_mem_take hr)
    · exact hdw r hr
  · obtain ⟨-, k2, k3, k4⟩ := hk
    have htab : ∀ t ∈ constRegs (c₀ :: cs) s₀, (⟨State.addr s₀.sp - 96#64, 100⟩ : Region).Disjoint t :=
      fun t ht => hdr t (by rw [hrd]; exact List.mem_append_right _ ht)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hcR, htrd, List.length_append, length_constRegs]
      simp
    · intro c hc i hi
      have ht : (⟨symAddr s₀ c.1, 8 * c.2.length⟩ : Region) ∈ constRegs (c₀ :: cs) s₀ :=
        List.mem_map_of_mem (f := fun c => (⟨symAddr s₀ c.1, 8 * c.2.length⟩ : Region)) hc
      have hfit : (symAddr s₀ c.1).toNat + 8 * c.2.length ≤ 2 ^ 32 := (k3 _ ht).1
      show (s₀.mem.writeW (State.addr s₀.sp) (s₀.gpr .r3)).readW (symAddr s₀ c.1 + BitVec.ofNat 64 (8 * i)) 64 =
        c.2.getD i 0
      rw [((Frame.refl [⟨State.addr s₀.sp, 4⟩] s₀.mem).writeW (List.mem_singleton_self _) (s₀.gpr .r3)
        (Region.contains_self _ _)).readW (r := ⟨symAddr s₀ c.1, 8 * c.2.length⟩)
        (Offset.contains_base _ (by omega) (by omega))
        (fun r' hr' => by
          simp only [List.mem_singleton] at hr'; subst hr'
          exact ((htab _ ht).symm.sub_right sat_args_sub)) (by decide)]
      exact k2 c hc i hi
    · intro t ht
      rw [hcR] at ht
      obtain ⟨a, b, -⟩ := k3 t ht
      refine ⟨a, fun r hr => b r hr, fun r hr => ?_⟩
      simp only [abi, stackBelow, hashSatState, List.mem_singleton] at hr; subst hr
      exact ((htab t ht).symm.sub_right sat_below_sub)
    · intro t ht
      rw [hcR] at ht
      exact k4 t ht

end

end VG.Proof.Ecdsa.Verify.Arm.Hash
