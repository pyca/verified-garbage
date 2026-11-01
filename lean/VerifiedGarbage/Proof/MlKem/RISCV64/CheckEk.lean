module

public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.MlKem.RISCV64.Common
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Impl.MlKem.RISCV64.Codec
public import VerifiedGarbage.Spec.MlKem.Contract
public import VerifiedGarbage.Proof.MlKem.EkCheck
import VerifiedGarbage.Proof.MlKem.RISCV64.Add
import VerifiedGarbage.Proof.MlKem.RISCV64.Bytes
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Common
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Impl.MlKem.RISCV64.Codec
meta import VerifiedGarbage.Spec.MlKem.Contract
meta import VerifiedGarbage.Proof.MlKem.EkCheck
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Add
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Bytes
meta import VerifiedGarbage.Proof.MlKem.Encode
meta import VerifiedGarbage.Proof.MlKem.Arith
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Spec.MlKem
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# ML-KEM on RISC-V: `vg_mlkem768_check_ek`

The loop counts the 12-bit fields that are at least `q` (`badCount`); the key
passes the check exactly when there are none (`ekCheck768`,
`badCount_eq_zero`). As on PPC64LE (`Proof/MlKem/PPC64LE/CheckEk.lean`), with
`3328` kept in `a5`.
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64.CheckEk

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-! ## The loop body -/

/-- 1 if the field `F < 2¹²` is at least `q`, as `countBad` computes it with `3328` in `a5`. -/
def bad (F : BitVec 64) : BitVec 64 := (3328 - F) >>> 63

/-- The first field of the bytes `b₀`, `b₁`. -/
def fld0 (b₀ b₁ : Byte) : BitVec 64 := ((b₁.setWidth 64 <<< 60) >>> 52) + b₀.setWidth 64

/-- The second field of the bytes `b₁`, `b₂`. -/
def fld1 (b₁ b₂ : Byte) : BitVec 64 := (b₁.setWidth 64 >>> 4) + (b₂.setWidth 64 <<< 4)

/-- What an iteration does. -/
def Step (s : State) (x c a : BitVec 64) (s' : State) : Prop :=
  s'.gpr .a0 = x + 3 ∧ s'.gpr .a1 = c - 1 ∧ s'.gpr .a5 = s.gpr .a5 ∧
    s'.gpr .a2 = a + bad (fld0 (s.mem x) (s.mem (x + BitVec.ofNat 64 1))) +
      bad (fld1 (s.mem (x + BitVec.ofNat 64 1)) (s.mem (x + BitVec.ofNat 64 2))) ∧
    s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.gpr .ra = s.gpr .ra ∧
    ∀ r ∈ preserved, s'.gpr r = s.gpr r

theorem body_ok {s : State} {x c a : BitVec 64} (h3 : s.gpr .a0 = x) (h4 : s.gpr .a1 = c)
    (h5 : s.gpr .a2 = a) (h8 : s.gpr .a5 = 3328)
    (i0 : InRegions (s.rd ++ s.wr) x 1) (i1 : InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 1) 1)
    (i2 : InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 2) 1) :
    WP isa (.block checkEkBody) s (Step s x c a) := by
  crun [checkEkBody, countBad, Step, bad, fld0, fld1, h3, h4, h5, h8, i0, i1, i2, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [setWidth_zero_append]

/-! ## The values -/

/-- 1 if `F` is at least `q`. -/
def badN (F : Nat) : Nat := if F < q then 0 else 1

theorem bad_toNat {F : BitVec 64} (h : F.toNat < 4096) : (bad F).toNat = badN F.toNat := by
  unfold bad badN
  rw [q_eq]
  split <;> bv_omega

theorem byte64 (b : Byte) : (b.setWidth 64).toNat = b.toNat := by
  rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := b.isLt; omega_arith)

theorem fld0_toNat (b₀ b₁ : Byte) : (fld0 b₀ b₁).toNat = b₀.toNat + 256 * (b₁.toNat % 16) := by
  have h₀ := b₀.isLt
  have h₁ := b₁.isLt
  rw [fld0, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, byte64, byte64,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega_arith

theorem fld1_toNat (b₁ b₂ : Byte) : (fld1 b₁ b₂).toNat = b₁.toNat / 16 + 16 * b₂.toNat := by
  have h₁ := b₁.isLt
  have h₂ := b₂.isLt
  rw [fld1, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, byte64, byte64,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega_arith

/-- The fields of the first `i` groups that are at least `q`. -/
def badCount (E : List Byte) : Nat → Nat
  | 0 => 0
  | i + 1 => badCount E i + badN (field0 E i) + badN (field1 E i)

theorem badCount_le (E : List Byte) : ∀ i, badCount E i ≤ 2 * i
  | 0 => Nat.le_refl _
  | i + 1 => by
    have := badCount_le E i
    simp only [badCount, badN]
    split <;> split <;> omega_arith

theorem badN_le (F : Nat) : badN F ≤ 1 := by
  unfold badN; split <;> omega_arith

theorem badN_eq_zero (F : Nat) : badN F = 0 ↔ F < q := by
  unfold badN; split <;> simp_all

theorem badCount_eq_zero (E : List Byte) :
    ∀ i, badCount E i = 0 ↔ ∀ g < i, field0 E g < q ∧ field1 E g < q
  | 0 => by simp [badCount]
  | i + 1 => by
    rw [badCount, Nat.add_eq_zero_iff, Nat.add_eq_zero_iff, badCount_eq_zero E i, badN_eq_zero,
      badN_eq_zero, Nat.forall_lt_succ_right, and_assoc]

/-! ## The loop -/

section
variable (s₀ : State)

abbrev K : Addr := s₀.gpr .a0
abbrev E : List Byte := bytesAt s₀.mem (K s₀) 1184

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [⟨K s₀, 1184⟩]
  wr : s₀.wr = []
  fitK : (K s₀).toNat + 1184 ≤ 2 ^ 64

structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  a0 : s.gpr .a0 = K s₀ + BitVec.ofNat 64 (3 * i)
  a1 : s.gpr .a1 = BitVec.ofNat 64 (384 - i)
  a2 : s.gpr .a2 = BitVec.ofNat 64 (badCount (E s₀) i)
  a5 : s.gpr .a5 = 3328
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  ra : s.gpr .ra = s₀.gpr .ra
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem

theorem step {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 384) {s : State} (h : Inv s₀ i s) :
    WP isa (.block checkEkBody) s fun s' => Inv s₀ (i + 1) s' ∧ (s'.gpr .a1 != 0) = decide (i + 1 ≠ 384) := by
  have fK := hp.fitK
  have eb : ∀ k < 3, K s₀ + BitVec.ofNat 64 (3 * i) + BitVec.ofNat 64 k = K s₀ + BitVec.ofNat 64 (3 * i + k) :=
    fun k _ => ptr_add _ _ _
  have x0 : K s₀ + BitVec.ofNat 64 (3 * i) = K s₀ + BitVec.ofNat 64 (3 * i + 0) := rfl
  have hrw : s.rd ++ s.wr = [⟨K s₀, 1184⟩] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have ib : ∀ k < 3, InRegions (s.rd ++ s.wr) (K s₀ + BitVec.ofNat 64 (3 * i + k)) 1 := fun k hk => by
    rw [hrw]; exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have rb : ∀ k < 3, s.mem (K s₀ + BitVec.ofNat 64 (3 * i + k)) = (E s₀).getD (3 * i + k) 0 := fun k hk => by
    rw [h.mem, bytesAt_getD _ _ (by omega_arith)]
  refine WP.mono (body_ok h.a0 h.a1 h.a2 h.a5 (by rw [x0]; exact ib 0 (by omega_arith))
    (by rw [eb 1 (by omega_arith)]; exact ib 1 (by omega_arith)) (by rw [eb 2 (by omega_arith)]; exact ib 2 (by omega_arith)))
    fun s' ⟨r3, r4, r8, r5, m, rd, wr, sp, ra, pres⟩ =>
    ⟨⟨?_, ?_, ?_, r8.trans h.a5, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, ra.trans h.ra,
      fun r hr => (pres r hr).trans (h.pres r hr), m.trans h.mem⟩, ?_⟩
  · rw [r3]; exact ptr_succ _ 3 i
  · rw [r4]; exact count_sub hi
  · rw [r5, eb 1 (by omega_arith), eb 2 (by omega_arith), x0, rb 0 (by omega_arith), rb 1 (by omega_arith), rb 2 (by omega_arith),
      Nat.add_zero]
    have l0 := ((E s₀).getD (3 * i) 0).isLt
    have l1 := ((E s₀).getD (3 * i + 1) 0).isLt
    have l2 := ((E s₀).getD (3 * i + 2) 0).isLt
    have c0 := bad_toNat (F := fld0 ((E s₀).getD (3 * i) 0) ((E s₀).getD (3 * i + 1) 0))
      (by rw [fld0_toNat]; omega_arith)
    have c1 := bad_toNat (F := fld1 ((E s₀).getD (3 * i + 1) 0) ((E s₀).getD (3 * i + 2) 0))
      (by rw [fld1_toNat]; omega_arith)
    rw [fld0_toNat] at c0
    rw [fld1_toNat] at c1
    have hb := badCount_le (E s₀) i
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_add, c0, c1, BitVec.toNat_ofNat, BitVec.toNat_ofNat, badCount]
    simp only [field0, field1]
    have := badN_le (((E s₀).getD (3 * i) 0).toNat + 256 * (((E s₀).getD (3 * i + 1) 0).toNat % 16))
    have := badN_le (((E s₀).getD (3 * i + 1) 0).toNat / 16 + 16 * ((E s₀).getD (3 * i + 2) 0).toNat)
    omega_arith
  · rw [r4, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hi]
    exact count_nz hi (by decide)

/-- The return value. -/
theorem ret_eq (n : Nat) (hn : n < 2 ^ 63) :
    BitVec.ofNat 64 1 - (BitVec.ofNat 64 0 - BitVec.ofNat 64 n) >>> 63 = if n = 0 then 1 else 0 := by
  by_cases h : n = 0
  · subst h; decide
  · rw [ite_eq_right h]
    bv_omega

theorem end_ok {s : State} {n : Nat} (h5 : s.gpr .a2 = BitVec.ofNat 64 n) :
    WP isa (.block [.li .a3 0, .sub .a3 .a3 .a2, .shift .srl .d .a3 .a3 63, .li .a0 1, .sub .a0 .a0 .a3]) s fun s' =>
      s'.gpr .a0 = BitVec.ofNat 64 1 - (BitVec.ofNat 64 0 - BitVec.ofNat 64 n) >>> 63 ∧ s'.sp = s.sp ∧
        s'.gpr .ra = s.gpr .ra ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  crun [h5, preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]

theorem init_ok {s₀ : State} :
    WP isa (.block ([.li .a1 384, .li .a2 0] ++ liq .a5 3328)) s₀ (Inv s₀ 0) := by
  simp only [liq, Nat.reduceLT, ite_false, List.cons_append, List.nil_append,
    Int.reduceSub, Int.reduceNeg, Int.cast_ofNat_Int]
  crun []
  refine ⟨by simp, by simp, by simp [badCount], by simp; decide, rfl, rfl, rfl, by simp, fun r hr => ?_, rfl⟩
  have : r ≠ .a1 ∧ r ≠ .a2 ∧ r ≠ .a5 := by revert r hr; decide
  simp [this.1, this.2.1, this.2.2]

theorem loop_ok {s₀ : State} (hp : Pre s₀) :
    WP isa checkEk s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp ∧ s'.gpr .ra = s₀.gpr .ra ∧
      s'.gpr .a0 = if badCount (E s₀) 384 = 0 then 1 else 0 := by
  refine WP.seq (WP.mono (init_ok (s₀ := s₀)) fun s h => ?_)
  refine WP.seq (wp_loop_nz (Inv s₀) (N := 384) (by decide) (fun i hi s h => step hp hi h)
    (fun s h => ?_) h)
  have hb := badCount_le (E s₀) 384
  refine WP.mono (end_ok h.a2) fun s' ⟨r3, sp, ra, pres⟩ =>
    ⟨fun r hr => (pres r hr).trans (h.pres r hr), sp.trans h.sp, ra.trans h.ra, ?_⟩
  rw [r3, ret_eq _ (by omega_arith)]

/-! ## Verified -/

theorem pre_of {s : State} (h : (Spec.MlKem.checkEkContract RISCV64.abi).pre s) : Pre s := by
  sig_pre [Spec.MlKem.checkEkContract, Spec.MlKem.checkEkSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨-, h1, h2, h3⟩ := h
  exact ⟨h1, h2, h3⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 1184⟩]
  wr := []

theorem verified :
    Verified RISCV64.target Impl.MlKem.RISCV64.checkEk (Spec.MlKem.checkEkContract RISCV64.abi) := by
  refine ⟨fun s hs => ?_, Add.ctRegs [.a0] (fun s₁ s₂ h => ?_) (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hra, h3⟩ := loop_ok (pre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp, hra⟩, ?_⟩
    sig_post [Spec.MlKem.checkEkContract, Spec.MlKem.checkEkSig, RISCV64.abi, RISCV64.argRegs]
    rw [h3]
    have hE : (E s).length = 1184 := bytesAt_length _ _ _
    by_cases hc : ekCheck mlKem768 (E s) = true
    · rw [ite_eq_left ((badCount_eq_zero _ 384).mpr ((ekCheck768 _ hE).mp hc)), ite_eq_left hc]; rfl
    · rw [ite_eq_right (fun h => hc ((ekCheck768 _ hE).mpr ((badCount_eq_zero _ 384).mp h))),
        ite_eq_right hc]; rfl
  · sig_pub [Spec.MlKem.checkEkContract, Spec.MlKem.checkEkSig, RISCV64.abi, RISCV64.argRegs] at h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact h.2
  · sig_pub [Spec.MlKem.checkEkContract, Spec.MlKem.checkEkSig, RISCV64.abi, RISCV64.argRegs] at h
    exact h.1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlKem.checkEkContract, Spec.MlKem.checkEkSig, RISCV64.abi, RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

end VG.Proof.MlKem.RISCV64.CheckEk
