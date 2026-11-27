module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.Derive.Body
public import VerifiedGarbage.Impl.Ffdh.RISCV64.GenerateKey
public import VerifiedGarbage.Proof.Ffdh.ScanAt
public import VerifiedGarbage.Proof.Ffdh.KeyScalar
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubOut
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.MontCore
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.RISCV64.Ctx

/-!
# FFDH's key generation on RISC-V: the scalar's pieces

`scan_ok`: `scanBody`, without a branch, keeps the first nonzero octet of the
bound (`bptr`) and its index (`scanAt`). `cut_ok`: `rand`'s octets to x, cut
there (`KeyScalar.cut`). `masked_ok`, `maskPre_ok`: x's octets and'ed with
the mask of the status 1. `XR`: what holds of x and `rand`. `ghdr_ok`: the
header's words and the arguments moved.
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.GenerateKey

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64 VG.Impl.Ffdh.RISCV64.GenerateKey
open VG.Proof.Bignum.RISCV64
open VG.Proof.Ffdh.RISCV64
open VG.Proof.Ffdh.KeyScalar (cut cut_length cut_get bnd)
open VG.Proof.Ffdh (scanAt scanAt_succ scanAt_length lead)
open VG.Proof.Bignum (slot)
open VG.Proof.Ffdh.RISCV64.Derive (AR)

/-! ## Masks -/

theorem nz_mask_nat : ∀ n < 256, (0 : BitVec 64) - (((0 : BitVec 64) - BitVec.ofNat 64 n ||| BitVec.ofNat 64 n) >>> 63) =
    bmask (n != 0) := by decide +kernel

/-- The mask of an octet being nonzero. -/
theorem nz_mask (b : Byte) : (0 : BitVec 64) - (((0 : BitVec 64) - b.setWidth 64 ||| b.setWidth 64) >>> 63) =
    bmask (b != 0) := by
  have e : b.setWidth 64 = BitVec.ofNat 64 b.toNat := by
    apply BitVec.eq_of_toNat_eq; simp
  have e2 : (b != 0) = (b.toNat != 0) := by
    cases h : (b != 0) <;> simp_all [BitVec.toNat_eq]
  rw [e, nz_mask_nat _ b.isLt, e2]

theorem mask_or_xor (a f : Bool) : (bmask a ||| bmask f) ^^^ bmask f = bmask (a && !f) := by
  cases a <;> cases f <;> rfl

theorem mask_or' (a f : Bool) : bmask f ||| bmask a = bmask (f || a) := by cases a <;> cases f <;> rfl

/-- A choice by a mask. -/
theorem sel (x y : BitVec 64) (c : Bool) : x ^^^ ((x ^^^ y) &&& bmask c) = if c then y else x := by
  cases c
  · show x ^^^ ((x ^^^ y) &&& 0) = x
    simp
  · show x ^^^ ((x ^^^ y) &&& BitVec.allOnes 64) = y
    rw [BitVec.and_allOnes, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem getD_bytesAt (m : Mem) (P : Addr) {n j : Nat} (hj : j < n) :
    (Spec.Rsa.bytesAt m P n).getD j 0 = m (off P j) := by
  simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, hj, off]

/-! ## The scan -/

/-- The registers the scan writes. -/
def scanRegs : List Reg := [.t2, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4]

/-- What the scan holds after `j` octets. -/
def ScanInv (s : State) (P : Addr) (k j : Nat) (t : State) : Prop :=
  t.gpr .t3 = off P j ∧ t.gpr .t4 = BitVec.ofNat 64 j ∧
    t.gpr .s1 = BitVec.ofNat 64 (scanAt (Spec.Rsa.bytesAt s.mem P k) j).2.1 ∧
    t.gpr .s2 = (scanAt (Spec.Rsa.bytesAt s.mem P k) j).2.2.setWidth 64 ∧
    t.gpr .s3 = bmask (scanAt (Spec.Rsa.bytesAt s.mem P k) j).1 ∧ t.mem = s.mem ∧ Keep scanRegs s t

theorem scanBody_ok {s t : State} {P : Addr} {k j : Nat} (hj : j < k)
    (hrd : InRegions (t.rd ++ t.wr) (off P j) 1) (h : ScanInv s P k j t) :
    WP isa (.block (scanBody ++ ([.addi .t5 .t5 (-1)] : List Instr))) t fun u =>
      ScanInv s P k (j + 1) u ∧ u.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 := by
  obtain ⟨t3, t4, t9, t14, t15, tm, tk⟩ := h
  have hb : t.mem (off P j) = (Spec.Rsa.bytesAt s.mem P k).getD j 0 := by rw [getD_bytesAt _ _ hj, tm]
  unfold ScanInv
  rw [scanAt_succ]
  rcases hr : scanAt (Spec.Rsa.bytesAt s.mem P k) j with ⟨f, i, o⟩
  rw [hr] at t9 t14 t15
  generalize (Spec.Rsa.bytesAt s.mem P k).getD j 0 = b at hb ⊢
  simp only
  have hst : WP isa (.block (scanBody ++ ([.addi .t5 .t5 (-1)] : List Instr))) t
      fun u => (u.gpr .t3 = off P (j + 1) ∧ u.gpr .t4 = BitVec.ofNat 64 (j + 1) ∧
        u.gpr .s1 = (BitVec.ofNat 64 i ^^^ ((BitVec.ofNat 64 i ^^^ BitVec.ofNat 64 j) &&& bmask (b != 0 && !f))) ∧
        u.gpr .s2 = (o.setWidth 64 ^^^ ((o.setWidth 64 ^^^ b.setWidth 64) &&& bmask (b != 0 && !f))) ∧
        u.gpr .s3 = (bmask f ||| bmask (b != 0 && !f)) ∧ u.mem = t.mem ∧
        u.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1) ∧ Keep scanRegs t u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    unfold scanBody
    brun [t3, t4, t9, t14, t15, hrd, add_ofNat_zero, Pub.read1_setWidth, hb, fin64_exec_li_zero]
    rw [nz_mask, mask_or_xor]
    exact ⟨by rw [BitVec.ofNat_add], rfl, rfl, rfl⟩
  refine WP.mono hst fun u ⟨⟨u12, u4, u9, u14, u15, um, u6⟩, ku⟩ =>
    ⟨⟨u12, u4, ?_, ?_, ?_, um.trans tm, (tk.trans ku).mono (by decide)⟩, u6⟩
  · rw [u9, sel]
    cases hc : (!f && b != 0) <;> simp_all [Bool.and_comm]
  · rw [u14, sel]
    cases hc : (!f && b != 0) <;> simp_all [Bool.and_comm]
  · rw [u15, mask_or']
    cases f <;> cases hc : (b != 0) <;> simp_all

theorem sub1_ofNat {k : Nat} (hk : 1 ≤ k) : BitVec.ofNat 64 k - 1#64 = BitVec.ofNat 64 (k - 1) := by
  rw [show k = (k - 1) + 1 by omega_arith, BitVec.ofNat_add, Nat.add_sub_cancel, BitVec.add_sub_cancel]

/-- `scanSetup` and the scan of the `k` octets at `P` (`t3`): `s1` and `s2`
are `lead` of them and its octet. -/
theorem scan_ok {s : State} {P : Addr} {k : Nat} (hk1 : 1 ≤ k) (hk : k < 2 ^ 32)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off P i) 1) (h3 : s.gpr .t3 = off P 0)
    (h4 : s.gpr .a4 = BitVec.ofNat 64 k) :
    WP isa (.block scanSetup) s fun u => WP isa (countLoop .t5 scanBody) u fun t =>
      (t.gpr .s1 = BitVec.ofNat 64 (lead (Spec.Rsa.bytesAt s.mem P k)) ∧
        t.gpr .s2 = ((Spec.Rsa.bytesAt s.mem P k).getD (lead (Spec.Rsa.bytesAt s.mem P k)) 0).setWidth 64 ∧
        t.mem = s.mem) ∧ Keep scanRegs s t := by
  have hlen : (Spec.Rsa.bytesAt s.mem P k).length = k := by simp [Spec.Rsa.bytesAt]
  have hne : Spec.Rsa.bytesAt s.mem P k ≠ [] := fun h => by rw [h] at hlen; simp at hlen; omega_arith
  refine (WP.mono (WP.keep scanRegs (Q := fun u => u.gpr .t3 = off P 0 ∧ u.gpr .t4 = BitVec.ofNat 64 0 ∧
      u.gpr .s1 = BitVec.ofNat 64 (k - 1) ∧ u.gpr .s2 = BitVec.ofNat 64 0 ∧ u.gpr .s3 = BitVec.ofNat 64 0 ∧
      u.mem = s.mem ∧ u.gpr .t5 = BitVec.ofNat 64 k) ?_ (by rfl) (by rfl)) fun u ⟨⟨u12, u4, u9, u14, u15, um, u6⟩, ku⟩ => ?_)
  · unfold scanSetup
    brun [h3, h4, fin64_exec_li_zero, add_ofNat_zero, exec_addi_neg_lit (show 1 ≤ 2048 by decide), sub1_ofNat hk1]
    rfl
  have h0 : ScanInv s P k 0 u := by
    refine ⟨u12, u4, ?_, ?_, ?_, um, ku⟩ <;> rw [scanAt.eq_1]
    · rw [u9, hlen]
    · rw [u14]; rfl
    · rw [u15]; rfl
  refine WP.mono (wp_countdown (cnt := .t5) (N := k) (by omega_arith) (by omega_arith) (ScanInv s P k)
    (fun j hj t ht _ => scanBody_ok hj (by rw [ht.2.2.2.2.2.2.2.1, ht.2.2.2.2.2.2.2.2]; exact hrd j hj) ht) h0 u6)
    fun t ⟨_, _, t9, t14, _, tm, kt⟩ => ?_
  have e := scanAt_length hne
  rw [hlen] at e
  rw [e] at t9 t14
  exact ⟨⟨t9, t14, tm⟩, kt⟩

/-! ## The smear -/

/-! ## Masks of the index -/

theorem lt_mask {j l : Nat} (hj : j < 2 ^ 32) (hl : l < 2 ^ 32) :
    (0 : BitVec 64) - ((BitVec.ofNat 64 j - BitVec.ofNat 64 l) >>> 63) = bmask (decide (j < l)) := by
  have e : (BitVec.ofNat 64 j - BitVec.ofNat 64 l) >>> 63 = BitVec.ofNat 64 (if j < l then 1 else 0) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    split <;> omega_arith
  rw [e]
  by_cases h : j < l <;> simp [h] <;> rfl

theorem eq_mask {j l : Nat} (hj : j < 2 ^ 32) (hl : l < 2 ^ 32) :
    (0 : BitVec 64) - (((BitVec.ofNat 64 j ^^^ BitVec.ofNat 64 l) - BitVec.ofNat 64 1) >>> 63) =
      bmask (decide (j = l)) := by
  have hx : (BitVec.ofNat 64 j ^^^ BitVec.ofNat 64 l) = BitVec.ofNat 64 (j ^^^ l) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.xor_lt_two_pow hj hl) (by decide))]
  have hlt : j ^^^ l < 2 ^ 32 := Nat.xor_lt_two_pow hj hl
  have hz : j ^^^ l = 0 ↔ j = l := ⟨fun h => by
    have := congrArg (· ^^^ l) h
    simpa [Nat.xor_assoc] using this, fun h => by rw [h, Nat.xor_self]⟩
  have e : ((BitVec.ofNat 64 (j ^^^ l)) - BitVec.ofNat 64 1) >>> 63 = BitVec.ofNat 64 (if j = l then 1 else 0) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    simp only [BitVec.toNat_ofNat]
    split <;> omega_arith
  rw [hx, e]
  by_cases h : j = l <;> simp [h] <;> rfl

theorem or_xor_mask (x : BitVec 64) (c : Bool) : (x ||| bmask c) ^^^ bmask c = if c then 0 else x := by
  cases c
  · show (x ||| 0) ^^^ 0 = x
    simp
  · show (x ||| BitVec.allOnes 64) ^^^ BitVec.allOnes 64 = 0
    rw [BitVec.or_allOnes, BitVec.xor_self]; rfl

/-- The octet the cut stores. -/
theorem cut_byte (b t : Byte) (lt eq : Bool) :
    (b.setWidth 64 &&& (if lt then 0 else if eq then t.setWidth 64 else BitVec.ofNat 64 255)).setWidth 8 =
      if lt then 0 else if eq then b &&& t else b := by
  cases lt <;> cases eq <;> simp only [ite_true, ite_false, Bool.false_eq_true] <;>
    apply BitVec.eq_of_toNat_eq <;> simp [BitVec.toNat_and]
  rw [show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt b.isLt]

theorem sel255 (v : BitVec 64) (c : Bool) :
    ((BitVec.ofNat 64 255 ^^^ v) &&& bmask c) ^^^ BitVec.ofNat 64 255 = if c then v else BitVec.ofNat 64 255 := by
  rw [BitVec.xor_comm _ (BitVec.ofNat 64 255), sel]

/-! ## The cut -/

/-- The registers the cut writes. -/
def cutRegs : List Reg := [.t1, .t2, .t4, .t5, .t6, .s0, .s3, .s4, .a0, .a1]

/-- What the cut holds after `j` octets. -/
def CutInv (s : State) (R X : Addr) (k ld : Nat) (tb : Byte) (j : Nat) (t : State) : Prop :=
  t.gpr .t1 = off R j ∧ t.gpr .a0 = off X j ∧ t.gpr .t4 = BitVec.ofNat 64 j ∧ t.gpr .s1 = BitVec.ofNat 64 ld ∧
    t.gpr .s2 = tb.setWidth 64 ∧ Outside X 0 j s.mem t.mem ∧
    (∀ i < j, t.mem (off X i) = (cut (Spec.Rsa.bytesAt s.mem R k) ld tb).getD i 0) ∧ Keep cutRegs s t

theorem cutBody_ok {s t : State} {R X : Addr} {k ld j : Nat} {tb : Byte} (hj : j < k) (hk : k < 2 ^ 32)
    (hld : ld < k) (_hnw : X.toNat + k ≤ 2 ^ 64) (hx : ∀ i < k, InRegions s.wr (off X i) 1)
    (hrd : InRegions (s.rd ++ s.wr) (off R j) 1)
    (hsep : ∀ y, ofs X y < k → off R j ≠ y) (h : CutInv s R X k ld tb j t) :
    WP isa (.block (cutBody ++ ([.addi .t5 .t5 (-1)] : List Instr))) t fun u =>
      CutInv s R X k ld tb (j + 1) u ∧ u.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 := by
  obtain ⟨t24, t25, t4, t9, t14, tout, tx, tk⟩ := h
  have hb : t.mem (off R j) = s.mem (off R j) := by
    refine tout _ (Or.inr ?_)
    by_contra hc
    exact hsep _ (by omega_arith) rfl
  have hrd' : InRegions (t.rd ++ t.wr) (off R j) 1 := by rw [tk.2.1, tk.2.2]; exact hrd
  have hst : InRegions t.wr (off X j) 1 := by rw [tk.2.2]; exact hx j hj
  unfold cutBody
  refine WP.mono (WP.keep cutRegs (Q := fun u => u.gpr .t1 = off R (j + 1) ∧ u.gpr .a0 = off X (j + 1) ∧
      u.gpr .t4 = BitVec.ofNat 64 (j + 1) ∧ u.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 ∧
      u.mem = t.mem.write (off X j) 1 (((s.mem (off R j)).setWidth 64 &&&
        (if decide (j < ld) then 0 else if decide (j = ld) then tb.setWidth 64 else BitVec.ofNat 64 255)).setWidth 8))
      ?_ (by rfl) (by rfl))
    fun u ⟨⟨u24, u25, u4, u6, um⟩, ku⟩ =>
      ⟨⟨u24, u25, u4, ?_, ?_, ?_, ?_, (tk.trans ku).mono (by decide)⟩, u6⟩
  · brun [t24, t25, t4, t9, t14, hrd', hst, add_ofNat_zero, Pub.read1_setWidth, hb, fin64_exec_li_zero,
      Dsa.RISCV64.exec_li_lit (show 255 < 2048 by decide), exec_addi_neg_lit (show 1 ≤ 2048 by decide),
      lt_mask (show j < 2 ^ 32 by omega_arith) (show ld < 2 ^ 32 by omega_arith),
      eq_mask (show j < 2 ^ 32 by omega_arith) (show ld < 2 ^ 32 by omega_arith), sel255, or_xor_mask]
    rw [BitVec.ofNat_add]
  · rw [ku.gpr (by decide), t9]
  · rw [ku.gpr (by decide), t14]
  · rw [um]
    exact (tout.mono (Nat.le_refl _) (by omega_arith)).trans ((write1_outside t.mem X (d := j) _ (by omega_arith)).mono
      (by omega_arith) (by omega_arith))
  · intro i hi
    rw [um]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [write1_outside t.mem X (d := j) _ (by omega_arith) _ (by rw [ofs_off0 X (by omega_arith)]; omega_arith)]
      exact tx i hi
    · rw [write1_self, cut_byte]
      have hl : (Spec.Rsa.bytesAt s.mem R k).length = k := by simp [Spec.Rsa.bytesAt]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [cut_length tb (by omega_arith), hl]; omega_arith),
        Option.getD_some, cut_get tb (by omega_arith) (by omega_arith)]
      have hr : (Spec.Rsa.bytesAt s.mem R k)[i]'(by omega_arith) = s.mem (off R i) := by
        simp [Spec.Rsa.bytesAt, off]
      rw [hr]
      by_cases h1 : i < ld
      · simp [h1]
      · by_cases h2 : i = ld <;> simp [h1, h2]

/-- The cut of `rand`'s `k` octets at `R` (`t1`) into x at `X` (`a0`). -/
theorem cut_ok {s : State} {R X : Addr} {k ld : Nat} {tb : Byte} (hk1 : 1 ≤ k) (hk : k < 2 ^ 32) (hld : ld < k)
    (hnw : X.toNat + k ≤ 2 ^ 64) (hx : ∀ i < k, InRegions s.wr (off X i) 1)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off R i) 1)
    (hsep : ∀ i < k, ∀ y, ofs X y < k → off R i ≠ y) (h1 : s.gpr .t1 = off R 0) (h0 : s.gpr .a0 = off X 0)
    (h4 : s.gpr .t4 = BitVec.ofNat 64 0) (hs1 : s.gpr .s1 = BitVec.ofNat 64 ld) (hs2 : s.gpr .s2 = tb.setWidth 64)
    (h5 : s.gpr .t5 = BitVec.ofNat 64 k) :
    WP isa (countLoop .t5 cutBody) s fun t =>
      (Spec.Rsa.bytesAt t.mem X k = cut (Spec.Rsa.bytesAt s.mem R k) ld tb ∧ Outside X 0 k s.mem t.mem) ∧
        Keep cutRegs s t := by
  refine WP.mono (wp_countdown (cnt := .t5) (N := k) (by omega_arith) (by omega_arith) (CutInv s R X k ld tb)
    (fun j hj t ht _ => cutBody_ok hj hk hld hnw hx (hrd j hj) (hsep j hj) ht)
    ⟨h1, h0, h4, hs1, hs2, Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith), Keep.refl _ _⟩ h5)
    fun t ⟨_, _, _, _, _, tout, tx, kt⟩ => ⟨⟨?_, tout⟩, kt⟩
  have hl : (Spec.Rsa.bytesAt s.mem R k).length = k := by simp [Spec.Rsa.bytesAt]
  apply List.ext_getElem (by rw [cut_length tb (by omega_arith), hl]; simp [Spec.Rsa.bytesAt])
  intro i h1 h2
  have hi : i < k := by simpa [Spec.Rsa.bytesAt] using h1
  have e : (Spec.Rsa.bytesAt t.mem X k)[i] = t.mem (off X i) := by simp [Spec.Rsa.bytesAt, off]
  rw [e, tx i hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]

/-! ## The mask of x -/

/-- The masked loop: x's `k` octets (`a1`) and'ed with the mask of `c` in `s4`. -/
theorem masked_ok {s : State} {X : Addr} {k : Nat} {c : Bool} (hk1 : 1 ≤ k) (hk : k < 2 ^ 32)
    (hnw : X.toNat + k ≤ 2 ^ 64) (hx : ∀ i < k, InRegions s.wr (off X i) 1)
    (h1 : s.gpr .a1 = off X 0) (h4 : s.gpr .s4 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if c then 1 else 0))
    (h5 : s.gpr .t5 = BitVec.ofNat 64 k) :
    WP isa maskLoop s fun t => (Spec.Rsa.bytesAt t.mem X k = (if c then Spec.Rsa.bytesAt s.mem X k else
        List.replicate k 0) ∧ Outside X 0 k s.mem t.mem) ∧ Keep [.t5, .t6, .a1] s t := by
  let Inv : Nat → State → Prop := fun j t => t.gpr .a1 = off X j ∧
    t.gpr .s4 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if c then 1 else 0) ∧
    Outside X 0 j s.mem t.mem ∧ (∀ i < j, t.mem (off X i) = if c then s.mem (off X i) else 0) ∧
    Keep [.t5, .t6, .a1] s t
  refine WP.mono (wp_countdown (cnt := .t5) (N := k) (by omega_arith) (by omega_arith) Inv
    (fun j hj t ⟨t25, t17, tout, tz, tk⟩ _ => ?_) ⟨h1, h4, Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith),
      Keep.refl _ _⟩ h5) fun t ⟨_, _, tout, tz, kt⟩ => ⟨⟨?_, tout⟩, kt⟩
  · have hst : InRegions t.wr (off X j) 1 := by rw [tk.2.2]; exact hx j hj
    have hrd : InRegions (t.rd ++ t.wr) (off X j) 1 := by
      obtain ⟨r, hr, hc⟩ := hst; exact ⟨r, List.mem_append_right _ hr, hc⟩
    have hb : t.mem (off X j) = s.mem (off X j) :=
      tout _ (Or.inr (by rw [ofs_off0 X (by omega_arith)]; omega_arith))
    refine WP.mono (WP.keep [.t5, .t6, .a1] (Q := fun u => u.gpr .a1 = off X (j + 1) ∧
        u.gpr .s4 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if c then 1 else 0) ∧
        u.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 ∧
        u.mem = t.mem.write (off X j) 1 (if c then s.mem (off X j) else 0)) (by
      brun [t25, t17, hrd, hst, add_ofNat_zero, Pub.read1_setWidth, hb, Pub.mask_byte])
      (by rfl) (by rfl)) fun u ⟨⟨u25, u17, u6, um⟩, ku⟩ =>
        ⟨⟨u25, u17, ?_, fun i hi => ?_, (tk.trans ku).mono (by decide)⟩, u6⟩
    · rw [um]
      exact (tout.mono (Nat.le_refl _) (by omega_arith)).trans ((write1_outside t.mem X (d := j) _ (by omega_arith)).mono
        (by omega_arith) (by omega_arith))
    · rw [um]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [write1_outside t.mem X (d := j) _ (by omega_arith) _ (by rw [ofs_off0 X (by omega_arith)]; omega_arith)]
        exact tz i hi
      · exact write1_self _ _ _
  · apply List.ext_getElem (by cases c <;> simp [Spec.Rsa.bytesAt])
    intro i h1 _
    have hi : i < k := by simpa [Spec.Rsa.bytesAt] using h1
    have e : ∀ m : Mem, (Spec.Rsa.bytesAt m X k)[i]'(by simp [Spec.Rsa.bytesAt]; omega_arith) = m (off X i) :=
      fun m => by simp [Spec.Rsa.bytesAt, off]
    rw [e, tz i hi]
    cases c
    · simp
    · simp only [ite_true]; rw [e]

/-! ## x's octets -/

/-- The bound's octets the code scans: q's, or p's. -/
def bptr (D : Addr) (k L : Nat) : Addr := if L = 3 * k then off D (2 * k) else D

/-- The bound's octets the code scans are `KeyScalar.bnd`'s. -/
theorem bptr_bnd (m : Mem) (D : Addr) {k L : Nat} (hL : L = 2 * k ∨ L = 3 * k) :
    Spec.Rsa.bytesAt m (bptr D k L) k = bnd k (Spec.Rsa.bytesAt m D L) := by
  have hl : (Spec.Rsa.bytesAt m D L).length = L := by simp [Spec.Rsa.bytesAt]
  unfold bptr bnd
  rw [hl]
  by_cases hq : L = 3 * k
  · rw [ite_eq_left hq, ite_eq_left hq, VG.Proof.Dsa.bytesAt_slice m D (by omega_arith : 2 * k + k ≤ L)]
  · rw [ite_eq_right hq, ite_eq_right hq, Proof.Ffdh.take_bytesAt m D (by omega_arith)]

/-! ## The scalar -/

/-- x: writable, not wrapping, apart from the working space and the domain;
`rand`: readable and apart from x. -/
structure XR (x : XD) (R : Addr) (s : State) : Prop where
  wX : ∀ i < x.k, InRegions s.wr (off x.X i) 1
  nwX : x.X.toNat + x.k ≤ 2 ^ 64
  sepSX : ∀ y, ofs x.S y < x.Z → x.k ≤ ofs x.X y
  sepDX : ∀ i < x.L, ∀ y, ofs x.X y < x.k → off x.D i ≠ y
  rdR : ∀ i < x.k, InRegions (s.rd ++ s.wr) (off R i) 1
  sepRX : ∀ i < x.k, ∀ y, ofs x.X y < x.k → off R i ≠ y
  sepRS : ∀ i < x.k, ∀ y, ofs x.S y < x.Z → off R i ≠ y
  xl : x.xl = x.k
  sepXO : ∀ i < x.k, ∀ y, ofs x.O y < x.k → off x.X i ≠ y
  sepSO : ∀ y, ofs x.S y < x.Z → x.k ≤ ofs x.O y
  sepOX : ∀ i < x.k, ∀ y, ofs x.X y < x.k → off x.O i ≠ y

theorem XR.keep {x : XD} {R : Addr} {s t : State} (h : XR x R s) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) :
    XR x R t :=
  ⟨by rw [hwr]; exact h.wX, h.nwX, h.sepSX, h.sepDX, by rw [hrd, hwr]; exact h.rdR, h.sepRX, h.sepRS, h.xl,
    h.sepXO, h.sepSO, h.sepOX⟩

/-- `Ctx` after writes to x alone. -/
theorem Ctx.ofX {x : XD} {R : Addr} {s t : State} (h : Ctx x s) (hx : XR x R s) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) (ho : Outside x.X 0 x.k s.mem t.mem) : Ctx x t := by
  have hn := h.scr.nowrap
  have hZ := h.hZ
  unfold slot hdrBytes at hZ
  have hw : ∀ d, d + 8 ≤ 256 → word t.mem x.S d = word s.mem x.S d := fun d hd =>
    Pub.Outside.word_apart ho hx.sepSX (by omega_arith) (by omega_arith) hn
  exact ⟨h.scr.congr hwr, h.k64, h.k1024, h.hL, h.hZ, h.nwO, by rw [hwr]; exact h.outW, h.sepO,
    by rw [hrd, hwr]; exact h.rdD, h.sepD, by rw [hrd, hwr]; exact h.rdY, h.sepY,
    by rw [hrd, hwr]; exact h.rdX, h.sepX, h.xl1, h.xlk,
    by rw [Pub.bytes_apart (Z := x.k) ho (by omega_arith) hx.sepDX]; exact h.bD,
    by rw [hw 0 (by decide)]; exact h.hO, by rw [hw 8 (by decide)]; exact h.hX,
    by rw [hw 16 (by decide)]; exact h.hXL, by rw [hw 24 (by decide)]; exact h.hY⟩

/-- The registers `scalar` writes. -/
def scRegs : List Reg := [.t1, .t2, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4, .a0, .a1]

/-! ## The front -/

/-- The header's words 0–3 and the moved arguments. -/
theorem ghdr_ok {s : State} {S : Addr} {Z : Nat} (hs : Scr s S Z) (hZ : 32 ≤ Z) (h6 : s.gpr .s6 = S) :
    WP isa (.block gkHdr) s fun t =>
      (word t.mem S 0 = s.gpr .a2 ∧ word t.mem S 8 = s.gpr .a0 ∧ word t.mem S 16 = s.gpr .a6 ∧
        word t.mem S 24 = s.gpr .a4 + s.gpr .a6 ∧ t.gpr .t1 = s.gpr .a7 ∧ t.gpr .a3 = s.gpr .a5 ∧
        t.gpr .a5 = s.gpr .a0 ∧ t.gpr .a0 = s.gpr .a2 ∧ t.gpr .a2 = s.gpr .a4 ∧ t.gpr .a4 = s.gpr .a6 ∧
        t.gpr .a6 = s.gpr .a6 ∧ t.gpr .s7 = s.gpr .a4 ∧ t.gpr .s8 = s.gpr .a6 ∧ t.gpr .a1 = s.gpr .a6 ∧
        Outside S 0 32 s.mem t.mem) ∧ Keep [.t2, .t1, .a3, .a5, .a0, .a2, .a4, .s7, .s8, .a1] s t := by
  have hn := hs.nowrap
  have h6' : s.gpr .s6 = off S 0 := by rw [h6]; simp [off]
  have i0 := hs.st (d := 0) (n := 8) (by omega_arith)
  have i8 := hs.st (d := 8) (n := 8) (by omega_arith)
  have i16 := hs.st (d := 16) (n := 8) (by omega_arith)
  have i24 := hs.st (d := 24) (n := 8) (by omega_arith)
  have l0 := hs.al8 (d := 0) (by omega_arith) (by decide)
  have l8 := hs.al8 (d := 8) (by omega_arith) (by decide)
  have l16 := hs.al8 (d := 16) (by omega_arith) (by decide)
  have l24 := hs.al8 (d := 24) (by omega_arith) (by decide)
  have o0 := writeW_outside s.mem S (d := 0) (s.gpr .a2) (by omega_arith)
  have o1 := writeW_outside (s.mem.writeW (off S 0) (s.gpr .a2)) S (d := 8) (s.gpr .a0) (by omega_arith)
  have o2 := writeW_outside ((s.mem.writeW (off S 0) (s.gpr .a2)).writeW (off S 8) (s.gpr .a0)) S (d := 16)
    (s.gpr .a6) (by omega_arith)
  have o3 := writeW_outside (((s.mem.writeW (off S 0) (s.gpr .a2)).writeW (off S 8) (s.gpr .a0)).writeW
    (off S 16) (s.gpr .a6)) S (d := 24) (s.gpr .a4 + s.gpr .a6) (by omega_arith)
  refine WP.mono (WP.keep [.t2, .t1, .a3, .a5, .a0, .a2, .a4, .s7, .s8, .a1] (Q := fun t => t.mem =
      (((s.mem.writeW (off S 0) (s.gpr .a2)).writeW (off S 8) (s.gpr .a0)).writeW (off S 16) (s.gpr .a6)).writeW
        (off S 24) (s.gpr .a4 + s.gpr .a6) ∧ t.gpr .t1 = s.gpr .a7 ∧ t.gpr .a3 = s.gpr .a5 ∧
      t.gpr .a5 = s.gpr .a0 ∧ t.gpr .a0 = s.gpr .a2 ∧ t.gpr .a2 = s.gpr .a4 ∧ t.gpr .a4 = s.gpr .a6 ∧
      t.gpr .a6 = s.gpr .a6 ∧ t.gpr .s7 = s.gpr .a4 ∧ t.gpr .s8 = s.gpr .a6 ∧ t.gpr .a1 = s.gpr .a6) ?_ (by rfl) (by rfl))
    fun t ⟨⟨tm, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10⟩, kt⟩ =>
      ⟨⟨?_, ?_, ?_, ?_, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ?_⟩, kt⟩
  · unfold gkHdr
    brun [h6', i0, i8, i16, i24, l0, l8, l16, l24]
    simp [off]
  · rw [tm, o3.word (by omega_arith) (by omega_arith), o2.word (by omega_arith) (by omega_arith),
      o1.word (by omega_arith) (by omega_arith)]
    exact word_writeW_self _ _ _ _
  · rw [tm, o3.word (by omega_arith) (by omega_arith), o2.word (by omega_arith) (by omega_arith)]
    exact word_writeW_self _ _ _ _
  · rw [tm, o3.word (by omega_arith) (by omega_arith)]
    exact word_writeW_self _ _ _ _
  · rw [tm]; exact word_writeW_self _ _ _ _
  · rw [tm]
    exact (((o0.mono (by omega_arith) (by omega_arith)).trans (o1.mono (by omega_arith) (by omega_arith))).trans
      (o2.mono (by omega_arith) (by omega_arith))).trans (o3.mono (by omega_arith) (by omega_arith))

/-! ## The mask's start -/

theorem st_mask : ∀ n < 4, (((0 : BitVec 64) - (BitVec.ofNat 64 n - BitVec.ofNat 64 1) |||
    (BitVec.ofNat 64 n - BitVec.ofNat 64 1)) >>> 63) - BitVec.ofNat 64 1 =
      BitVec.ofNat 64 0 - BitVec.ofNat 64 (if n = 1 then 1 else 0) := by decide

/-- `maskPre`: the mask of the status 1, and x's address and length from the
header. -/
theorem maskPre_ok {s : State} {S X : Addr} {Z k n : Nat} (hs : Scr s S Z) (hZ : 256 ≤ Z) (h6 : s.gpr .s6 = S)
    (h0 : s.gpr .a0 = BitVec.ofNat 64 n) (hn : n < 4) (hX : word s.mem S 8 = off X 0)
    (hK : word s.mem S 16 = BitVec.ofNat 64 k) :
    WP isa (.block maskPre) s fun t =>
      (t.gpr .s4 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if n = 1 then 1 else 0) ∧ t.gpr .a1 = off X 0 ∧
        t.gpr .t5 = BitVec.ofNat 64 k ∧ t.mem = s.mem) ∧ Keep [.t2, .t3, .s4, .a1, .t5] s t := by
  have hn' := hs.nowrap
  have h6' : s.gpr .s6 = off S 0 := by rw [h6]; simp [off]
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold maskPre
  brun [h6', h0, fin64_exec_li_zero, exec_addi_neg_lit (show 1 ≤ 2048 by decide),
    hs.ld (d := 8) (n := 8) (by omega_arith), hs.ld (d := 16) (n := 8) (by omega_arith),
    hs.al8 (d := 8) (by omega_arith) (by decide), hs.al8 (d := 16) (by omega_arith) (by decide)]
  exact ⟨st_mask n hn, hX, hK⟩

/-- Writes to x leave the working space. -/
theorem outX_scr {X S : Addr} {k Z : Nat} {m m' : Mem} (ho : Outside X 0 k m m')
    (hsep : ∀ y, ofs S y < Z → k ≤ ofs X y) : Outside S Z (2 ^ 64) m m' := fun y hy =>
  ho y (Or.inr (by
    rw [Nat.zero_add]
    rcases hy with h | h
    · exact hsep y h
    · have := (y - S).isLt; simp only [ofs] at h; omega_arith))

end VG.Proof.Ffdh.RISCV64.GenerateKey
