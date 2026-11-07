module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.Derive.Body
public import VerifiedGarbage.Impl.Ffdh.RISCV64.GenerateKey
public import VerifiedGarbage.Proof.Ffdh.ScanAt
public import VerifiedGarbage.Proof.Ffdh.KeyScalar
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubMid
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
import VerifiedGarbage.Proof.Ffdh.RISCV64.Li

/-!
# `vg_ffdh_generate_key` on RISC-V: the scalar, and the front

`scan_ok`: `scanBody`, without a branch, keeps the first nonzero octet of the
bound and its index (`scanAt`). `smear_ok`: the bits of that octet below its
top one (`smearN`). `cut_ok`: `rand`'s octets to x, cut there
(`KeyScalar.cut`), so that x is `scalarOfOctets` of `rand` (`gkOct_eq`).
`masked_ok`: x's octets and'ed with a mask. `gkContract`, `gxOf` and
`gkFront_ok`: the function, its public data as `vg_ffdh_derive_public`'s
(`XD`), and its front.
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.GenerateKey

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64 VG.Impl.Ffdh.RISCV64.GenerateKey
open VG.Proof.Bignum.RISCV64
open VG.Proof.Ffdh.RISCV64
open VG.Proof.Ffdh.KeyScalar (smearN smearN_eq smearN_lt cut cut_length cut_get cut_eq bnd bnd_length)
open VG.Proof.Ffdh (scanAt scanAt_succ scanAt_length lead)
open VG.Proof.Bignum (slot)
open VG.Proof.Ffdh.RISCV64.Derive (AR)
open VG.Proof.Bignum.RISCV64.Pub (savW savR)

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

theorem smear_nat : ∀ n < 256, (let a := BitVec.ofNat 64 n ||| BitVec.ofNat 64 n >>> 1
    let b := a ||| a >>> 2
    b ||| b >>> 4) = BitVec.ofNat 64 (smearN n) := by decide +kernel

/-- `smear`: `s2 :=` `smearN` of its octet. -/
theorem smear_ok (s : State) {b : Byte} (h2 : s.gpr .s2 = b.setWidth 64) :
    WP isa (.block smear) s fun t =>
      (t.gpr .s2 = (BitVec.ofNat 8 (smearN b.toNat)).setWidth 64 ∧ t.mem = s.mem) ∧ Keep [.s2, .t6] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold smear
  brun [h2]
  have e : b.setWidth 64 = BitVec.ofNat 64 b.toNat := by apply BitVec.eq_of_toNat_eq; simp
  have e2 : (BitVec.ofNat 8 (smearN b.toNat)).setWidth 64 = BitVec.ofNat 64 (smearN b.toNat) := by
    apply BitVec.eq_of_toNat_eq
    have := smearN_lt _ b.isLt
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_arith
  rw [e, e2]
  exact smear_nat _ b.isLt

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
      fin64_exec_li_lit (show 255 < 2048 by decide), exec_addi_neg_lit (show 1 ≤ 2048 by decide),
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

/-- The smeared octet of the bound's first nonzero one. -/
def smeared (m : Mem) (D : Addr) (k L : Nat) : Byte :=
  BitVec.ofNat 8 (smearN ((Spec.Rsa.bytesAt m (bptr D k L) k).getD (lead (Spec.Rsa.bytesAt m (bptr D k L) k)) 0).toNat)

/-- x's octets: `rand`'s cut at the bound's first nonzero octet. -/
def gkOct (m : Mem) (D R : Addr) (k L : Nat) : List Byte :=
  cut (Spec.Rsa.bytesAt m R k) (lead (Spec.Rsa.bytesAt m (bptr D k L) k)) (smeared m D k L)

/-- The bound's octets the code scans are `KeyScalar.bnd`'s. -/
theorem bptr_bnd (m : Mem) (D : Addr) {k L : Nat} (hL : L = 2 * k ∨ L = 3 * k) :
    Spec.Rsa.bytesAt m (bptr D k L) k = bnd k (Spec.Rsa.bytesAt m D L) := by
  have hl : (Spec.Rsa.bytesAt m D L).length = L := by simp [Spec.Rsa.bytesAt]
  unfold bptr bnd
  rw [hl]
  by_cases hq : L = 3 * k
  · rw [ite_eq_left hq, ite_eq_left hq, VG.Proof.Dsa.bytesAt_slice m D (by omega_arith : 2 * k + k ≤ L)]
  · rw [ite_eq_right hq, ite_eq_right hq, Proof.Ffdh.take_bytesAt m D (by omega_arith)]

theorem gkOct_length (m : Mem) (D R : Addr) {k L : Nat} (hk : 1 ≤ k) : (gkOct m D R k L).length = k := by
  have hl : (Spec.Rsa.bytesAt m (bptr D k L) k).length = k := by simp [Spec.Rsa.bytesAt]
  have hne : Spec.Rsa.bytesAt m (bptr D k L) k ≠ [] := fun he => by rw [he] at hl; simp at hl; omega_arith
  have := Proof.Ffdh.lead_lt hne
  have hR : (Spec.Rsa.bytesAt m R k).length = k := by simp [Spec.Rsa.bytesAt]
  unfold gkOct
  rw [cut_length _ (by rw [hR]; omega_arith), hR]

/-- x's octets are the scalar of the attempt. -/
theorem gkOct_eq (m : Mem) (D R : Addr) {k L : Nat} (hk : 1 ≤ k) (hL : L = 2 * k ∨ L = 3 * k)
    (hp : L ≠ 3 * k → Spec.Rsa.os2ip (Spec.Rsa.bytesAt m D k) % 2 = 1 ∧ 1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt m D k)) :
    Spec.Rsa.os2ip (gkOct m D R k L) =
      Spec.Ffdh.scalarOfOctets (Spec.Ffdh.domainOf k (Spec.Rsa.bytesAt m D L)) (Spec.Rsa.bytesAt m R k) := by
  have hl : (Spec.Rsa.bytesAt m D L).length = L := by simp [Spec.Rsa.bytesAt]
  have hd : (Spec.Rsa.bytesAt m D L).length = 2 * k ∨ (Spec.Rsa.bytesAt m D L).length = 3 * k := by rw [hl]; exact hL
  unfold gkOct smeared
  rw [bptr_bnd m D hL]
  refine cut_eq hk hd (fun h3 => ?_) (by simp [Spec.Rsa.bytesAt]) ?_
  · rw [Proof.Ffdh.take_bytesAt m D (by omega_arith)]; exact hp (by rw [hl] at h3; exact h3)
  · rw [Proof.Ffdh.getD_of (Proof.Ffdh.lead_lt (by
        intro he; have := bnd_length hd; rw [he] at this; simp at this; omega_arith))]
    have hlt := BitVec.isLt ((bnd k (Spec.Rsa.bytesAt m D L))[lead (bnd k (Spec.Rsa.bytesAt m D L))]'(Proof.Ffdh.lead_lt (by
        intro he; have := bnd_length hd; rw [he] at this; simp at this; omega_arith)))
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (smearN_lt _ hlt), smearN_eq _ hlt]

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

/-- `boundPtr`: `t3 :=` the bound's octets. -/
theorem bp_ok {x : XD} {s : State} (hc : Ctx x s) (ha : AR x s) :
    WP isa boundPtr s fun t => (t.gpr .t3 = off (bptr x.D x.k x.L) 0 ∧ t.mem = s.mem) ∧ Keep [.t2, .t3] s t := by
  have hk' := hc.k1024
  have hL := hc.hL
  refine WP.keep _ ?_ (by rfl)
  unfold boundPtr
  refine WP.seq (WP.mono (WP.keep [.t2] (Q := fun t => (t.gpr .t2 == 0) = decide (x.L = 3 * x.k) ∧ t.mem = s.mem)
    (by unfold hasQ; brun [ha.a3, ha.a4]; exact Derive.sub_3k_zero (by omega_arith) (by omega_arith)) (by rfl) (by rfl))
    fun s₁ ⟨⟨t2, m1⟩, k1⟩ => ?_)
  refine WP.ite (s₁.gpr .t2 == 0) (Steps.eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · rw [t2, decide_eq_true_eq] at hb
    refine WP.mono (WP.keep [.t3] (Q := fun t => t.gpr .t3 = off (off x.D (2 * x.k)) 0 ∧ t.mem = s₁.mem)
      (by brun [(k1.gpr (r := .a2) (by decide)).trans ha.a2, (k1.gpr (r := .a4) (by decide)).trans ha.a4,
        Derive.q_addr]) (by rfl) (by rfl)) fun t ⟨⟨t3, mt⟩, _⟩ => ⟨?_, by rw [mt, m1]⟩
    rw [t3]; unfold bptr; rw [ite_eq_left hb]
  · have hq : ¬ x.L = 3 * x.k := by rw [t2] at hb; simpa using hb
    refine WP.mono (WP.keep [.t3] (Q := fun t => t.gpr .t3 = off x.D 0 ∧ t.mem = s₁.mem)
      (by brun [(k1.gpr (r := .a2) (by decide)).trans ha.a2, add_ofNat_zero]) (by rfl) (by rfl))
      fun t ⟨⟨t3, mt⟩, _⟩ => ⟨?_, by rw [mt, m1]⟩
    rw [t3]; unfold bptr; rw [ite_eq_right hq]

/-- The registers `scalar` writes. -/
def scRegs : List Reg := [.t1, .t2, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4, .a0, .a1]

/-- `scalar`: x's octets the cut of `rand`'s (`gkOct`), and `s0 := 0`. -/
theorem scalar_ok {x : XD} {R : Addr} {s : State} (hb : Base x s) (ha : AR x s) (hx : XR x R s)
    (h1 : s.gpr .t1 = R) :
    WP isa scalar s fun t =>
      (Spec.Rsa.bytesAt t.mem x.X x.k = gkOct s.mem x.D R x.k x.L ∧ Outside x.X 0 x.k s.mem t.mem ∧
        t.gpr .s0 = 0) ∧ Keep scRegs s t := by
  have hc := hb.ctx
  have hk := hc.k64
  have hk' := hc.k1024
  have hL := hc.hL
  unfold scalar
  refine WP.seq (WP.mono (bp_ok hc ha) fun s₂ ⟨⟨b3, m2⟩, k2⟩ => ?_)
  have hrdB : ∀ i < x.k, InRegions (s₂.rd ++ s₂.wr) (off (bptr x.D x.k x.L) i) 1 := fun i hi => by
    rw [k2.2.1, k2.2.2]
    unfold bptr
    by_cases hq : x.L = 3 * x.k
    · rw [ite_eq_left hq, Derive.off_off]; exact hc.rdD _ (by omega_arith)
    · rw [ite_eq_right hq]; exact hc.rdD _ (by omega_arith)
  refine WP.seq (WP.mono (scan_ok (P := bptr x.D x.k x.L) (by omega_arith) (by omega_arith) hrdB b3
    ((k2.gpr (by decide)).trans ha.a4)) fun u hu => WP.seq (WP.mono hu fun s₃ ⟨⟨h31, h32, m3⟩, k3⟩ => ?_))
  have k23 := k2.trans k3
  rw [m2] at h31 h32
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (smear_ok s₃ h32) fun s₄ ⟨⟨h42, m4⟩, k4⟩ => ?_
  have k24 := k23.trans k4
  refine WP.mono (WP.keep [.t5, .t4, .a0] (Q := fun u => u.gpr .t5 = BitVec.ofNat 64 x.k ∧
    u.gpr .t4 = BitVec.ofNat 64 0 ∧ u.gpr .a0 = off x.X 0 ∧ u.mem = s₄.mem)
    (by unfold cutSetup; brun [(k24.gpr (r := .a4) (by decide)).trans ha.a4, (k24.gpr (r := .a5) (by decide)).trans ha.a5,
      fin64_exec_li_zero, add_ofNat_zero]; rfl) (by rfl) (by rfl))
    fun s₅ ⟨⟨h55, h54, h50, m5⟩, k5⟩ => ?_
  have k25 := k24.trans k5
  have hm5 : s₅.mem = s.mem := by rw [m5, m4, m3, m2]
  refine WP.seq (WP.mono (cut_ok (R := R) (X := x.X) (k := x.k) (ld := lead (Spec.Rsa.bytesAt s.mem (bptr x.D x.k x.L) x.k))
    (tb := smeared s.mem x.D x.k x.L) (by omega_arith) (by omega_arith)
    (by
      have hl : (Spec.Rsa.bytesAt s.mem (bptr x.D x.k x.L) x.k).length = x.k := by simp [Spec.Rsa.bytesAt]
      have hne : Spec.Rsa.bytesAt s.mem (bptr x.D x.k x.L) x.k ≠ [] := fun he => by rw [he] at hl; simp at hl; omega_arith
      have := Proof.Ffdh.lead_lt hne
      omega_arith)
    hx.nwX (by rw [k25.2.2]; exact hx.wX) (by rw [k25.2.1, k25.2.2]; exact hx.rdR) hx.sepRX
    (by rw [k25.gpr (by decide), h1]; simp [off]) h50 h54
    ((k5.gpr (by decide)).trans ((k4.gpr (by decide)).trans h31))
    ((k5.gpr (by decide)).trans h42) h55) fun s₆ ⟨⟨h6b, o6⟩, k6⟩ => ?_)
  refine WP.mono (WP.keep [.s0] (Q := fun u => u.gpr .s0 = 0 ∧ u.mem = s₆.mem) (by brun [fin64_exec_li_zero])
    (by rfl) (by rfl)) fun t ⟨⟨t0, mt⟩, kt⟩ => ⟨⟨?_, ?_, t0⟩, ((k25.trans k6).trans kt).mono (by decide)⟩
  · rw [mt, h6b, hm5]; rfl
  · rw [mt, ← hm5]; exact o6

/-! ## The function -/

/-- The arguments on the stack: `rand_len`, `scratch` and `scratch_len`. -/
abbrev gkStack (s : State) : Region := ⟨stackArgAddr s 0, 24⟩

/-- The status of the attempt. -/
def gkStatus (s : State) : Nat :=
  let a := Spec.Ffdh.domainOf (s.gpr .a6).toNat (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat)
  Spec.Ffdh.keyStatus a (Spec.Ffdh.scalarOfOctets a (Spec.Rsa.bytesAt s.mem (s.gpr .a7) (stackArg s 0).toNat))

/-- What timing may depend on: the domain and the status. -/
def gkLeak (s : State) : List Nat :=
  (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat).map (·.toNat) ++ [gkStatus s]

/-- `vg_ffdh_generate_key`, on the registers and the stack. -/
def gkContract : Contract isa where
  pre s :=
    let x : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let y : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
    let dom : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
    let rand : Region := ⟨s.gpr .a7, (stackArg s 0).toNat⟩
    let scr : Region := ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
    s.rd = [dom, rand, gkStack s] ∧ s.wr = [x, y, scr] ∧
      x.Disjoint y ∧ x.Disjoint dom ∧ x.Disjoint rand ∧ x.Disjoint scr ∧ x.Disjoint (gkStack s) ∧
      y.Disjoint dom ∧ y.Disjoint rand ∧ y.Disjoint scr ∧ y.Disjoint (gkStack s) ∧
      dom.Disjoint scr ∧ rand.Disjoint scr ∧ scr.Disjoint (gkStack s) ∧
      (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
      (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64 ∧ (s.gpr .a7).toNat + (stackArg s 0).toNat ≤ 2 ^ 64 ∧
      (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Ffdh.pLenValid (s.gpr .a6).toNat ∧ Spec.Ffdh.domainLenValid (s.gpr .a6).toNat (s.gpr .a5).toNat ∧
      (s.gpr .a1).toNat = (s.gpr .a6).toNat ∧ (s.gpr .a3).toNat = (s.gpr .a6).toNat ∧
      (stackArg s 0).toNat = (s.gpr .a6).toNat ∧ Spec.Rsa.scratchWords (s.gpr .a6).toNat ≤ (stackArg s 2).toNat ∧
      (stackArg s 1).toNat % 8 = 0 ∧ s.sp.toNat % 16 = 0
  post s t :=
    let dom := Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat
    let a := Spec.Ffdh.domainOf (s.gpr .a6).toNat dom
    let sc := Spec.Ffdh.scalarOfOctets a (Spec.Rsa.bytesAt s.mem (s.gpr .a7) (stackArg s 0).toNat)
    Spec.Ffdh.domainValid (s.gpr .a6).toNat dom = true →
      ((t.gpr .a0).setWidth 32).toNat = Spec.Ffdh.keyStatus a sc ∧
        if Spec.Ffdh.keyStatus a sc = 1 then
          Spec.Rsa.bytesAt t.mem (s.gpr .a0) (s.gpr .a6).toNat = Spec.Rsa.i2osp sc (s.gpr .a6).toNat ∧
            Spec.Rsa.bytesAt t.mem (s.gpr .a2) (s.gpr .a6).toNat =
              Spec.Rsa.i2osp (Spec.Rsa.powMod a.g sc a.p) (s.gpr .a6).toNat
        else Spec.Rsa.bytesAt t.mem (s.gpr .a0) (s.gpr .a6).toNat = List.replicate (s.gpr .a6).toNat 0 ∧
          Spec.Rsa.bytesAt t.mem (s.gpr .a2) (s.gpr .a6).toNat = List.replicate (s.gpr .a6).toNat 0
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.gpr .a6 = s₂.gpr .a6 ∧
      s₁.gpr .a7 = s₂.gpr .a7 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
      stackArg s₁ 2 = stackArg s₂ 2 ∧ gkLeak s₁ = gkLeak s₂

/-- The exchange's public data: `y` as `out`, x as x, g as the peer. -/
def gxOf (s : State) : XD :=
  ⟨s.gpr .a2, s.gpr .a4, (s.gpr .a5).toNat, (s.gpr .a6).toNat, s.gpr .a0, (s.gpr .a6).toNat,
    off (s.gpr .a4) (s.gpr .a6).toNat, stackArg s 1, (stackArg s 2).toNat * 8,
    Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat⟩

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

/-- The registers the front writes. -/
def frontRegs : List Reg := [.t0, .s6, .t2, .t1, .a3, .a5, .a0, .a2, .a4, .s7, .s8, .a1, .a7, .s5, .s10, .s11]

/-- `gkFront`: `Base`, `AR`, `rand` in `t1`, the callee-saved registers
saved, and only the header changed. -/
theorem gkFront_ok {s : State} (h : gkContract.pre s) :
    WP isa (.block gkFront) s fun t =>
      Base (gxOf s) t ∧ AR (gxOf s) t ∧ t.gpr .t1 = s.gpr .a7 ∧
        (∀ i < 12, t.mem.readW (off (savW (stackArg s 1)) (8 * i)) 64 = s.gpr (PublicChecked.saved i)) ∧
        Keep frontRegs s t ∧ Outside (stackArg s 1) 0 256 s.mem t.mem := by
  obtain ⟨hrd, hwr, dXY, dXD, dXR, dXS, dXA, dYD, dYR, dYS, dYA, dDS, dRS, dSA, nwX, nwY, nwD, nwR, nwS,
    ⟨hk, hk'⟩, hL, hxl, hyl, hrl, hsl, alS, alsp⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  simp only [gxOf]
  have hA1 : InRegions (s.rd ++ s.wr) (stackArgAddr s 1) 8 := by
    refine ⟨gkStack s, List.mem_append_left _ (by rw [hrd]; simp), ?_⟩
    show (⟨s.sp + BitVec.ofNat 64 (8 * 0), 24⟩ : Region).Contains (s.sp + BitVec.ofNat 64 (8 * 1)) 8
    simp only [Nat.mul_zero, Nat.mul_one, add_ofNat_zero]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  generalize hSd : stackArg s 1 = S at hwr dXS dYS dDS dRS dSA nwS alS ⊢
  generalize hZd : (stackArg s 2).toNat * 8 = Z at hwr dXS dYS dDS dRS dSA nwS ⊢
  have hZ : 256 + 128 * (s.gpr .a6).toNat ≤ Z := by omega_arith
  have hs : Scr s S Z := Scr.of_mem (by rw [hwr]; simp) nwS alS
  unfold gkFront
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (loadS1_ok s hA1 alsp) fun s₁ ⟨⟨a0', m1⟩, k1⟩ => ?_)
  rw [hSd] at a0'
  have hin : ∀ i < 12, InRegions s₁.wr (off (savW (s₁.gpr .t0)) (8 * i)) 8 := fun i hi => by
    rw [a0', k1.2.2, hwr]
    show InRegions _ (S + BitVec.ofNat 64 128 + BitVec.ofNat 64 (8 * i)) 8
    rw [Offset.add_add]
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  refine WP.block_append (WP.mono (Pub.save_ok s₁ hin (fun i hi => by
    rw [a0']; exact Pub.sav_al alS (by omega_arith) hi)) fun s₂ hS => ?_)
  have k12 := k1.trans hS.keep
  have h6₂ : s₂.gpr .s6 = S := hS.s6.trans a0'
  refine WP.block_append (WP.mono (ghdr_ok (hs.congr k12.2.2) (by omega_arith) h6₂)
    fun s₃ ⟨⟨w0, w8, w16, w24, b1, b3, b5, b0, b2, b4, b6, b7, b8, ba1, o3⟩, k3⟩ => ?_)
  have k13 := k12.trans k3
  refine WP.mono (Pub.setup_ok (O := s.gpr .a2) (k := (s.gpr .a6).toNat) (b0.trans (k12.gpr (by decide)))
    (by rw [ba1, k12.gpr (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq])
    ((k3.gpr (by decide)).trans h6₂) hk') fun t ⟨⟨j10, j11, j0, j5, j7, jm⟩, k4⟩ => ?_
  have k := k13.trans k4
  have hrdt : t.rd ++ t.wr = s.rd ++ s.wr := by rw [k.2.1, k.2.2]
  have hsavO : Outside S 0 256 s.mem s₂.mem := fun y hy => by
    rw [← m1]
    refine hS.frame y fun r hr hc => ?_
    rw [List.mem_singleton] at hr
    subst hr
    rw [a0'] at hc
    have hc' := (Offset.sub_base (n := 96) (k := 256) S (d := 128) (by omega_arith)) _ hc
    simp only [Region.Contains] at hc'
    simp only [ofs] at hy
    omega_arith
  have hO : Outside S 0 256 s.mem t.mem := by
    rw [jm]; exact hsavO.trans (o3.mono (Nat.le_refl _) (by omega_arith))
  have hOZ : Outside S 0 Z s.mem t.mem := hO.mono (Nat.le_refl _) (by omega_arith)
  have hb : ∀ (Q : Addr) n, (∀ i < n, ∀ y, ofs S y < Z → off Q i ≠ y) →
      Spec.Rsa.bytesAt t.mem Q n = Spec.Rsa.bytesAt s.mem Q n := fun Q n hsep =>
    Pub.bytes_apart (o := 0) (n := Z) hOZ (by omega_arith) hsep
  have hw3 : ∀ d, d + 8 ≤ 32 → word t.mem S d = word s₃.mem S d := fun d _ => by rw [jm]
  have hLk : 2 * (s.gpr .a6).toNat ≤ (s.gpr .a5).toNat ∧ (s.gpr .a5).toNat ≤ 3 * (s.gpr .a6).toNat := by
    simp only [Spec.Ffdh.domainLenValid] at hL; omega_arith
  have sepD := Pub.ne_of_disjoint dDS (Nat.le_of_lt (s.gpr .a5).isLt)
  have rdD : ∀ i < (s.gpr .a5).toNat, InRegions (t.rd ++ t.wr) (off (s.gpr .a4) i) 1 := by
    rw [hrdt]; exact rd_of_mem (by rw [hrd]; simp) (Nat.le_refl _) (BitVec.isLt _)
  have rdX : ∀ i < (s.gpr .a6).toNat, InRegions (t.rd ++ t.wr) (off (s.gpr .a0) i) 1 := fun i hi => by
    rw [hrdt]
    exact ⟨⟨s.gpr .a0, (s.gpr .a1).toNat⟩, List.mem_append_right _ (by rw [hwr]; simp),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  refine ⟨⟨⟨hs.congr k.2.2, hk, hk', hLk, ?_, by rw [← hyl]; exact nwY, fun i hi => ⟨⟨s.gpr .a2, (s.gpr .a3).toNat⟩,
      by rw [k.2.2, hwr]; simp, Offset.contains_base _ (by change i < (s.gpr .a6).toNat at hi; omega_arith)
        (by change i < (s.gpr .a6).toNat at hi; omega_arith)⟩,
      fun y hy => Pub.sep_of_disjoint dYS y (by rw [hyl]; exact hy),
      rdD, sepD, fun i hi => by rw [Derive.off_off]; exact rdD _ (by change i < (s.gpr .a6).toNat at hi; omega_arith),
      fun i hi => by rw [Derive.off_off]; exact sepD _ (by change i < (s.gpr .a6).toNat at hi; omega_arith),
      rdX, fun i hi => Pub.ne_of_disjoint dXS (Nat.le_of_lt (s.gpr .a1).isLt) i
        (by change i < (s.gpr .a6).toNat at hi; omega_arith), by change 1 ≤ (s.gpr .a6).toNat; omega_arith, Nat.le_refl _,
      (by rw [hb _ _ sepD]), ?_, ?_, ?_, ?_⟩,
    by rw [k4.gpr (by decide), k3.gpr (by decide)]; exact h6₂, j7,
    by rw [j5, Nat.mul_add], j0, by rw [k4.gpr (by decide), b7, k12.gpr (by decide)]; simp [off],
    by rw [k4.gpr (by decide), b8, k12.gpr (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq],
    by rw [j10]; simp [off], j11⟩,
    ⟨by rw [k4.gpr (by decide), b2, k12.gpr (by decide)],
      by rw [k4.gpr (by decide), b3, k12.gpr (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq],
      by rw [k4.gpr (by decide), b4, k12.gpr (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq],
      by rw [k4.gpr (by decide), b5, k12.gpr (by decide)],
      by rw [k4.gpr (by decide), b6, k12.gpr (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩,
    by rw [k4.gpr (by decide), b1, k12.gpr (by decide)], ?_, k.mono (by decide), hO⟩
  · show slot (((s.gpr .a6).toNat + 7) / 8) 24 ≤ Z
    unfold slot hdrBytes; omega_arith
  · rw [hw3 0 (by decide), w0, k12.gpr (by decide)]; simp [off]
  · rw [hw3 8 (by decide), w8, k12.gpr (by decide)]; simp [off]
  · rw [hw3 16 (by decide), w16, k12.gpr (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [hw3 24 (by decide), w24, k12.gpr (by decide), k12.gpr (by decide)]; simp [off]
  · intro i hi
    have e : off (savW S) (8 * i) = off S (128 + 8 * i) := by rw [off, off, Offset.add_add]
    rw [e]
    show word t.mem S (128 + 8 * i) = _
    rw [jm, o3.word (Or.inr (by omega_arith)) (by omega_arith)]
    show s₂.mem.readW (off S (128 + 8 * i)) 64 = _
    rw [← e, ← a0', hS.saved i hi, k1.gpr fun h => Pub.saved_ne_t0 i hi (List.mem_singleton.mp h)]

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

theorem gkOct_congr {m m' : Mem} {D R : Addr} {k L : Nat} (hR : Spec.Rsa.bytesAt m' R k = Spec.Rsa.bytesAt m R k)
    (hB : Spec.Rsa.bytesAt m' (bptr D k L) k = Spec.Rsa.bytesAt m (bptr D k L) k) :
    gkOct m' D R k L = gkOct m D R k L := by
  unfold gkOct smeared; rw [hR, hB]

/-- x's and `rand`'s facts, from the precondition. -/
theorem xr_of_pre {s t : State} (h : gkContract.pre s) (r3 : t.rd = s.rd) (w3 : t.wr = s.wr) :
    XR (gxOf s) (s.gpr .a7) t := by
  obtain ⟨hrd, hwr, dXY, dXD, dXR, dXS, dXA, dYD, dYR, dYS, dYA, dDS, dRS, dSA, nwX, nwY, nwD, nwR, nwS,
    ⟨hk, hk'⟩, hL, hxl, hyl, hrl, hsl, alS, alsp⟩ := h
  refine ⟨fun i hi => ?_, by change (s.gpr .a0).toNat + (s.gpr .a6).toNat ≤ _; omega_arith,
    fun y hy => by
      change ofs (stackArg s 1) y < (stackArg s 2).toNat * 8 at hy
      change (s.gpr .a6).toNat ≤ ofs (s.gpr .a0) y
      have := Pub.sep_of_disjoint dXS.symm y hy
      rw [hxl] at this; exact this,
    fun i hi y hy => Pub.ne_of_disjoint dXD.symm (Nat.le_of_lt (s.gpr .a5).isLt) i hi y (by rw [hxl]; exact hy),
    fun i hi => ?_, fun i hi y hy => Pub.ne_of_disjoint dXR.symm (Nat.le_of_lt (stackArg s 0).isLt) i
      (by change i < (s.gpr .a6).toNat at hi; omega_arith) y (by rw [hxl]; exact hy),
    fun i hi => Pub.ne_of_disjoint dRS (Nat.le_of_lt (stackArg s 0).isLt) i
      (by change i < (s.gpr .a6).toNat at hi; omega_arith), rfl,
    fun i hi y hy => Pub.ne_of_disjoint dXY (Nat.le_of_lt (s.gpr .a1).isLt) i
      (by change i < (s.gpr .a6).toNat at hi; omega_arith) y (by rw [hyl]; exact hy),
    fun y hy => by
      change ofs (stackArg s 1) y < (stackArg s 2).toNat * 8 at hy
      change (s.gpr .a6).toNat ≤ ofs (s.gpr .a2) y
      have := Pub.sep_of_disjoint dYS.symm y hy
      rw [hyl] at this; exact this,
    fun i hi y hy => Pub.ne_of_disjoint dXY.symm (Nat.le_of_lt (s.gpr .a3).isLt) i
      (by change i < (s.gpr .a6).toNat at hi; omega_arith) y (by rw [hxl]; exact hy)⟩
  · change i < (s.gpr .a6).toNat at hi
    rw [w3, hwr]
    exact ⟨_, List.mem_cons_self, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · change i < (s.gpr .a6).toNat at hi
    rw [r3, w3]
    exact rd_of_mem (L := (stackArg s 0).toNat) (by rw [hrd]; simp) (by omega_arith) (BitVec.isLt _) i hi

/-- Writes to x leave the working space. -/
theorem outX_scr {X S : Addr} {k Z : Nat} {m m' : Mem} (ho : Outside X 0 k m m')
    (hsep : ∀ y, ofs S y < Z → k ≤ ofs X y) : Outside S Z (2 ^ 64) m m' := fun y hy =>
  ho y (Or.inr (by
    rw [Nat.zero_add]
    rcases hy with h | h
    · exact hsep y h
    · have := (y - S).isLt; simp only [ofs] at h; omega_arith))

/-- `scalar` keeps `X4`, `AR` and `XR`. -/
theorem scalarX4_ok {x : XD} {R : Addr} {s : State} (h : X4 x s) (hz : s.gpr .s0 = 0) (ha : AR x s)
    (hx : XR x R s) (h1 : s.gpr .t1 = R) :
    WP isa scalar s fun t => X4 x t ∧ t.gpr .s0 = 0 ∧ AR x t ∧ XR x R t ∧
      Spec.Rsa.bytesAt t.mem x.X x.k = gkOct s.mem x.D R x.k x.L ∧ Outside x.X 0 x.k s.mem t.mem := by
  have hv := h.2.2.mp hz
  have hb := h.1
  have hc := hb.ctx
  have hZ := hc.hZ
  have hn := hc.scr.nowrap
  unfold slot hdrBytes at hZ
  refine WP.mono (WP.rdwr (scalar_ok hb ha hx h1)) fun s₁ ⟨⟨⟨xb, xo, z0⟩, k1⟩, r1, w1, _⟩ => ?_
  have hc1 := Ctx.ofX hc hx r1 w1 xo
  have os1 := outX_scr xo hx.sepSX
  have hb1 : Base x s₁ := ⟨hc1, (k1.gpr (by decide)).trans hb.s6, (k1.gpr (by decide)).trans hb.a7,
    (k1.gpr (by decide)).trans hb.s5, (k1.gpr (by decide)).trans hb.t0, (k1.gpr (by decide)).trans hb.s7,
    (k1.gpr (by decide)).trans hb.s8, (k1.gpr (by decide)).trans hb.s10, (k1.gpr (by decide)).trans hb.s11⟩
  have e0 : slot x.w 0 = 256 := by simp [slot, hdrBytes]
  exact ⟨⟨hb1, by rw [Outside.wordsVal os1 (Or.inl (by omega_arith)) (by omega_arith)]; exact h.2.1,
    fun _ => hv, fun _ => z0⟩, z0, ha.keep k1, hx.keep r1 w1, xb, xo⟩

end VG.Proof.Ffdh.RISCV64.GenerateKey
