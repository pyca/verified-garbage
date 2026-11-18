module

public import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubOut
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ffdh.PPC64LE.GenerateKey
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Eq
public import VerifiedGarbage.Proof.Ffdh.ScanAt
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound

/-! ### `Ffdh.PPC64LE.GenerateKey.Scan`, which this module and modules that import it used -/

section

/-!
# `vg_ffdh_generate_key` on PPC64LE: the scan of the bound's octets

`scanBody`, without a branch, keeps the first nonzero octet of the bound and
its index: after `j` of the `k` octets at `P`, `r22`, `r14` and the mask in
`r15` hold `scanAt` of them (`scan_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.GenerateKey

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.GenerateKey
open VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Proof.MillerRabin.PPC64LE (mask)

/-! ## Masks -/

theorem nz_mask_nat : ∀ n < 256, BitVec.ofNat 64 0 - ((BitVec.ofNat 64 0 - BitVec.ofNat 64 n ||| BitVec.ofNat 64 n) >>> 63) =
    mask (n != 0) := by decide +kernel

/-- The mask of an octet being nonzero. -/
theorem nz_mask (b : Byte) : 0#64 - ((0#64 - b.setWidth 64 ||| b.setWidth 64) >>> 63) =
    mask (b != 0) := by
  have e : b.setWidth 64 = BitVec.ofNat 64 b.toNat := by
    apply BitVec.eq_of_toNat_eq; simp
  have e2 : (b != 0) = (b.toNat != 0) := by
    cases h : (b != 0) <;> simp_all [BitVec.toNat_eq]
  rw [e, nz_mask_nat _ b.isLt, e2]

theorem mask_or_xor (a f : Bool) : (mask a ||| mask f) ^^^ mask f = mask (a && !f) := by
  cases a <;> cases f <;> rfl

theorem mask_or' (a f : Bool) : mask f ||| mask a = mask (f || a) := by cases a <;> cases f <;> rfl

/-- A choice by a mask. -/
theorem sel (x y : BitVec 64) (c : Bool) : x ^^^ ((x ^^^ y) &&& mask c) = if c then y else x := by
  cases c
  · show x ^^^ ((x ^^^ y) &&& 0) = x
    simp
  · show x ^^^ ((x ^^^ y) &&& BitVec.allOnes 64) = y
    rw [BitVec.and_allOnes, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem getD_bytesAt (m : Mem) (P : Addr) {n j : Nat} (hj : j < n) :
    (Spec.Rsa.bytesAt m P n).getD j 0 = m (off P j) := by
  simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, hj, off]

/-! ## The loop -/

/-- The registers the scan writes. -/
def scanRegs : List Reg := [.r0, .r4, .r6, .r22, .r12, .r14, .r15, .r16, .r17, .r18]

/-- What the scan holds after `j` octets. -/
def ScanInv (s : State) (P : Addr) (k j : Nat) (t : State) : Prop :=
  t.gpr .r12 = off P j ∧ t.gpr .r4 = BitVec.ofNat 64 j ∧
    t.gpr .r22 = BitVec.ofNat 64 (scanAt (Spec.Rsa.bytesAt s.mem P k) j).2.1 ∧
    t.gpr .r14 = (scanAt (Spec.Rsa.bytesAt s.mem P k) j).2.2.setWidth 64 ∧
    t.gpr .r15 = mask (scanAt (Spec.Rsa.bytesAt s.mem P k) j).1 ∧ t.mem = s.mem ∧ Keep scanRegs s t

theorem scanBody_ok {s t : State} {P : Addr} {k j : Nat} (hj : j < k)
    (hrd : InRegions (t.rd ++ t.wr) (off P j) 1) (h : ScanInv s P k j t) :
    WP isa (.block (scanBody ++ ([.subi .r6 .r6 1] : List Instr))) t fun u =>
      ScanInv s P k (j + 1) u ∧ u.gpr .r6 = t.gpr .r6 - BitVec.ofNat 64 1 := by
  obtain ⟨t12, t4, t9, t14, t15, tm, tk⟩ := h
  have hb : t.mem (off P j) = (Spec.Rsa.bytesAt s.mem P k).getD j 0 := by rw [getD_bytesAt _ _ hj, tm]
  unfold ScanInv
  rw [scanAt_succ]
  rcases hr : scanAt (Spec.Rsa.bytesAt s.mem P k) j with ⟨f, i, o⟩
  rw [hr] at t9 t14 t15
  generalize (Spec.Rsa.bytesAt s.mem P k).getD j 0 = b at hb ⊢
  simp only
  unfold scanBody
  have hst : WP isa (.block ([.lbz .r16 .r12 0, .li .r0 0, .sub .r17 .r0 .r16, .logic .or .r17 .r17 .r16,
      .lsr .d .r17 .r17 63, .sub .r17 .r0 .r17, .logic .or .r17 .r17 .r15, .logic .xor .r17 .r17 .r15,
      .logic .xor .r18 .r22 .r4, .logic .and .r18 .r18 .r17, .logic .xor .r22 .r22 .r18,
      .logic .xor .r18 .r14 .r16, .logic .and .r18 .r18 .r17, .logic .xor .r14 .r14 .r18,
      .logic .or .r15 .r15 .r17, .addi .r12 .r12 1, .addi .r4 .r4 1] ++ ([.subi .r6 .r6 1] : List Instr))) t
      fun u => (u.gpr .r12 = off P (j + 1) ∧ u.gpr .r4 = BitVec.ofNat 64 (j + 1) ∧
        u.gpr .r22 = (BitVec.ofNat 64 i ^^^ ((BitVec.ofNat 64 i ^^^ BitVec.ofNat 64 j) &&& mask (b != 0 && !f))) ∧
        u.gpr .r14 = (o.setWidth 64 ^^^ ((o.setWidth 64 ^^^ b.setWidth 64) &&& mask (b != 0 && !f))) ∧
        u.gpr .r15 = (mask f ||| mask (b != 0 && !f)) ∧ u.mem = t.mem ∧
        u.gpr .r6 = t.gpr .r6 - BitVec.ofNat 64 1) ∧ Keep scanRegs t u := by
    refine WP.keep _ ?_ (by decide)
    prun [t12, t4, t9, t14, t15, exec_lbz' (show Reg.r12 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide), hrd,
      BitVec.add_zero, Pub.read1_setWidth, hb]
    rw [nz_mask, mask_or_xor]
    exact ⟨by rw [BitVec.ofNat_add], rfl, rfl, rfl⟩
  refine WP.mono hst fun u ⟨⟨u12, u4, u9, u14, u15, um, u6⟩, ku⟩ => ⟨⟨u12, u4, ?_, ?_, ?_, um.trans tm, (tk.trans ku).mono (by decide)⟩, u6⟩
  · rw [u9, sel]
    cases hc : (!f && b != 0) <;> simp_all [Bool.and_comm]
  · rw [u14, sel]
    cases hc : (!f && b != 0) <;> simp_all [Bool.and_comm]
  · rw [u15, mask_or']
    cases f <;> cases hc : (b != 0) <;> simp_all

theorem sub1_ofNat {k : Nat} (hk : 1 ≤ k) : BitVec.ofNat 64 k - 1#64 = BitVec.ofNat 64 (k - 1) := by
  rw [show k = (k - 1) + 1 by omega_using [hk], BitVec.ofNat_add, Nat.add_sub_cancel, BitVec.add_sub_cancel]

/-- `scanSetup` and the scan of the `k` octets at `P` (`r12`): `r22` and `r14`
are `lead` of them and its octet. -/
theorem scan_ok {s : State} {P : Addr} {k : Nat} (hk1 : 1 ≤ k) (hk : k < 2 ^ 32)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off P i) 1) (h12 : s.gpr .r12 = off P 0)
    (h28 : s.gpr .r28 = BitVec.ofNat 64 k) :
    WP isa (.block scanSetup) s fun u => WP isa (countLoop .r6 scanBody) u fun t =>
      (t.gpr .r22 = BitVec.ofNat 64 (lead (Spec.Rsa.bytesAt s.mem P k)) ∧
        t.gpr .r14 = ((Spec.Rsa.bytesAt s.mem P k).getD (lead (Spec.Rsa.bytesAt s.mem P k)) 0).setWidth 64 ∧
        t.mem = s.mem) ∧ Keep scanRegs s t := by
  have hlen : (Spec.Rsa.bytesAt s.mem P k).length = k := by simp [Spec.Rsa.bytesAt]
  have hne : Spec.Rsa.bytesAt s.mem P k ≠ [] := fun h => by rw [h] at hlen; simp at hlen; omega_using [hk1, hlen]
  refine (WP.mono (WP.keep scanRegs (Q := fun u => u.gpr .r12 = off P 0 ∧ u.gpr .r4 = BitVec.ofNat 64 0 ∧
      u.gpr .r22 = BitVec.ofNat 64 (k - 1) ∧ u.gpr .r14 = BitVec.ofNat 64 0 ∧ u.gpr .r15 = BitVec.ofNat 64 0 ∧
      u.mem = s.mem ∧ u.gpr .r6 = BitVec.ofNat 64 k) ?_ (by decide)) fun u ⟨⟨u12, u4, u9, u14, u15, um, u6⟩, ku⟩ => ?_)
  · unfold scanSetup
    prun [h12, h28, sub1_ofNat hk1, BitVec.add_zero]
  have h0 : ScanInv s P k 0 u := by
    refine ⟨u12, u4, ?_, ?_, ?_, um, ku⟩ <;> rw [scanAt.eq_1]
    · rw [u9, hlen]
    · rw [u14]; rfl
    · rw [u15]; exact (show mask false = 0#64 by decide).symm
  refine WP.mono (wp_countdown (cnt := .r6) (N := k) (by omega_using [hk]) (by omega_using [hk1]) (ScanInv s P k)
    (fun j hj t ht _ => scanBody_ok hj (by rw [ht.2.2.2.2.2.2.rd, ht.2.2.2.2.2.2.wr]; exact hrd j hj) ht) h0 u6)
    fun t ⟨_, _, t9, t14, _, tm, kt⟩ => ?_
  have e := scanAt_length hne
  rw [hlen] at e
  rw [e] at t9 t14
  exact ⟨⟨t9, t14, tm⟩, kt⟩

end VG.Proof.Ffdh.PPC64LE.GenerateKey

end

end

/-!
# `vg_ffdh_generate_key` on PPC64LE: the cut

`cut_ok`: `rand`'s `k` octets at `R` to x at `X`, zeros before
the index `ld` in `r22`, and'ed with the octet in `r14` at it, kept after it
(`KeyScalar.cut`), without a branch.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.GenerateKey

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.GenerateKey
open VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Ffdh.KeyScalar
open VG.Proof.MillerRabin.PPC64LE (mask)

/-! ## The smear -/

/-! ## Masks of the index -/

theorem lt_mask {j l : Nat} (hj : j < 2 ^ 32) (hl : l < 2 ^ 32) :
    0#64 - ((BitVec.ofNat 64 j - BitVec.ofNat 64 l) >>> 63) = mask (decide (j < l)) := by
  have e : (BitVec.ofNat 64 j - BitVec.ofNat 64 l) >>> 63 = BitVec.ofNat 64 (if j < l then 1 else 0) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    split <;> omega_arith
  rw [e]
  by_cases h : j < l <;> simp [h]

theorem eq_mask {j l : Nat} (hj : j < 2 ^ 32) (hl : l < 2 ^ 32) :
    0#64 - (((BitVec.ofNat 64 j ^^^ BitVec.ofNat 64 l) - 1#64) >>> 63) = mask (decide (j = l)) := by
  have hx : (BitVec.ofNat 64 j ^^^ BitVec.ofNat 64 l) = BitVec.ofNat 64 (j ^^^ l) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hj]),
      Nat.mod_eq_of_lt (by omega_using [hl]), Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.xor_lt_two_pow hj hl) (by decide))]
  have hlt : j ^^^ l < 2 ^ 32 := Nat.xor_lt_two_pow hj hl
  have hz : j ^^^ l = 0 ↔ j = l := ⟨fun h => by
    have := congrArg (· ^^^ l) h
    simpa [Nat.xor_assoc] using this, fun h => by rw [h, Nat.xor_self]⟩
  have e : ((BitVec.ofNat 64 (j ^^^ l)) - 1#64) >>> 63 = BitVec.ofNat 64 (if j = l then 1 else 0) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    simp only [BitVec.toNat_ofNat]
    split <;> omega_arith
  rw [hx, e]
  by_cases h : j = l <;> simp [h]

theorem or_xor_mask (x : BitVec 64) (c : Bool) : (x ||| mask c) ^^^ mask c = if c then 0 else x := by
  cases c
  · show (x ||| 0) ^^^ 0 = x
    simp
  · show (x ||| BitVec.allOnes 64) ^^^ BitVec.allOnes 64 = 0
    rw [BitVec.or_allOnes, BitVec.xor_self]; rfl

/-- The octet the cut stores. -/
theorem cut_byte (b t : Byte) (lt eq : Bool) :
    (b.setWidth 64 &&& (if lt then 0 else if eq then t.setWidth 64 else 255#64)).setWidth 8 =
      if lt then 0 else if eq then b &&& t else b := by
  cases lt <;> cases eq <;> simp only [ite_true, ite_false, Bool.false_eq_true] <;>
    apply BitVec.eq_of_toNat_eq <;> simp [BitVec.toNat_and]
  rw [show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt b.isLt]

theorem sel255 (v : BitVec 64) (c : Bool) : ((255#64 ^^^ v) &&& mask c) ^^^ 255#64 = if c then v else 255#64 := by
  rw [BitVec.xor_comm _ 255#64, sel]

/-! ## The cut -/

/-- The registers the cut writes. -/
def cutRegs : List Reg := [.r0, .r4, .r6, .r16, .r17, .r18, .r19, .r20, .r24, .r25]

/-- What the cut holds after `j` octets. -/
def CutInv (s : State) (R X : Addr) (k ld : Nat) (tb : Byte) (j : Nat) (t : State) : Prop :=
  t.gpr .r24 = off R j ∧ t.gpr .r25 = off X j ∧ t.gpr .r4 = BitVec.ofNat 64 j ∧ t.gpr .r22 = BitVec.ofNat 64 ld ∧
    t.gpr .r14 = tb.setWidth 64 ∧ Outside X 0 j s.mem t.mem ∧
    (∀ i < j, t.mem (off X i) = (cut (Spec.Rsa.bytesAt s.mem R k) ld tb).getD i 0) ∧ (0 < j → t.gpr .r0 = 0#64) ∧
    Keep cutRegs s t

theorem cutBody_ok {s t : State} {R X : Addr} {k ld j : Nat} {tb : Byte} (hj : j < k) (hk : k < 2 ^ 32)
    (hld : ld < k) (hx : Scr s X k) (hrd : InRegions (s.rd ++ s.wr) (off R j) 1)
    (hsep : ∀ y, ofs X y < k → off R j ≠ y) (h : CutInv s R X k ld tb j t) :
    WP isa (.block (cutBody ++ ([.subi .r6 .r6 1] : List Instr))) t fun u =>
      CutInv s R X k ld tb (j + 1) u ∧ u.gpr .r6 = t.gpr .r6 - BitVec.ofNat 64 1 := by
  obtain ⟨t24, t25, t4, t9, t14, tout, tx, -, tk⟩ := h
  have hb : t.mem (off R j) = s.mem (off R j) := by
    refine tout _ (Or.inr ?_)
    by_contra hc
    exact hsep _ (by omega_using [hj, hc]) rfl
  have hrd' : InRegions (t.rd ++ t.wr) (off R j) 1 := by rw [tk.rd, tk.wr]; exact hrd
  have hst : InRegions t.wr (off X j) 1 := (hx.congr tk.wr).st (d := j) (n := 1) (by omega_using [hj])
  have hnw := hx.nowrap
  unfold cutBody
  refine WP.mono (WP.keep cutRegs (Q := fun u => u.gpr .r24 = off R (j + 1) ∧ u.gpr .r25 = off X (j + 1) ∧
      u.gpr .r4 = BitVec.ofNat 64 (j + 1) ∧ u.gpr .r6 = t.gpr .r6 - BitVec.ofNat 64 1 ∧ u.gpr .r0 = 0#64 ∧
      u.mem = t.mem.write (off X j) 1 (((s.mem (off R j)).setWidth 64 &&&
        (if decide (j < ld) then 0 else if decide (j = ld) then tb.setWidth 64 else 255#64)).setWidth 8)) ?_ (by decide))
    fun u ⟨⟨u24, u25, u4, u6, u0, um⟩, ku⟩ =>
      ⟨⟨u24, u25, u4, ?_, ?_, ?_, ?_, fun _ => u0, (tk.trans ku).mono (by decide)⟩, u6⟩
  · prun [t24, t25, t4, t9, t14, exec_lbz' (show Reg.r24 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide), hrd',
      exec_stb (show Reg.r25 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide), hst, BitVec.add_zero, Pub.read1_setWidth,
      hb, lt_mask (show j < 2 ^ 32 by omega_using [hj, hk]) (show ld < 2 ^ 32 by omega_using [hk, hld]),
      eq_mask (show j < 2 ^ 32 by omega_using [hj, hk]) (show ld < 2 ^ 32 by omega_using [hk, hld]), sel255, or_xor_mask]
    rw [BitVec.ofNat_add]
  · rw [ku.gpr .r22 (by decide), t9]
  · rw [ku.gpr .r14 (by decide), t14]
  · rw [um]
    exact (tout.mono (Nat.le_refl _) (by omega_using [])).trans ((write1_outside t.mem X (d := j) _ (by omega_using [hj, hk])).mono
      (by omega_using []) (by omega_using []))
  · intro i hi
    rw [um]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [write1_outside t.mem X (d := j) _ (by omega_using [hj, hk]) _ (by rw [Bignum.PPC64LE.ofs_off0 X (by omega_arith)]; omega_using [hi])]
      exact tx i hi
    · rw [write1_self, cut_byte]
      have hl : (Spec.Rsa.bytesAt s.mem R k).length = k := by simp [Spec.Rsa.bytesAt]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [cut_length tb (by omega_using [hld, hl]), hl]; omega_using [hj]),
        Option.getD_some, cut_get tb (by omega_using [hld, hl]) (by omega_using [hj, hl])]
      have hr : (Spec.Rsa.bytesAt s.mem R k)[i]'(by omega_using [hj, hl]) = s.mem (off R i) := by
        simp [Spec.Rsa.bytesAt, off]
      rw [hr]
      by_cases h1 : i < ld
      · simp [h1]
      · by_cases h2 : i = ld <;> simp [h1, h2]

/-- The cut of `rand`'s `k` octets at `R` (`r24`) into x at `X` (`r25`). -/
theorem cut_ok {s : State} {R X : Addr} {k ld : Nat} {tb : Byte} (hk1 : 1 ≤ k) (hk : k < 2 ^ 32) (hld : ld < k)
    (hx : Scr s X k) (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off R i) 1)
    (hsep : ∀ i < k, ∀ y, ofs X y < k → off R i ≠ y) (h24 : s.gpr .r24 = off R 0) (h25 : s.gpr .r25 = off X 0)
    (h4 : s.gpr .r4 = BitVec.ofNat 64 0) (h22 : s.gpr .r22 = BitVec.ofNat 64 ld) (h14 : s.gpr .r14 = tb.setWidth 64)
    (h6 : s.gpr .r6 = BitVec.ofNat 64 k) :
    WP isa (countLoop .r6 cutBody) s fun t =>
      (Spec.Rsa.bytesAt t.mem X k = cut (Spec.Rsa.bytesAt s.mem R k) ld tb ∧ Outside X 0 k s.mem t.mem ∧
        t.gpr .r0 = 0#64) ∧ Keep cutRegs s t := by
  refine WP.mono (wp_countdown (cnt := .r6) (N := k) (by omega_using [hk]) (by omega_using [hk1]) (CutInv s R X k ld tb)
    (fun j hj t ht _ => cutBody_ok hj hk hld hx (hrd j hj) (hsep j hj) ht)
    ⟨h24, h25, h4, h22, h14, Outside.refl _ _ _ _, fun _ h => absurd h (by omega_using []), fun h => absurd h (by omega_using []),
      Keep.refl _ _⟩ h6)
    fun t ⟨_, _, _, _, _, tout, tx, t0, kt⟩ => ⟨⟨?_, tout, t0 (by omega_using [hk1])⟩, kt⟩
  have hl : (Spec.Rsa.bytesAt s.mem R k).length = k := by simp [Spec.Rsa.bytesAt]
  apply List.ext_getElem (by rw [cut_length tb (by omega_using [hld, hl]), hl]; simp [Spec.Rsa.bytesAt])
  intro i h1 h2
  have hi : i < k := by simpa [Spec.Rsa.bytesAt] using h1
  have e : (Spec.Rsa.bytesAt t.mem X k)[i] = t.mem (off X i) := by simp [Spec.Rsa.bytesAt, off]
  rw [e, tx i hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]

/-! ## The mask of x -/

/-- The masked loop: x's `k` octets (`r25`) and'ed with the mask of `c` in `r17`. -/
theorem masked_ok {s : State} {X : Addr} {k : Nat} {c : Bool} (hk1 : 1 ≤ k) (hk : k < 2 ^ 32) (hx : Scr s X k)
    (h25 : s.gpr .r25 = off X 0) (h17 : s.gpr .r17 = mask c) (h6 : s.gpr .r6 = BitVec.ofNat 64 k) :
    WP isa (countLoop .r6 [.lbz .r16 .r25 0, .logic .and .r16 .r16 .r17, .stb .r16 .r25 0, .addi .r25 .r25 1]) s
      fun t => (Spec.Rsa.bytesAt t.mem X k = (if c then Spec.Rsa.bytesAt s.mem X k else List.replicate k 0) ∧
        Outside X 0 k s.mem t.mem) ∧ Keep [.r6, .r16, .r25] s t := by
  have hnw := hx.nowrap
  let Inv : Nat → State → Prop := fun j t => t.gpr .r25 = off X j ∧ t.gpr .r17 = mask c ∧
    Outside X 0 j s.mem t.mem ∧ (∀ i < j, t.mem (off X i) = if c then s.mem (off X i) else 0) ∧
    Keep [.r6, .r16, .r25] s t
  refine WP.mono (wp_countdown (cnt := .r6) (N := k) (by omega_using [hk]) (by omega_using [hk1]) Inv
    (fun j hj t ⟨t25, t17, tout, tz, tk⟩ _ => ?_) ⟨h25, h17, Outside.refl _ _ _ _, fun _ h => absurd h (by omega_using []),
      Keep.refl _ _⟩ h6) fun t ⟨_, _, tout, tz, kt⟩ => ⟨⟨?_, tout⟩, kt⟩
  · have hst : InRegions t.wr (off X j) 1 := (hx.congr tk.wr).st (d := j) (n := 1) (by omega_using [hj])
    have hrd : InRegions (t.rd ++ t.wr) (off X j) 1 := (hx.congr tk.wr).ld (d := j) (n := 1) (by omega_using [hj])
    have hb : t.mem (off X j) = s.mem (off X j) :=
      tout _ (Or.inr (by rw [Bignum.PPC64LE.ofs_off0 X (by omega_using [hk, hj])]; omega_using []))
    refine WP.mono (WP.keep [.r6, .r16, .r25] (Q := fun u => u.gpr .r25 = off X (j + 1) ∧ u.gpr .r17 = mask c ∧
        u.gpr .r6 = t.gpr .r6 - BitVec.ofNat 64 1 ∧
        u.mem = t.mem.write (off X j) 1 (if c then s.mem (off X j) else 0)) (by
      prun [t25, t17, exec_lbz' (show Reg.r25 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide), hrd,
        exec_stb (show Reg.r25 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide), hst, BitVec.add_zero,
        Pub.read1_setWidth, hb, Pub.mask_byte])
      (by decide)) fun u ⟨⟨u25, u17, u6, um⟩, ku⟩ =>
        ⟨⟨u25, u17, ?_, fun i hi => ?_, (tk.trans ku).mono (by decide)⟩, u6⟩
    · rw [um]
      exact (tout.mono (Nat.le_refl _) (by omega_using [])).trans ((write1_outside t.mem X (d := j) _ (by omega_using [hk, hj])).mono
        (by omega_using []) (by omega_using []))
    · rw [um]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [write1_outside t.mem X (d := j) _ (by omega_using [hk, hj]) _ (by rw [Bignum.PPC64LE.ofs_off0 X (by omega_arith)]; omega_using [hi])]
        exact tz i hi
      · exact write1_self _ _ _
  · apply List.ext_getElem (by cases c <;> simp [Spec.Rsa.bytesAt])
    intro i h1 _
    have hi : i < k := by simpa [Spec.Rsa.bytesAt] using h1
    have e : ∀ m : Mem, (Spec.Rsa.bytesAt m X k)[i]'(by simp [Spec.Rsa.bytesAt]; omega_using [hi]) = m (off X i) :=
      fun m => by simp [Spec.Rsa.bytesAt, off]
    rw [e, tz i hi]
    cases c
    · simp
    · simp only [ite_true]; rw [e]

end VG.Proof.Ffdh.PPC64LE.GenerateKey
