module

import VerifiedGarbage.Proof.Bignum.PPC64LE.ModArithDouble
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubPower
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubE
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCheck
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
public import VerifiedGarbage.Impl.Bignum.PPC64LE.ModArith
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Mont.Words32

/-!
# Modular arithmetic on PPC64LE: reduction

`reduce_ok`: `x mod m` into array 1, for the `L ≥ 1` bytes of `x` at `D`
(`r30`, `r31`), most significant first, apart from the working space.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.ModArith

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.PublicChecked
open VG.Impl.Bignum.PPC64LE.ModArith VG.Proof.Bignum.PPC64LE

/-- The registers the reduction writes. -/
def redRegs : List Reg := [.r0, .r3, .r14, .r15, .r16, .r17, .r20, .r24, .r25, .r30, .r31]

/-- Between the bits of the scan from `s`: the arrays' bases in place, and the
accumulator (array 1) is `c mod N`, with only arrays 1–3 changed. -/
def RInv (s : State) (B : Addr) (w N c : Nat) (t : State) : Prop :=
  Keep redRegs s t ∧ Mont.Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem ∧
    val32 t.mem B (slot w 1) (2 * w) = c % N ∧ t.gpr .r5 = off B (slot w 1) ∧ t.gpr .r8 = off B (slot w 2) ∧
    t.gpr .r9 = off B (slot w 3)

theorem mod_double_bit (c N b : Nat) : (2 * (c % N) + b) % N = (2 * c + b) % N := by
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]

/-- `reduceByte`: the eight bits of the byte at `r30` scanned, `c := 256 c + b`. -/
theorem reduceByte_ok {s t : State} {B D : Addr} {Z w N c i : Nat} (hs : Scr s B Z) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hZ : slot w 4 ≤ Z) (h10 : s.gpr .r10 = off B (slot w 0))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hNd : val32 s.mem B (slot w 0) (2 * w) = N) (hN : 0 < N)
    (ht : RInv s B w N c t) (h30 : t.gpr .r30 = off D i) (hrd : InRegions (t.rd ++ t.wr) (off D i) 1) :
    WP isa reduceByte t fun t' =>
      RInv s B w N (256 * c + (t.mem (off D i)).toNat) t' ∧ t'.gpr .r30 = off D (i + 1) ∧
        t'.gpr .r31 = t.gpr .r31 := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4
  have hh : hdrBytes = 256 := rfl
  obtain ⟨kt, ot, tv, t5, t8, t9⟩ := ht
  generalize hb : (t.mem (off D i)).toNat = b
  have hb256 : b < 256 := by rw [← hb]; exact (t.mem (off D i)).isLt
  unfold reduceByte
  refine WP.seq (WP.mono (WP.keep [.r24, .r30, .r25] (Q := fun t₁ =>
    t₁.gpr .r24 = BitVec.ofNat 64 b <<< 56 ∧ t₁.gpr .r30 = off D (i + 1) ∧ t₁.gpr .r25 = BitVec.ofNat 64 8 ∧
      t₁.mem = t.mem) ?_ (by decide)) fun t₁ ⟨⟨a24, a30, a25, m1⟩, k1⟩ => ?_)
  · prun [h30, exec_lbz' (show Reg.r30 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide), hrd, read_byte64, hb]
  let Inv : Nat → State → Prop := fun j u =>
    (∃ c', c' * 2 ^ 64 + (u.gpr .r24).toNat = (256 * c + b) * 2 ^ 56 * 2 ^ j ∧ RInv s B w N c' u) ∧
      u.gpr .r30 = off D (i + 1) ∧ u.gpr .r31 = t.gpr .r31
  refine WP.mono (wp_countdown (cnt := .r25) (N := 8) (by decide) (by decide) Inv
    (fun j _ u ⟨⟨c', hc, ku, ou, uv, u5, u8, u9⟩, u30, u31⟩ _ => ?_)
    ⟨⟨c, ?_, kt.trans' k1.mono, by rw [m1]; exact ot, by rw [m1]; exact tv, by rw [k1.gpr .r5 (by decide)]; exact t5,
      by rw [k1.gpr .r8 (by decide)]; exact t8, by rw [k1.gpr .r9 (by decide)]; exact t9⟩, a30,
      k1.gpr .r31 (by decide)⟩ a25)
    fun u ⟨⟨c', hc, hu⟩, u30, u31⟩ => ⟨?_, u30, u31⟩
  · have g : ∀ r ∈ [Reg.r10, .r11], u.gpr r = s.gpr r := fun r hr => ku.gpr r (by revert r; decide)
    refine WP.seq (WP.mono (doubleBitMod_ok (hs.congr ku.wr) u8 u9 ((g .r10 (by simp)).trans h10) u5
      ((g .r11 (by simp)).trans h11) hw hw' hZ
      (by rw [uv, (ou.val32 (by omega) (by omega)).trans hNd]; exact Nat.mod_lt _ hN))
      fun u₁ ⟨hv, a24', out₁, k'⟩ => ?_)
    refine WP.mono (subi_ok u₁ .r25 (by decide)) fun u₂ e => ?_
    subst e
    have hN₁ : val32 u.mem B (slot w 0) (2 * w) = N := (ou.val32 (by omega) (by omega)).trans hNd
    refine ⟨⟨⟨2 * c' + (u.gpr .r24 >>> 63).toNat, ?_, (ku.trans (k'.trans (Keep.write _ _ _))).mono,
      ou.trans out₁, by rw [mem_write, hv, hN₁, uv, mod_double_bit], ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · simp only [gpr_write, reduceCtorEq, ↓reduceIte]
      have e24 : (u.gpr .r24 >>> 63).toNat = if decide (2 ^ 63 ≤ (u.gpr .r24).toNat) then 1 else 0 := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
        have := (u.gpr .r24).isLt
        split <;> simp_all <;> omega
      rw [a24', Pub.r24_step, e24, show (2 : Nat) ^ (j + 1) = 2 ^ j * 2 from Nat.pow_succ 2 j, ← Nat.mul_assoc]
      have hlt := (u.gpr .r24).isLt
      generalize (u.gpr .r24).toNat = r at hc hlt ⊢
      generalize (256 * c + b) * 2 ^ 56 * 2 ^ j = Y at hc ⊢
      split
      · rename_i hb; simp only [decide_eq_true_eq] at hb
        omega_using [hc, hlt, hb]
      · omega_using [hc, hlt]
    · simp only [gpr_write, reduceCtorEq, ↓reduceIte]; rw [k'.gpr .r5 (by decide)]; exact u5
    · simp only [gpr_write, reduceCtorEq, ↓reduceIte]; rw [k'.gpr .r8 (by decide)]; exact u8
    · simp only [gpr_write, reduceCtorEq, ↓reduceIte]; rw [k'.gpr .r9 (by decide)]; exact u9
    · simp only [gpr_write, reduceCtorEq, ↓reduceIte]; rw [k'.gpr .r30 (by decide)]; exact u30
    · simp only [gpr_write, reduceCtorEq, ↓reduceIte]; rw [k'.gpr .r31 (by decide)]; exact u31
    · simp only [gpr_write, ↓reduceIte]; rw [k'.gpr .r25 (by decide)]
  · rw [a24, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
    omega
  · have hc' : c' = 256 * c + b := by
      have := (u.gpr .r24).isLt
      rw [show (256 * c + b) * 2 ^ 56 * 2 ^ 8 = (256 * c + b) * 2 ^ 64 by rw [Nat.mul_assoc]] at hc
      omega
    rw [← hc']; exact hu

/-- `reduceScan`: the `L ≥ 1` bytes at `D` (`r30`, `r31`) scanned, most
significant first, apart from the working space. -/
theorem reduceScan_ok {s t : State} {B D : Addr} {Z w N L : Nat} (hs : Scr s B Z) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hZ : slot w 4 ≤ Z) (h10 : s.gpr .r10 = off B (slot w 0))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hNd : val32 s.mem B (slot w 0) (2 * w) = N) (hN : 0 < N)
    (hL : 1 ≤ L) (hL' : L < 2 ^ 63) (hrd : ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1)
    (hsep : ∀ i < L, ∀ x, ofs B x < Z → off D i ≠ x)
    (ht : RInv s B w N 0 t) (h30 : t.gpr .r30 = off D 0) (h31 : t.gpr .r31 = BitVec.ofNat 64 L) :
    WP isa reduceScan t (RInv s B w N (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D L))) := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e1 := e 1; have e4 := e 4
  let Inv : Nat → State → Prop := fun i u =>
    RInv s B w N (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D i)) u ∧ u.gpr .r30 = off D i
  refine WP.mono (wp_countdown (cnt := .r31) (N := L) (by omega) (by omega) Inv
    (fun i hi u ⟨hu, u30⟩ _ => ?_) ⟨ht, h30⟩ h31) fun u h => h.1
  have hb : u.mem (off D i) = s.mem (off D i) := by
    refine hu.2.1 _ (Or.inr ?_)
    by_contra hc
    exact hsep i hi (off D i) (by simp only [Mont.ofs, ofs] at hc ⊢; omega) rfl
  refine WP.seq (WP.mono (reduceByte_ok hs hw hw' hZ h10 h11 hNd hN hu u30
    (by rw [hu.1.rd, hu.1.wr]; exact hrd i hi)) fun u₁ ⟨hu₁, a30, a31⟩ => ?_)
  refine WP.mono (subi_ok u₁ .r31 (by decide)) fun u₂ e => ?_
  subst e
  obtain ⟨k₁, o₁, v₁, u5, u8, u9⟩ := hu₁
  refine ⟨⟨⟨(k₁.trans (Keep.write _ _ _)).mono, o₁, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · rw [mem_write, v₁, hb, Pub.bytesAt_succ, VG.Proof.Rsa.os2ip_snoc]
  · simp only [gpr_write, reduceCtorEq, ↓reduceIte]; exact u5
  · simp only [gpr_write, reduceCtorEq, ↓reduceIte]; exact u8
  · simp only [gpr_write, reduceCtorEq, ↓reduceIte]; exact u9
  · simp only [gpr_write, reduceCtorEq, ↓reduceIte]; exact a30
  · simp only [gpr_write, ↓reduceIte]; rw [a31]

/-- `reduce`: `x mod m` into array 1, for `m` (not zero) in array 0 and the
`L ≥ 1` bytes of `x` at `D` (`r30`, `r31`), most significant first, apart from
the working space; only arrays 1–3 change. -/
theorem reduce_ok {s : State} {B D : Addr} {Z w L : Nat} (hs : Scr s B Z) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hZ : slot w 4 ≤ Z) (h10 : s.gpr .r10 = off B (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hN : 0 < val32 s.mem B (slot w 0) (2 * w))
    (h30 : s.gpr .r30 = off D 0) (h31 : s.gpr .r31 = BitVec.ofNat 64 L) (hL : 1 ≤ L) (hL' : L < 2 ^ 63)
    (hrd : ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1)
    (hsep : ∀ i < L, ∀ x, ofs B x < Z → off D i ≠ x) :
    WP isa reduce s fun t =>
      (val32 t.mem B (slot w 1) (2 * w) =
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D L) % val32 s.mem B (slot w 0) (2 * w) ∧
        Mont.Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem) ∧ Keep (redRegs ++ ([.r5, .r8, .r9] : List Reg)) s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4
  have hh : hdrBytes = 256 := rfl
  unfold reduce
  refine WP.seq (WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) h10 h29 1) fun s₁ ⟨⟨a14, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (zeroWords_ok (hs.congr k1.wr) a14 ((k1.gpr _ (by decide)).trans h11) hw hw'
    (by omega)) fun s₂ ⟨⟨_, hz, out₂⟩, k₂⟩ => ?_)
  have k12 := k1.trans k₂
  rw [m1] at out₂
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r5) (by decide) (by decide) ((k12.gpr _ (by decide)).trans h10)
    ((k12.gpr _ (by decide)).trans h29) 1) fun s₃ ⟨⟨a5, m3⟩, k3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r8) (by decide) (by decide)
    ((k3.gpr _ (by decide)).trans ((k12.gpr _ (by decide)).trans h10))
    ((k3.gpr _ (by decide)).trans ((k12.gpr _ (by decide)).trans h29)) 2) fun s₄ ⟨⟨a8, m4⟩, k4⟩ => ?_
  have k14 := (k12.trans k3).trans k4
  refine WP.mono (Pub.base_ok (rd := .r9) (by decide) (by decide) ((k14.gpr _ (by decide)).trans h10)
    ((k14.gpr _ (by decide)).trans h29) 3) fun s₅ ⟨⟨a9, m5⟩, k5⟩ => ?_
  have k15 := k14.trans k5
  have m25 : s₅.mem = s₂.mem := m5.trans (m4.trans m3)
  have o25 : Mont.Outside B (slot w 1) (24 * (w + 2)) s.mem s₅.mem := by
    rw [m25]; exact fun x hx => out₂ x (by simp only [Mont.ofs] at hx ⊢; omega)
  have hNd : val32 s₅.mem B (slot w 0) (2 * w) = val32 s.mem B (slot w 0) (2 * w) :=
    o25.val32 (by omega) (by omega)
  have hrd5 : ∀ i < L, InRegions (s₅.rd ++ s₅.wr) (off D i) 1 := by
    rw [k15.rd, k15.wr]; exact hrd
  have hsep5 : ∀ i < L, ∀ x, ofs B x < Z → off D i ≠ x := hsep
  have hz5 : val32 s₅.mem B (slot w 1) (2 * w) = 0 := by
    rw [m25, Pre.val32_eq_wv]
    exact (wv_eq_zero_iff _ _ _ _).mpr hz
  refine WP.mono (reduceScan_ok (s := s₅) (hs.congr k15.wr) hw hw' hZ ((k5.gpr _ (by decide)).trans
    ((k14.gpr _ (by decide)).trans h10)) ((k15.gpr _ (by decide)).trans h11) hNd hN hL hL' hrd5 hsep5
    ⟨Keep.refl _ _, Mont.Outside.refl _ _ _ _, by rw [hz5, Nat.zero_mod], (k5.gpr _ (by decide)).trans ((k4.gpr _ (by decide)).trans a5),
      (k5.gpr _ (by decide)).trans a8, a9⟩ ((k15.gpr _ (by decide)).trans h30) ((k15.gpr _ (by decide)).trans h31))
    fun t ⟨kt, ot, tv, _, _, _⟩ => ⟨⟨?_, o25.trans ot⟩, (k15.trans kt).mono⟩
  have hbytes : Spec.Rsa.bytesAt s₅.mem D L = Spec.Rsa.bytesAt s.mem D L := by
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    show s₅.mem (off D i) = s.mem (off D i)
    refine o25 _ (Or.inr ?_)
    by_contra hc
    exact hsep i hi (off D i) (by simp only [Mont.ofs, ofs] at hc ⊢; omega) rfl
  rw [tv, hbytes]

end VG.Proof.Bignum.PPC64LE.ModArith
