module
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightTile

import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section
namespace VG.Proof.Bignum.AArch64.ProductEight
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.BlockedRedc

abbrev productColumnRegs := tileRegs ++ [.x15]

structure ProductColumnInv (s : State) (B : Addr) (eQ eT eN k j : Nat) (t : State) : Prop where
  value : wv t.mem B eT (8 * (k + 1)) +
      2 ^ (64 * (8 * j)) * (2 ^ 64) ^ 8 * (t.gpr .x10).toNat =
    wv s.mem B eT (8 * (k + 1)) + wv s.mem B eQ 8 * wv s.mem B eN (8 * j)
  carry : (t.gpr .x10).toNat ≤ 1
  ptrT : t.gpr .x16 = off B (eT + 64 * j)
  ptrN : t.gpr .x17 = off B (eN + 64 * j)
  frame : Outside B eT (64 * (j + 1)) s.mem t.mem
  keep : Keep productColumnRegs s t

theorem decrement_ok {s : State} :
    WP isa (.block [.subImm .x .x15 .x15 1]) s fun t =>
      (t.gpr .x15 = s.gpr .x15 - BitVec.ofNat 64 1 ∧ t.mem = s.mem) ∧
        Keep [.x15] s t := by
  refine WP.keep [.x15] ?_ rfl rfl rfl
  brun []

theorem bit_word {x : Word} (h : x.toNat ≤ 1) :
    ∃ p : Bool, x = BitVec.ofNat 64 p.toNat := by
  by_cases hz : x.toNat = 0
  · exact ⟨false, BitVec.eq_of_toNat_eq hz⟩
  · exact ⟨true, BitVec.eq_of_toNat_eq (by simpa using (show x.toNat = 1 by omega))⟩

/-- Compose overlapping two-block products without losing the pending carry. -/
theorem productColumnStep_ok {s t : State} {B : Addr} {Z eQ eT eN j k : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eQ) (h7 : s.gpr .x7 = 0)
    (hQ : eQ + 64 ≤ Z) (hT : eT + 64 * (k + 1) ≤ Z) (hN : eN + 64 * k ≤ Z)
    (hQT : eQ + 64 ≤ eT ∨ eT + 64 * (k + 1) ≤ eQ)
    (hNT : eN + 64 * k ≤ eT ∨ eT + 64 * (k + 1) ≤ eN)
    (hj : j < k) (hI : ProductColumnInv s B eQ eT eN k j t) :
    WP isa (.block (VG.Impl.Bignum.AArch64.ProductEight.offBlock ++
      ([.subImm .x .x15 .x15 1] : List Instr))) t fun u =>
      ProductColumnInv s B eQ eT eN k (j + 1) u ∧
        u.gpr .x15 = t.gpr .x15 - BitVec.ofNat 64 1 := by
  have hnw := hs.nowrap
  obtain ⟨p, hp⟩ := bit_word hI.carry
  have q := hI.frame.wv (d := eQ) (k := 8) (by omega) (by omega)
  have n := hI.frame.wv (d := eN + 64 * j) (k := 8) (by omega) (by omega)
  apply WP.block_append
  refine WP.mono (offBlock_ok (hs.congr hI.keep.wr)
    ((hI.keep.gpr .x8 (by decide)).trans h8) hI.ptrT hI.ptrN
    ((hI.keep.gpr .x7 (by decide)).trans h7) hp
    hQ (by omega) (by omega) (by omega) (by omega))
    fun a ⟨hav, hac, ha16, ha17, hao, ka⟩ => ?_
  refine WP.mono (decrement_ok (s := a)) fun u ⟨⟨hu15, hum⟩, ku⟩ => ?_
  have hf := wv_window_delta (n := 8 * (k + 1)) (j := 8 * j) (k := 16)
    (by omega : eT + 8 * (8 * (k + 1)) ≤ 2 ^ 64) (by omega)
    (show Outside B (eT + 8 * (8 * j)) (8 * 16) t.mem a.mem from
      by simpa only [show 8 * (8 * j) = 64 * j by omega] using hao)
  have havAligned := hav
  have hoff : eT + 64 * j = eT + 8 * (8 * j) := by omega
  rewrite [hoff] at havAligned
  have he := window_lift hf havAligned
  have hc : (t.gpr .x10).toNat = p.toNat := by
    rw [hp]
    cases p <;> rfl
  have hv := column_value hI.value
    (show wv a.mem B eT (8 * (k + 1)) +
        2 ^ (64 * (8 * j)) * (2 ^ 64) ^ 8 * (2 ^ 64) ^ 8 * (a.gpr .x10).toNat =
      wv t.mem B eT (8 * (k + 1)) +
        2 ^ (64 * (8 * j)) * (wv s.mem B eQ 8 * wv s.mem B (eN + 64 * j) 8) +
        2 ^ (64 * (8 * j)) * (2 ^ 64) ^ 8 * (t.gpr .x10).toNat from by
      simpa only [q, n, hc, Nat.mul_assoc] using he)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ((hI.keep.trans ka).trans ku).mono (by decide)⟩,
    hu15.trans (congrArg (· - BitVec.ofNat 64 1) (ka.gpr .x15 (by decide)))⟩
  · rewrite [hum, ku.gpr .x10 (by decide), pow_blocks_succ, wv_blocks_succ s.mem B eN j]
    exact hv
  · exact Nat.le_trans (Nat.le_of_eq (congrArg BitVec.toNat (ku.gpr .x10 (by decide)))) hac
  · exact ((ku.gpr .x16 (by decide)).trans ha16).trans (congrArg (off B) (by omega))
  · exact ((ku.gpr .x17 (by decide)).trans ha17).trans (congrArg (off B) (by omega))
  · have ho : Outside B (eT + 64 * j) 128 t.mem u.mem := by
      intro x hx
      exact (congrArg (fun m : Mem => m x) hum).trans (hao x hx)
    exact (hI.frame.mono (by omega) (by omega)).trans (ho.mono (by omega) (by omega))

/-- All columns of an eight-limb multiplication row. -/
theorem productColumns_ok {s : State} {B : Addr} {Z eQ eT eN k : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eQ) (h7 : s.gpr .x7 = 0)
    (h10 : s.gpr .x10 = 0)
    (h16 : s.gpr .x16 = off B eT) (h17 : s.gpr .x17 = off B eN)
    (h15 : s.gpr .x15 = BitVec.ofNat 64 k)
    (hQ : eQ + 64 ≤ Z) (hT : eT + 64 * (k + 1) ≤ Z) (hN : eN + 64 * k ≤ Z)
    (hQT : eQ + 64 ≤ eT ∨ eT + 64 * (k + 1) ≤ eQ)
    (hNT : eN + 64 * k ≤ eT ∨ eT + 64 * (k + 1) ≤ eN)
    (hk : 0 < k) (hk' : k < 2 ^ 64) :
    WP isa (countLoop .x15 VG.Impl.Bignum.AArch64.ProductEight.offBlock) s
      (ProductColumnInv s B eQ eT eN k k) := by
  have h0 : ProductColumnInv s B eQ eT eN k 0 s := by
    refine ⟨?_, ?_, h16, h17, Outside.refl _ _ _ _, Keep.refl _ _⟩
    · simp only [h10, show (0 : Word).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero, wv, Nat.zero_add]
    · rw [h10]; exact Nat.zero_le 1
  unfold countLoop
  exact wp_countdown hk' hk (ProductColumnInv s B eQ eT eN k)
    (fun j hj t hI _ => productColumnStep_ok hs h8 h7 hQ hT hN hQT hNT hj hI) h0 h15

/-- With the outer-row bound, the final pending carry is zero. The bound
also admits the all-zero multiplier. -/
theorem productColumns_bounded {s : State} {B : Addr} {Z eQ eT eN k : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eQ) (h7 : s.gpr .x7 = 0)
    (h10 : s.gpr .x10 = 0)
    (h16 : s.gpr .x16 = off B eT) (h17 : s.gpr .x17 = off B eN)
    (h15 : s.gpr .x15 = BitVec.ofNat 64 k)
    (hQ : eQ + 64 ≤ Z) (hT : eT + 64 * (k + 1) ≤ Z) (hN : eN + 64 * k ≤ Z)
    (hQT : eQ + 64 ≤ eT ∨ eT + 64 * (k + 1) ≤ eQ)
    (hNT : eN + 64 * k ≤ eT ∨ eT + 64 * (k + 1) ≤ eN)
    (hk : 0 < k) (hk' : k < 2 ^ 64)
    (hbound : wv s.mem B eT (8 * (k + 1)) ≤ wv s.mem B eN (8 * k)) :
    WP isa (countLoop .x15 VG.Impl.Bignum.AArch64.ProductEight.offBlock) s fun t =>
      ProductColumnInv s B eQ eT eN k k t ∧ t.gpr .x10 = 0 ∧
        wv t.mem B eT (8 * (k + 1)) = wv s.mem B eT (8 * (k + 1)) +
          wv s.mem B eQ 8 * wv s.mem B eN (8 * k) := by
  refine WP.mono (productColumns_ok hs h8 h7 h10 h16 h17 h15 hQ hT hN hQT hNT hk hk')
    fun t hI => ?_
  have hq := wv_lt s.mem B eQ 8
  have hb := wv_lt s.mem B eN (8 * k)
  have hv := hI.value
  have hc := row_carry_zero (radix := (2 ^ 64) ^ 8) (span := 2 ^ (64 * (8 * k)))
    (by decide) hbound (by simpa only [Nat.pow_mul] using hq) hb
    (by simpa only [Nat.mul_comm (2 ^ (64 * (8 * k))), Nat.mul_assoc] using hv)
  have hz : t.gpr .x10 = 0 := BitVec.eq_of_toNat_eq hc
  refine ⟨hI, hz, ?_⟩
  simpa only [hc, Nat.mul_zero, Nat.add_zero] using hv

end VG.Proof.Bignum.AArch64.ProductEight
