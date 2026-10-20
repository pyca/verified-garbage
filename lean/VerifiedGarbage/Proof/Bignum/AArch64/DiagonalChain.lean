module


import VerifiedGarbage.Proof.Bignum.AArch64.DiagonalChainTile
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCount
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareMath
public import VerifiedGarbage.Impl.Bignum.AArch64.DiagonalChain
public import VerifiedGarbage.Proof.Bignum.AArch64.DiagonalChainMath
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! The single-carry diagonal pass retains the existing full-width postcondition. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.DiagonalChain
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.Bignum.AArch64.Square
open VG.Proof.MlKem.AArch64 (Keep)

abbrev carryWord (s : State) : (BitVec 64) := (s.gpr .x5 >>> 63) + BitVec.ofNat 64 s.c.toNat

theorem carryWord_nat (s : State) : (carryWord s).toNat = carry s := by
  have h := (s.gpr .x5).isLt
  have hc := Bool.toNat_le s.c
  simp only [carryWord, carry, BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega_arith

theorem diagonal_ok {s : State} {B : Addr} {Z A eb k : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B A) (h9 : s.gpr .x9 = off B eb)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 (4*k)) (h7 : s.gpr .x7 = 0)
    (hk0 : 0 < k) (hk : k < 2 ^ 58)
    (hA : A+16*(4*k)+8 ≤ Z) (hb : eb+8*(4*k) ≤ Z)
    (sb : eb+8*(4*k) ≤ A ∨ A+16*(4*k)+8 ≤ eb) :
    WP isa VG.Impl.Bignum.AArch64.DiagonalChain.code s fun t =>
      wv t.mem B A (2*(4*k)+1) = 2*wv s.mem B A (2*(4*k)) + diagonalValue s.mem B eb (4*k) ∧
      Outside B A (16*(4*k)+8) s.mem t.mem ∧ t.gpr .x16 = off B (A+16*(4*k)) ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x11, .x14, .x16] s t := by
  have hn := hs.nowrap
  unfold VG.Impl.Bignum.AArch64.DiagonalChain.code
  refine WP.seq (WP.mono (WP.keep [.x16, .x11, .x14, .x5] (Q := fun t =>
      t.gpr .x16 = off B A ∧ t.gpr .x11 = off B eb ∧
      t.gpr .x14 = BitVec.ofNat 64 k ∧ t.gpr .x5 = 0 ∧ t.mem = s.mem ∧ t.c = false)
    (by
      brun [h8, h9, h12, h7, Square.shr2_ofNat (show 4*k < 2 ^ 64 by omega)]
      congr 1
      omega) rfl rfl rfl) fun u ⟨⟨h16, h11, h14, h5, hm, hc⟩, ku⟩ => ?_)
  have u7 := (ku.gpr .x7 (by decide)).trans h7
  have h0 : DiagInv u B Z A eb 0 u :=
    ⟨hs.congr ku.wr, Keep.refl _ _, by rw [h16]; rfl, by rw [h11]; rfl,
      Outside.refl _ _ _ _, by simp [wv, carry, h5, hc, diagonalValue, VG.Proof.Bignum.Square.diagonal]⟩
  refine WP.seq (WP.mono (wp_countdown (N := k) (by omega) hk0 (fun j => DiagInv u B Z A eb (4*j))
    (fun j hj t hI _ => diagonalBlockStep_ok u7 hj (by omega) hb (by omega) hI) h0 h14)
    fun v hI => ?_)
  have v7 := (hI.keep.gpr .x7 (by decide)).trans u7
  refine WP.mono (WP.keep [.x5] (Q := fun t =>
      t.mem = v.mem.writeW (off B (A+16*(4*k))) (carryWord v))
    (by brun [v7, carryWord, hI.x16, hI.scr.st (show A+16*(4*k)+8 ≤ Z by omega), add_zero64])
    rfl rfl rfl) fun t ⟨htm, kt⟩ => ?_
  refine ⟨?_, ?_, (kt.gpr .x16 (by decide)).trans hI.x16, ((ku.trans hI.keep).trans kt).mono (by decide)⟩
  · have hv := hI.val
    rw [hm] at hv
    rw [htm, show A+16*(4*k) = A+8*(2*(4*k)) by omega,
      wv_writeW_top _ B A (2*(4*k)) _ (by omega), carryWord_nat]
    simpa only [show 64*(2*(4*k)) = 128*(4*k) by omega] using hv
  · have ho := hI.out
    rw [hm] at ho
    rw [htm]
    exact (ho.mono (o' := A) (n' := 16*(4*k)+8) (Nat.le_refl _) (by omega)).trans
      ((writeW_outside v.mem B (carryWord v) (d := A+16*(4*k)) (by omega)).mono (by omega) (by omega))

end VG.Proof.Bignum.AArch64.DiagonalChain
