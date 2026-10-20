module
public import VerifiedGarbage.Impl.Bignum.AArch64.Square
public import VerifiedGarbage.Proof.Bignum.AArch64.Run

import VerifiedGarbage.Proof.Bignum.AArch64.SquareTiledRow
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! One triangular cross-product row, including its final carry word. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.Square
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem crossTail_ok {s : State} {B : Addr} {Z e eb i : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B (e+8*i))
    (h5 : s.gpr .x5 = off B e) (h11 : s.gpr .x11 = off B (eb+8*i))
    (h13 : s.gpr .x13 = BitVec.ofNat 64 i) (hZ : e+8*i+8 ≤ Z) :
    WP isa (.block [st .x2 .x16, next .x5, next .x11,
      .addImm .x .x13 .x13 1, .subImm .x .x6 .x6 1]) s fun t =>
      (t.mem = s.mem.writeW (off B (e+8*i)) (s.gpr .x2) ∧
        t.gpr .x5 = off B (e+8) ∧ t.gpr .x11 = off B (eb+8*(i+1)) ∧
        t.gpr .x13 = BitVec.ofNat 64 (i+1) ∧
        t.gpr .x6 = s.gpr .x6 - BitVec.ofNat 64 1) ∧ Keep [.x5, .x6, .x11, .x13] s t := by
  refine WP.keep [.x5, .x6, .x11, .x13] ?_ rfl rfl rfl
  brun [h16, h5, h11, h13, hs.st hZ, ofNat_add_ofNat]
  congr 1

theorem crossRow_ok {s : State} {B : Addr} {Z e eb i : Nat}
    (hs : Scr s B Z) (h5 : s.gpr .x5 = off B e)
    (h11 : s.gpr .x11 = off B (eb+8*i)) (h9 : s.gpr .x9 = off B eb)
    (h13 : s.gpr .x13 = BitVec.ofNat 64 i) (h7 : s.gpr .x7 = 0)
    (hi : i < 2 ^ 60) (hA : e+8*(i+1) ≤ Z) (hb : eb+8*(i+1) ≤ Z)
    (sb : e+8*(i+1) ≤ eb ∨ eb+8*(i+1) ≤ e) :
    WP isa VG.Impl.Bignum.AArch64.Square.crossRow s fun t =>
      wv t.mem B e (i+1) = wv s.mem B e i +
        (word s.mem B (eb+8*i)).toNat * wv s.mem B eb i ∧
      Outside B e (8*(i+1)) s.mem t.mem ∧ t.gpr .x5 = off B (e+8) ∧
      t.gpr .x11 = off B (eb+8*(i+1)) ∧ t.gpr .x13 = BitVec.ofNat 64 (i+1) ∧
      t.gpr .x6 = s.gpr .x6 - BitVec.ofNat 64 1 ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x11, .x13, .x14, .x16, .x17] s t := by
  have hn := hs.nowrap
  unfold VG.Impl.Bignum.AArch64.Square.crossRow
  refine WP.seq (WP.mono (WP.keep [.x1, .x2, .x16, .x17] (Q := fun t =>
    t.gpr .x1 = word s.mem B (eb+8*i) ∧ t.gpr .x16 = off B e ∧
    t.gpr .x17 = off B eb ∧ t.gpr .x2 = 0 ∧ t.c = false ∧ t.mem = s.mem)
    (by brun [h11, h5, h9, h7, hs.ld (show eb+8*i+8 ≤ Z by omega)]) rfl rfl rfl)
    fun u ⟨⟨h1, h16, h17, h2, hcf, hm⟩, ku⟩ => ?_)
  have u7 := (ku.gpr .x7 (by decide)).trans h7
  have u13 := (ku.gpr .x13 (by decide)).trans h13
  have h0 : RowInv u B Z e eb 0 u :=
    ⟨hs.congr ku.wr, Keep.refl _ _, by rw [h16]; rfl, by rw [h17]; rfl,
      Outside.refl _ _ _ _, by simp only [carry, h2, hcf, Bool.toNat_false]; rfl,
      by simp only [carry, h2, hcf, Bool.toNat_false]; decide⟩
  refine WP.seq (WP.mono (tiledRow_ok u7 (by omega) (by omega) (by omega)
    (by omega) (Or.inr rfl) u13 h0) fun v hI => ?_)
  have v7 := (hI.keep.gpr .x7 (by decide)).trans u7
  rw [WP.block_append_iff]
  refine WP.mono (carryOut_ok v v7 hI.carry_lt) fun c ⟨⟨hmc, hcarry⟩, kc⟩ => ?_
  have kAll := (ku.trans hI.keep).trans kc
  have c16 := (kc.gpr .x16 (by decide)).trans hI.x16
  have c5 := (kAll.gpr .x5 (by decide)).trans h5
  have c11 := (kAll.gpr .x11 (by decide)).trans h11
  have c13 := (kAll.gpr .x13 (by decide)).trans h13
  refine WP.mono (crossTail_ok (hs.congr kAll.wr) c16 c5 c11 c13 (by omega))
    fun t ⟨⟨htm, ht5, ht11, ht13, ht6⟩, kt⟩ => ?_
  refine ⟨?_, ?_, ht5, ht11, ht13, ?_, (kAll.trans kt).mono (by decide)⟩
  · rw [htm, wv_writeW_top _ B e i _ (by omega), hmc, hcarry]
    have hv := hI.val
    rw [hm, h1] at hv
    exact hv
  · have ho := hI.out
    rw [hm] at ho
    rw [htm, hmc]
    exact (ho.mono (o' := e) (n' := 8*(i+1)) (Nat.le_refl _) (by omega)).trans
      ((writeW_outside v.mem B (c.gpr .x2) (d := e+8*i) (by omega)).mono (by omega) (by omega))
  · rw [ht6, kAll.gpr .x6 (by decide)]

end VG.Proof.Bignum.AArch64.Square
