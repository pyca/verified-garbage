module
public import VerifiedGarbage.Impl.Bignum.AArch64.Square
public import VerifiedGarbage.Proof.Bignum.AArch64.MontMul

import VerifiedGarbage.Proof.Bignum.AArch64.SquareRedcLoop
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! REDC's final pending carry and exact Montgomery relation. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.Square
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem redcFinish_ok {s : State} {B : Addr} {Z e w : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B (e+8*(w-1)))
    (h7 : s.gpr .x7 = 0) (hw : 1 ≤ w) (hZ : e+8*(w+2) ≤ Z) :
    WP isa (.block [next .x16, st .x5 .x16, st .x7 .x16 8]) s fun t =>
      (wv t.mem B e (w+2) = wv s.mem B e w + 2 ^ (64*w)*(s.gpr .x5).toNat ∧
        Outside B (e+8*w) 16 s.mem t.mem) ∧ Keep [.x16] s t := by
  have hn := hs.nowrap
  have hadd : e+8*(w-1)+8 = e+8*w := by omega
  refine WP.mono (WP.keep [.x16] (Q := fun t =>
    t.mem = (s.mem.writeW (off B (e+8*w)) (s.gpr .x5)).writeW (off B (e+8*w+8)) (0 : BitVec 64))
    (by brun [h16, h7, hadd, hs.st (show e+8*w+8 ≤ Z by omega),
      hs.st (show e+8*w+8+8 ≤ Z by omega)]) rfl rfl rfl) fun t ⟨hm, kt⟩ => ?_
  refine ⟨⟨?_, ?_⟩, kt⟩
  · rw [hm, show e+8*w+8 = e+8*(w+1) by omega,
      show w+2 = (w+1)+1 by omega, wv_writeW_top _ B e (w+1) _ (by omega),
      wv_writeW_top _ B e w _ (by omega)]
    simp only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
  · rw [hm]
    exact ((writeW_outside s.mem B (s.gpr .x5) (d := e+8*w) (by omega)).mono
      (Nat.le_refl _) (by omega)).trans
      ((writeW_outside (s.mem.writeW (off B (e+8*w)) (s.gpr .x5)) B (0 : BitVec 64)
        (d := e+8*w+8) (by omega)).mono (by omega) (by omega))

/-- The result satisfies REDC's exact relation whenever the inverse is valid.
The frame and structural register facts are independent of inverse validity. -/
theorem redc_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hZ : slot w 8 ≤ Z) (h8 : s.gpr .x8 = off B (slot w aAcc+16))
    (h10 : s.gpr .x10 = off B (slot w aN)) (h12 : s.gpr .x12 = BitVec.ofNat 64 w)
    (h15 : s.gpr .x15 = minv) (h7 : s.gpr .x7 = 0) (hw1 : 2 ≤ w) (hw : w < 2 ^ 60) :
    WP isa VG.Impl.Bignum.AArch64.Square.redc s fun t =>
      ((((word s.mem B (slot w aN)).toNat*minv.toNat+1) % 2 ^ 64 = 0) →
        ∃ q < 2 ^ (64*w), 2 ^ (64*w)*wv t.mem B (slot w aTmp) (w+2) =
          wv s.mem B (slot w aAcc+16) (2*w) + q*wv s.mem B (slot w aN) w) ∧
      Outside B (slot w aAcc+16) (8*(2*w+2)) s.mem t.mem ∧
      t.gpr .x8 = off B (slot w aTmp) ∧ t.gpr .x10 = off B (slot w aN) ∧
      t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x7 = 0 ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have hA := slot_le (w := w) (show aTmp < 8 by decide)
  have hAT : slot w aAcc+16+8*w = slot w aTmp := by unfold slot aAcc aTmp; omega
  unfold VG.Impl.Bignum.AArch64.Square.redc
  refine WP.seq (WP.mono (WP.keep [.x13, .x5] (Q := fun t =>
    t.gpr .x13 = BitVec.ofNat 64 w ∧ t.gpr .x5 = 0 ∧ t.mem = s.mem)
    (by brun [h12]) rfl rfl rfl) fun u ⟨⟨u13, u5, um⟩, ku⟩ => ?_)
  refine WP.seq (WP.mono (redcRows_ok (hs.congr ku.wr) hZ
    ((ku.gpr .x8 (by decide)).trans h8) ((ku.gpr .x10 (by decide)).trans h10)
    ((ku.gpr .x12 (by decide)).trans h12) ((ku.gpr .x15 (by decide)).trans h15)
    ((ku.gpr .x7 (by decide)).trans h7) u5 u13 hw1 hw) fun v hI => ?_)
  have kAll := ku.trans hI.keep
  have v8 := hI.x8
  rw [hAT] at v8
  have v16 := hI.x16 (show 0 < w by omega)
  have h16' : v.gpr .x16 = off B (slot w aTmp+8*(w-1)) := by
    rw [v16]; congr 1; unfold slot aAcc aTmp; omega
  refine WP.mono (redcFinish_ok hI.scr h16'
    ((kAll.gpr .x7 (by decide)).trans h7) (by omega) (by unfold slot aTmp at *; omega))
    fun t ⟨⟨hv, ho⟩, kt⟩ => ?_
  refine ⟨?_, ?_, (kt.gpr .x8 (by decide)).trans v8,
    ((kAll.trans kt).gpr .x10 (by decide)).trans h10,
    ((kAll.trans kt).gpr .x12 (by decide)).trans h12,
    ((kAll.trans kt).gpr .x7 (by decide)).trans h7,
    (kAll.trans kt).mono (by decide)⟩
  · intro inv
    have invu : ((word u.mem B (slot w aN)).toNat*minv.toNat+1) % 2 ^ 64 = 0 := by
      rw [um]; exact inv
    obtain ⟨q, hq, heq⟩ := hI.val invu
    rw [hAT, show 2*w-w = w by omega, um] at heq
    exact ⟨q, hq, by rw [hv]; exact heq⟩
  · have out := hI.out
    rw [um] at out
    exact (out.mono (o' := slot w aAcc+16) (n' := 8*(2*w+2)) (Nat.le_refl _) (by omega)).trans
      (ho.mono (o' := slot w aAcc+16) (n' := 8*(2*w+2)) (by unfold slot aAcc aTmp; omega)
        (by unfold slot aAcc aTmp; omega))

end VG.Proof.Bignum.AArch64.Square
