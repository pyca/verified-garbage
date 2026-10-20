module
public import VerifiedGarbage.Impl.Bignum.AArch64.FastFinish
public import VerifiedGarbage.Proof.Bignum.AArch64.Run

import VerifiedGarbage.Proof.Bignum.AArch64.FastFinishSelTile
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCount
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section
namespace VG.Proof.Bignum.AArch64.FastFinish
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem sel_ok {s : State} {B : Addr} {Z n eA eT eo : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .x8 = off B eA) (h6 : s.gpr .x6 = off B eT) (h5 : s.gpr .x5 = off B eo)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 (4*n)) {lt : Bool} (hc : s.c = !lt)
    (hw : 1 ≤ n) (hw' : (4*n) < 2 ^ 31) (hA : eA + 8 * (4*n) ≤ Z) (hT : eT + 8 * (4*n) ≤ Z) (ho : eo + 8 * (4*n) ≤ Z)
    (sA : eo + 8 * (4*n) ≤ eA ∨ eA + 8 * (4*n) ≤ eo) (sT : eo + 8 * (4*n) ≤ eT ∨ eT + 8 * (4*n) ≤ eo) :
    WP isa VG.Impl.Bignum.AArch64.FastFinish.sel s fun t =>
      wv t.mem B eo (4*n) = (if lt then wv s.mem B eA (4*n) else wv s.mem B eT (4*n)) ∧
      Outside B eo (8 * (4*n)) s.mem t.mem ∧ Keep [.x3, .x4, .x5, .x6, .x14, .x16] s t := by
  have hn := hs.nowrap
  unfold VG.Impl.Bignum.AArch64.FastFinish.sel
  refine WP.seq (WP.mono (WP.keep [.x14, .x16] (Q := fun t => t.gpr .x16 = off B eA ∧
    t.gpr .x14 = BitVec.ofNat 64 n ∧ t.c = s.c ∧ t.mem = s.mem) (by
      brun [h8, h12, Square.shr2_ofNat (show 4*n < 2 ^ 64 by omega)]
      congr 1
      omega)
    (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨⟨h16, h14, hc₁, hm₁⟩, k₁⟩ => ?_)
  have h0 : SelInv s₁ B Z eA eT eo lt 0 s₁ :=
    ⟨hs.congr k₁.wr, Keep.refl _ _, by rw [h16]; rfl, by rw [k₁.gpr .x6 (by decide), h6]; rfl,
      by rw [k₁.gpr .x5 (by decide), h5]; rfl, hc₁.trans hc, Outside.refl _ _ _ _, by cases lt <;> rfl⟩
  refine WP.mono (wp_countdown (N := n) (by omega) (by omega) (fun j => SelInv s₁ B Z eA eT eo lt (4*j))
      (fun j hj _ hI _ => selTile_ok hA hT ho sA sT hj hI) h0 h14)
    fun t hI => ⟨by rw [hI.val, hm₁], by rw [← hm₁]; exact hI.out, (k₁.trans hI.keep).mono (by decide)⟩

end VG.Proof.Bignum.AArch64.FastFinish
