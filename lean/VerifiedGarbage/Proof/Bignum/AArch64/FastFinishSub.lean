module
public import VerifiedGarbage.Impl.Bignum.AArch64.FastFinish
public import VerifiedGarbage.Proof.Bignum.AArch64.Run

import VerifiedGarbage.Proof.Bignum.AArch64.FastFinishSubTile
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCount
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section
namespace VG.Proof.Bignum.AArch64.FastFinish
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem sub_ok {s : State} {B : Addr} {Z n eA eN eT : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .x8 = off B eA) (h10 : s.gpr .x10 = off B eN) (h6 : s.gpr .x6 = off B eT)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 (4*n)) (h7 : s.gpr .x7 = 0) (hw : 1 ≤ n) (hw' : (4*n) < 2 ^ 31)
    (hA : eA + 8 * (4*n + 1) ≤ Z) (hN : eN + 8 * (4*n) ≤ Z) (hT : eT + 8 * (4*n) ≤ Z)
    (sA : eT + 8 * (4*n) ≤ eA ∨ eA + 8 * (4*n + 1) ≤ eT) (sN : eT + 8 * (4*n) ≤ eN ∨ eN + 8 * (4*n) ≤ eT) :
    WP isa VG.Impl.Bignum.AArch64.FastFinish.sub s fun t => ∃ c : Bool,
      t.c = !decide ((word s.mem B (eA + 8 * (4*n))).toNat < c.toNat) ∧
      wv t.mem B eT (4*n) + wv s.mem B eN (4*n) = wv s.mem B eA (4*n) + 2 ^ (64 * (4*n)) * c.toNat ∧
      Outside B eT (8 * (4*n)) s.mem t.mem ∧ Keep [.x3, .x4, .x13, .x14, .x16, .x17] s t := by
  have hn := hs.nowrap
  unfold VG.Impl.Bignum.AArch64.FastFinish.sub
  refine WP.seq (WP.mono (WP.keep [.x3, .x13, .x14, .x16, .x17] (Q := fun t => t.gpr .x16 = off B eA ∧
    t.gpr .x17 = off B eN ∧ t.gpr .x13 = off B eT ∧ t.gpr .x14 = BitVec.ofNat 64 n ∧ t.c = true ∧
    t.mem = s.mem) (by
      brun [h8, h10, h6, h12, h7, Square.shr2_ofNat (show 4*n < 2 ^ 64 by omega)]
      congr 1
      omega) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h16, h17, h13, h14, hc₁, hm₁⟩, k₁⟩ => ?_)
  have h0 : SubInv s₁ B Z eA eN eT 0 s₁ :=
    ⟨hs.congr k₁.wr, Keep.refl _ _, by rw [h16]; rfl, by rw [h17]; rfl, by rw [h13]; rfl,
      Outside.refl _ _ _ _, by rw [hc₁]; rfl⟩
  refine WP.seq (WP.mono (wp_countdown (N := n) (by omega) (by omega) (fun j => SubInv s₁ B Z eA eN eT (4*j))
    (fun j hj t hI _ => subTile_ok (by omega) hN hT (by omega) sN hj hI) h0 h14) fun t hI => ?_)
  have t7 : t.gpr .x7 = 0 := (hI.keep.gpr .x7 (by decide)).trans ((k₁.gpr .x7 (by decide)).trans h7)
  have hX : word t.mem B (eA + 8 * (4*n)) = word s.mem B (eA + 8 * (4*n)) := by
    rw [hI.out.word (by omega) (by omega), hm₁]
  refine WP.mono (WP.keep [.x3] (Q := fun t' => t'.mem = t.mem ∧
      t'.c = decide (2 ^ 64 ≤ (word t.mem B (eA + 8 * (4*n))).toNat + (~~~(0 : BitVec 64)).toNat + t.c.toNat))
    (by brun [hI.x16, t7, hI.scr.ld (show eA + 8 * (4*n) + 8 ≤ Z by omega)])
    (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨hm', hc'⟩, k'⟩ => ?_
  refine ⟨!t.c, ?_, ?_, ?_, ((k₁.trans hI.keep).trans k').mono (by decide)⟩
  · rw [hc', top_borrow, hX]
  · rw [hm', ← hm₁]; exact hI.val
  · rw [hm', ← hm₁]; exact hI.out

end VG.Proof.Bignum.AArch64.FastFinish
