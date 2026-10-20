module

public import VerifiedGarbage.Impl.Bignum.AArch64.Square
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Clear the existing two-array square buffer. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.Square
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem zeroWide_ok {s : State} {B : Addr} {Z w eA : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .x8 = off B eA) (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (h7 : s.gpr .x7 = 0)
    (hw' : w < 2 ^ 60) (hA : eA + 8 * (2 * w + 2) ≤ Z) :
    WP isa VG.Impl.Bignum.AArch64.Square.zeroWide s fun t => wv t.mem B eA (2 * w + 2) = 0 ∧ Outside B eA (8 * (2 * w + 2)) s.mem t.mem ∧
      Keep [.x14, .x16] s t := by
  have hn := hs.nowrap
  unfold VG.Impl.Bignum.AArch64.Square.zeroWide
  refine WP.seq (WP.mono (WP.keep [.x14, .x16] (Q := fun t => t.gpr .x16 = off B eA ∧
    t.gpr .x14 = BitVec.ofNat 64 (2 * w + 2) ∧ t.mem = s.mem)
    (by brun [h8, h12, ofNat_add_ofNat]; congr 1; all_goals omega) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h16, h14, hm₁⟩, k₁⟩ => ?_)
  have hstep : ∀ j < 2 * w + 2, ∀ t, ZeroInv s B Z eA j t → t.gpr .x14 = BitVec.ofNat 64 (2 * w + 2 - j) →
      WP isa (.block ([st .x7 .x16, next .x16] ++ ([.subImm .x .x14 .x14 1] : List Instr))) t
        fun t' => ZeroInv s B Z eA (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
    intro j hj t hI _
    have t7 : t.gpr .x7 = 0 := (hI.keep.gpr .x7 (by decide)).trans h7
    rw [WP.block_append_iff]
    refine WP.mono (WP.keep [.x16] (Q := fun t₁ => t₁.mem = t.mem.writeW (off B (eA + 8 * j)) (0 : BitVec 64) ∧
      t₁.gpr .x16 = off B (eA + 8 * j + 8))
      (by brun [hI.x16, t7, hI.scr.st (show eA + 8 * j + 8 ≤ Z by omega)]) (by decide) (by decide)
        (by decide +kernel)) fun t₁ ⟨⟨hm, h16'⟩, k₁⟩ => ?_
    refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14', hm', _⟩, k'⟩ => ⟨?_, by rw [h14', k₁.gpr .x14 (by decide)]⟩
    refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
      by rw [k'.gpr .x16 (by decide), h16', Nat.mul_succ, Nat.add_assoc], ?_, ?_⟩
    · rw [hm', hm]
      intro x hx
      rw [writeW_outside t.mem B _ (by omega) x (by omega)]
      exact hI.out x (by omega)
    · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega), hI.val]
      rfl
  refine WP.mono (wp_countdown (N := 2 * w + 2) (by omega) (by omega) (ZeroInv s B Z eA) hstep
    ⟨hs.congr k₁.wr, k₁.mono (by decide), by rw [h16]; rfl, by rw [hm₁]; exact Outside.refl _ _ _ _, rfl⟩ h14)
    fun t hI => ⟨hI.val, hI.out, hI.keep⟩

end VG.Proof.Bignum.AArch64.Square
