module

import VerifiedGarbage.Proof.Bignum.AArch64.SquareCrossRow
import VerifiedGarbage.Proof.Bignum.AArch64.SquareZero
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareMath
public import VerifiedGarbage.Impl.Bignum.AArch64.Square
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Triangular rows form the exact off-diagonal part of the square. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.Square
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- Before row `i`, the buffer holds the cross products of the first `i`
words. Words at and above `2 i` are still zero. -/
structure CrossInv (s₀ : State) (B : Addr) (Z A eb w : Nat) (i : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x11, .x13, .x14, .x16, .x17] s₀ t
  x5 : t.gpr .x5 = off B (A + 8 * i)
  x11 : t.gpr .x11 = off B (eb + 8 * i)
  x13 : t.gpr .x13 = BitVec.ofNat 64 i
  out : Outside B A (8 * (2 * w + 2)) s₀.mem t.mem
  val : wv t.mem B A (2 * w + 2) = crossValue s₀.mem B eb i
  zero : ∀ k, 2 * i ≤ k → k < 2 * w + 2 → word t.mem B (A + 8 * k) = 0

/-- A triangular row extends the exact cross-product value and zero upper words. -/
theorem crossStep_ok {s₀ t : State} {B : Addr} {Z A eb w i : Nat}
    (h9 : s₀.gpr .x9 = off B eb) (h7 : s₀.gpr .x7 = 0)
    (hw : w < 2 ^ 60) (hi : i < w)
    (hA : A+8*(2*w+2) ≤ Z) (hb : eb+8*w ≤ Z)
    (sb : eb+8*w ≤ A ∨ A+8*(2*w+2) ≤ eb)
    (hI : CrossInv s₀ B Z A eb w i t) :
    WP isa VG.Impl.Bignum.AArch64.Square.crossRow t fun t' =>
      CrossInv s₀ B Z A eb w (i+1) t' ∧
      t'.gpr .x6 = t.gpr .x6 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have kp := hI.keep
  refine WP.mono (crossRow_ok hI.scr hI.x5 hI.x11 ((kp.gpr .x9 (by decide)).trans h9)
    hI.x13 ((kp.gpr .x7 (by decide)).trans h7) (by omega) (by omega) (by omega) (by omega))
    fun t' ⟨hv, ho, h5', h11', h13', h6', kt⟩ => ⟨?_, h6'⟩
  have rB : wv t.mem B eb i = wv s₀.mem B eb i := hI.out.wv (by omega) (by omega)
  have rX : word t.mem B (eb+8*i) = word s₀.mem B (eb+8*i) := hI.out.word (by omega) (by omega)
  have z : word t.mem B (A+8*i+8*i) = 0 := by
    rw [show A+8*i+8*i = A+8*(2*i) by omega]
    exact hI.zero _ (Nat.le_refl _) (by omega)
  have old : wv t.mem B (A+8*i) (i+1) = wv t.mem B (A+8*i) i := by
    rw [wv, z]; simp
  rw [rB, rX, ← old] at hv
  have global := wv_change_window (n := 2*w+2) (by omega) (by omega) ho hv
  rw [hI.val] at global
  refine ⟨hI.scr.congr kt.wr, (kp.trans kt).mono (by decide), ?_, h11', h13',
    hI.out.trans (ho.mono (o' := A) (n' := 8*(2*w+2)) (by omega) (by omega)), ?_, ?_⟩
  · rw [h5']; congr 1
  · rw [global, crossValue_succ]
    grind
  · intro k hk hk'
    rw [ho.word (by omega) (by omega)]
    exact hI.zero k (by omega) hk'

/-- Every off-diagonal product is accumulated once within the existing scratch. -/
theorem cross_ok {s : State} {B : Addr} {Z A eb w : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B A) (h9 : s.gpr .x9 = off B eb)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (h7 : s.gpr .x7 = 0)
    (hw1 : 2 ≤ w) (hw : w < 2 ^ 60)
    (hA : A+8*(2*w+2) ≤ Z) (hb : eb+8*w ≤ Z)
    (sb : eb+8*w ≤ A ∨ A+8*(2*w+2) ≤ eb) :
    WP isa VG.Impl.Bignum.AArch64.Square.cross s fun t =>
      wv t.mem B A (2*w+2) = crossValue s.mem B eb w ∧
      Outside B A (8*(2*w+2)) s.mem t.mem ∧
      (∀ k, 2*w ≤ k → k < 2*w+2 → word t.mem B (A+8*k) = 0) ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x11, .x13, .x14, .x16, .x17] s t := by
  have hn := hs.nowrap
  unfold VG.Impl.Bignum.AArch64.Square.cross
  refine WP.seq (WP.mono (zeroWide_ok hs h8 h12 h7 hw hA) fun u ⟨hz, ho, ku⟩ => ?_)
  have u8 := (ku.gpr .x8 (by decide)).trans h8
  have u9 := (ku.gpr .x9 (by decide)).trans h9
  have u12 := (ku.gpr .x12 (by decide)).trans h12
  have sub1 : BitVec.ofNat 64 w - BitVec.ofNat 64 1 = BitVec.ofNat 64 (w-1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith
  refine WP.seq (WP.mono (WP.keep [.x5, .x11, .x13, .x6] (Q := fun t =>
      t.gpr .x5 = off B (A+8) ∧ t.gpr .x11 = off B (eb+8) ∧
      t.gpr .x13 = BitVec.ofNat 64 1 ∧ t.gpr .x6 = BitVec.ofNat 64 (w-1) ∧ t.mem = u.mem)
    (by brun [u8, u9, u12, sub1]) rfl rfl rfl) fun v ⟨⟨h5, h11, h13, h6, hm⟩, kv⟩ => ?_)
  have kAll := ku.trans kv
  have v9 := (kAll.gpr .x9 (by decide)).trans h9
  have v7 := (kAll.gpr .x7 (by decide)).trans h7
  have h0 : CrossInv v B Z A eb w 1 v := by
    refine ⟨hs.congr kAll.wr, Keep.refl _ _, h5, h11, h13, Outside.refl _ _ _ _, ?_, ?_⟩
    · rw [hm, hz]
      simp [crossValue, VG.Proof.Bignum.Square.cross, VG.Proof.Bignum.Square.value]
    · intro k _ hk
      rw [hm]
      exact (wv_eq_zero_iff u.mem B A (2*w+2)).mp hz k hk
  refine WP.mono (wp_countdown (N := w-1) (by omega) (by omega)
    (fun j => CrossInv v B Z A eb w (j+1))
    (fun j hj t hI _ => by
      simpa only [Nat.add_assoc] using (crossStep_ok v9 v7 hw (show j+1 < w by omega) hA hb sb hI))
    h0 h6) fun t ht => ?_
  have heq : w-1+1 = w := by omega
  rw [heq] at ht
  refine ⟨?_, ?_, ht.zero, (kAll.trans ht.keep).mono (by decide)⟩
  · rw [ht.val]
    apply crossValue_congr
    intro j hj
    rw [hm]
    exact ho.word (by omega) (by omega)
  · have ho' := ht.out
    rw [hm] at ho'
    exact ho.trans ho'

end VG.Proof.Bignum.AArch64.Square
