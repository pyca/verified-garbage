module
public import VerifiedGarbage.Impl.Bignum.AArch64.Square
public import VerifiedGarbage.Proof.Bignum.AArch64.Run

import VerifiedGarbage.Proof.Bignum.AArch64.SquareRedcStep
import VerifiedGarbage.Proof.Bignum.AArch64.SquareTiledRow

/-! Reduction rows are safe for every inverse; cancellation requires a valid one. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.Square
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem redcRow_analyze {s : State} {B : Addr} {Z e eN w n : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B e) (h10 : s.gpr .x10 = off B eN)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (h15 : s.gpr .x15 = minv)
    (h7 : s.gpr .x7 = 0) (hw1 : 2 ≤ w) (hw : w < 2 ^ 60) (hwn : w < n)
    (heZ : e+8*n ≤ Z) (hN : eN+8*w ≤ Z) (hsep : eN+8*w ≤ e) :
    WP isa VG.Impl.Bignum.AArch64.Square.redcRow s fun t => ∃ u < 2 ^ 64,
      wv t.mem B e n + 2 ^ (64*w)*2 ^ 64*(t.gpr .x5).toNat =
        wv s.mem B e n + 2 ^ (64*w)*(s.gpr .x5).toNat + u*wv s.mem B eN w ∧
      (((word s.mem B eN).toNat*minv.toNat+1) % 2 ^ 64 = 0 → word t.mem B e = 0) ∧
      ((s.gpr .x5).toNat ≤ 1 → (t.gpr .x5).toNat ≤ 1) ∧
      Outside B e (8*(w+1)) s.mem t.mem ∧ t.gpr .x8 = off B (e+8) ∧
      t.gpr .x16 = off B (e+8*w) ∧ t.gpr .x13 = s.gpr .x13 - BitVec.ofNat 64 1 ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x8, .x13, .x14, .x16, .x17] s t := by
  have hn := hs.nowrap
  unfold VG.Impl.Bignum.AArch64.Square.redcRow
  refine WP.seq (WP.mono (redcHead_ok hs h8 h10 h15 h7 (by omega_arith))
    fun a ⟨⟨h1, h16, h17, h2, hcf, hm⟩, ka⟩ => ?_)
  have a7 := (ka.gpr .x7 (by decide)).trans h7
  have a12 := (ka.gpr .x12 (by decide)).trans h12
  have h0 : RowInv a B Z e eN 0 a :=
    ⟨hs.congr ka.wr, Keep.refl _ _, by rw [h16]; rfl, by rw [h17]; rfl,
      Outside.refl _ _ _ _, by simp only [carry, h2, hcf, Bool.toNat_false]; rfl,
      by simp only [carry, h2, hcf, Bool.toNat_false]; decide⟩
  refine WP.seq (WP.mono (tiledRow_ok a7 (by omega_arith) hN (by omega_arith)
    (by omega_arith) (Or.inl rfl) a12 h0) fun b hI => ?_)
  have b7 := (hI.keep.gpr .x7 (by decide)).trans a7
  refine WP.seq (WP.mono (carryOut_ok b b7 hI.carry_lt) fun c ⟨⟨hmc, hcarry⟩, kc⟩ => ?_)
  have kAll := (ka.trans hI.keep).trans kc
  have c8 := (kAll.gpr .x8 (by decide)).trans h8
  have c7 := (kAll.gpr .x7 (by decide)).trans h7
  have c16 := (kc.gpr .x16 (by decide)).trans hI.x16
  have c5 := kAll.gpr .x5 (by decide)
  have val := hI.val
  rw [hm, h1] at val
  have ho := hI.out
  rw [hm] at ho
  have hlow : ((word s.mem B eN).toNat*minv.toNat+1) % 2 ^ 64 = 0 → word b.mem B e = 0 :=
    fun inv => redc_low (by omega_arith) inv val
  have top : word c.mem B (e+8*w) = word s.mem B (e+8*w) := by
    rw [hmc]; exact ho.word (by omega_arith) (by omega_arith)
  refine WP.mono (redcTail_ok (hs.congr kAll.wr) c8 c16 c7 (by omega_arith))
    fun t ⟨⟨lo, htm, ht, hc, ht8, ht13⟩, kt⟩ => ?_
  rw [top, c5] at ht
  rw [c5] at hc
  have outTop : Outside B (e+8*w) 8 c.mem t.mem := by
    rw [htm]; exact writeW_outside _ _ _ (by omega_arith)
  have allOut : Outside B e (8*(w+1)) s.mem t.mem := by
    have ot := outTop
    rw [hmc] at ot
    exact (ho.mono (o' := e) (n' := 8*(w+1)) (Nat.le_refl _) (by omega_arith)).trans
      (ot.mono (o' := e) (n' := 8*(w+1)) (by omega_arith) (by omega_arith))
  have pre : wv t.mem B e w = wv b.mem B e w := by
    rw [outTop.wv (by omega_arith) (by omega_arith), hmc]
  have topNew : word t.mem B (e+8*w) = lo := by rw [htm, word_writeW_self]
  have upper : wv t.mem B (e+8*w+8) (n-(w+1)) = wv s.mem B (e+8*w+8) (n-(w+1)) :=
    allOut.wv (by omega_arith) (by omega_arith)
  refine ⟨(redcU (word s.mem B e) minv).toNat, (redcU (word s.mem B e) minv).isLt,
    ?_, ?_, hc, allOut, ht8, (kt.gpr .x16 (by decide)).trans c16, ?_,
    (kAll.trans kt).mono (by decide)⟩
  · rw [wv_at_word _ _ _ _ _ hwn, wv_at_word s.mem _ _ _ _ hwn, pre, topNew, upper]
    have vc : (c.gpr .x2).toNat = carry b := hcarry
    rw [vc] at ht
    grind
  · intro inv
    rw [outTop.word (by omega_arith) (by omega_arith), hmc]
    exact hlow inv
  · rw [ht13, kAll.gpr .x13 (by decide)]

/-- With a valid inverse the canceled word can be shifted out exactly. -/
theorem redcRow_ok {s : State} {B : Addr} {Z e eN w n : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B e) (h10 : s.gpr .x10 = off B eN)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (h15 : s.gpr .x15 = minv)
    (h7 : s.gpr .x7 = 0) (hw1 : 2 ≤ w) (hw : w < 2 ^ 60) (hwn : w < n)
    (heZ : e+8*n ≤ Z) (hN : eN+8*w ≤ Z) (hsep : eN+8*w ≤ e)
    (hinv : ((word s.mem B eN).toNat*minv.toNat+1) % 2 ^ 64 = 0) :
    WP isa VG.Impl.Bignum.AArch64.Square.redcRow s fun t => ∃ u < 2 ^ 64,
      2 ^ 64*(wv t.mem B (e+8) (n-1) + 2 ^ (64*w)*(t.gpr .x5).toNat) =
        wv s.mem B e n + 2 ^ (64*w)*(s.gpr .x5).toNat + u*wv s.mem B eN w ∧
      ((s.gpr .x5).toNat ≤ 1 → (t.gpr .x5).toNat ≤ 1) ∧
      Outside B e (8*(w+1)) s.mem t.mem ∧ t.gpr .x8 = off B (e+8) ∧
      t.gpr .x16 = off B (e+8*w) ∧ t.gpr .x13 = s.gpr .x13 - BitVec.ofNat 64 1 ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x8, .x13, .x14, .x16, .x17] s t := by
  refine WP.mono (redcRow_analyze hs h8 h10 h12 h15 h7 hw1 hw hwn heZ hN hsep)
    fun t ⟨u, hu, hv, hz, hc, ho, ht8, ht16, ht13, kt⟩ => ?_
  have low := hz hinv
  rw [show n = (n-1)+1 by omega_arith, wv_low, low] at hv
  simp only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.zero_add] at hv
  exact ⟨u, hu, by grind, hc, ho, ht8, ht16, ht13, kt⟩

end VG.Proof.Bignum.AArch64.Square
