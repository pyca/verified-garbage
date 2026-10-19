module

public import VerifiedGarbage.Proof.Dsa.X86_64.MinusHead
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Dsa.X86_64.MinusStep
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! # Complete subtraction for DSA modulus-minus constants -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

abbrev minusTail : List Instr := [cfFromRbp, .mov .rax (.mem (ix .rsi .r14)), .alu .sbb .rax (.imm 0),
  .store (ix .rbx .r14) .rax, cfToRbp]

/-- Copy the modulus minus a small constant into the ordinary result array.
The input modulus is preserved, including its leading-zero padding. -/
theorem minusCore_ok {s : State} {B : Addr} {Z w amount : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (ha : amount < 2 ^ 31) (hm : amount ≤ wv s.mem B (slot w aN) w) :
    WP isa (.seq (.block (minusHead amount)) (wordLoop 1 minusTail)) s fun t =>
      wv t.mem B (slot w aY) w = wv s.mem B (slot w aN) w - amount ∧
      Outside B (slot w aY) (8 * w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hnowrap := hg.scr.nowrap
  have hy := Nat.le_trans (slot_le (w := w) (show aY < 8 by decide)) hZ
  have hn := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  have hsep := slot_sep (w := w) (show aY ≠ aN by decide)
  refine WP.seq (WP.mono (minusHead_ok hg hZ ha) fun u ⟨hu12, husi, hubx, hfu, hval, hku⟩ => ?_)
  have huN : ∀ k ≤ w, wv u.mem B (slot w aN) k = wv s.mem B (slot w aN) k :=
    fun k hk => hfu.wv (by omega) (by omega)
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 1 → t.mem = u.mem → Keep [.r14] u t → t.cf = u.cf →
      MinusInv u B Z (slot w aN) (slot w aY) amount 1 t := by
    intro t ht14 htm hkt _
    obtain ⟨c, huc, huv⟩ := hval
    refine ⟨hg.scr.congr (hkt.2.2.trans hku.2.2), hkt.mono (by decide), ht14,
      by rw [htm]; exact Outside.refl _ _ _ _, ⟨c, (hkt.gpr (by decide)).trans huc, ?_⟩⟩
    rw [htm, huN 1 (by omega)]
    exact huv
  refine WP.mono (wordLoop_ok (start := 1) (N := w) (by omega) hw'
    (MinusInv u B Z (slot w aN) (slot w aY) amount) h0
    (fun j _ hj t hi => minusStep_ok hubx husi hu12 (by omega) (by omega) (by omega) (by omega) hj hi))
    fun t ht => ?_
  obtain ⟨c, _, hv⟩ := ht.val
  rw [huN w (Nat.le_refl _)] at hv
  have hvlt := wv_lt t.mem B (slot w aY) w
  refine ⟨?_, (hfu.mono (Nat.le_refl _) (by omega)).trans ht.out, (hku.trans ht.keep).mono (by decide)⟩
  cases c
  · simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hv
    omega
  · simp only [Bool.toNat_true, Nat.mul_one] at hv
    omega

end VG.Proof.Dsa.X86_64
