module
public import VerifiedGarbage.Impl.Weierstrass.AArch64
public import VerifiedGarbage.Proof.Mont.AArch64.Ops
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionMath
public import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn

import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Function
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem

/-! The P-521 square through the existing field-program call protocol. -/

@[expose] public section

set_option exponentiation.threshold 1024

namespace VG.Proof.Weierstrass.AArch64.Mont

open VG VG.AArch64 VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass.AArch64.Mont
open VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square

/-- The callee's broad vector scratch use does not affect the saved link in `v29`. -/
theorem sqrCall521Core_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod}
    (hM : ModOkA M size fieldPrime s.mem base) (hn : M.n = 9) (htmp : M.tmp = moAt M.n)
    {o a : Nat} (ho : o + 8 * M.n ≤ own M.n) (ha : a + 8 * M.n ≤ own M.n)
    (hA : wordsVal s.mem base a M.n < fieldPrime) :
    WP isa (callProg (Impl.Weierstrass.Mont.p521p.fn "sqr") sqrFn521 o a a) s fun s' =>
      OpKeep M base o s s' ∧ wordsVal s'.mem base o M.n < fieldPrime ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % fieldPrime =
        wordsVal s.mem base a M.n * wordsVal s.mem base a M.n % fieldPrime := by
  apply callProgV29_ok hs hM (.inr (.inr hn)) htmp ho ha ha rfl
    (fun A _ => A < fieldPrime) (fun A _ => A * A) hA
  intro W t hp hval
  rw [hn] at hp hval ⊢
  exact square_fn_ok hp hval

theorem sqrCall521_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod}
    (hM : ModOkA M size Impl.Weierstrass.Mont.p521p.m s.mem base) (hn : M.n = 9)
    (htmp : M.tmp = moAt M.n) {o a : Nat}
    (ho : o + 8 * M.n ≤ own M.n) (ha : a + 8 * M.n ≤ own M.n)
    (hA : wordsVal s.mem base a M.n < Impl.Weierstrass.Mont.p521p.m) :
    WP isa (sqrCall521 o a) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n < Impl.Weierstrass.Mont.p521p.m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % Impl.Weierstrass.Mont.p521p.m =
        wordsVal s.mem base a M.n * wordsVal s.mem base a M.n % Impl.Weierstrass.Mont.p521p.m := by
  have he : Impl.Weierstrass.Mont.p521p.m = fieldPrime := by decide +kernel
  rw [he] at hM hA ⊢
  exact sqrCall521Core_ok hs hM hn htmp ho ha hA

theorem sqr521Ok_eq {n m : Nat} (h : sqr521Ok n m = true) :
    n = 9 ∧ m = Impl.Weierstrass.Mont.p521p.m := by
  simpa only [sqr521Ok, Bool.and_eq_true, beq_iff_eq] using h

end VG.Proof.Weierstrass.AArch64.Mont
