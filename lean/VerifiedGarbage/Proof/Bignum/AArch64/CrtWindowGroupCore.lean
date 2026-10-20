module
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowCore

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowStep
import VerifiedGarbage.Proof.Bignum.CrtWindowFive
import Mathlib.Data.Int.ModEq

/-! The arithmetic composition of all eight windows in a five-byte group. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowFive (groupWindows)

theorem groupWindows_ok (M : Mont) (S : Selector) (n : Nat) {t : State} {P : Addr} {w : Nat}
    {mi : BitVec 64} {X Xc x E V : Nat} {Q : Prop}
    (hn : n ≤ 8) (hc : TableCtx t P w mi X Xc)
    (ht : CrtWindowFive.CTab t.mem P w X Q x)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) X)
    (hy : wv t.mem P (slot w aY) w < X)
    (hyv : Q → wv t.mem P (slot w aY) w % X = x ^ E * 2 ^ (64 * w) % X)
    (hV : word t.mem P (8 * Crt.sV) = BitVec.ofNat 64 V) (hV' : V < 2 ^ 64) :
    WP isa (groupWindows M.mm S.code n) t fun u =>
      TableCtx u P w mi X Xc ∧ CrtWindowFive.CTab u.mem P w X Q x ∧
      wv u.mem P (slot w aY) w < X ∧
      (Q → wv u.mem P (slot w aY) w % X =
        x ^ (E * 32 ^ n + V % 32 ^ n) * 2 ^ (64 * w) % X) ∧
      word u.mem P (8 * Crt.sV) = BitVec.ofNat 64 V ∧
      Frm P (crtWinRanges w) t.mem u.mem ∧ Keep mmRegs t u := by
  induction n generalizing t E with
  | zero =>
    apply WP.block_nil
    exact ⟨hc, ht, hy, by simpa only [Nat.pow_zero, Nat.mul_one, Nat.mod_one, Nat.add_zero] using hyv, hV, Frm.refl _ _ _, Keep.refl _ _⟩
  | succ n ih =>
    unfold groupWindows
    refine WP.seq (WP.mono (windowStep_ok M S hc ht hw hw' hR hy hyv hV hV'
      (shift := 5 * n) (by omega)) fun a ⟨ca, ta, ya, va, hVa, fa, ka⟩ => ?_)
    refine WP.mono (ih (by omega) ca ta ya va hVa) fun u ⟨cu, tu, yu, vu, hVu, fu, ku⟩ =>
      ⟨cu, tu, yu, ?_, hVu, fa.trans fu, (ka.trans ku).mono (by decide)⟩
    intro hQ
    rw [vu hQ, CrtWindowFive.group_reconstruct]

end VG.Proof.Bignum.AArch64.WindowFive
