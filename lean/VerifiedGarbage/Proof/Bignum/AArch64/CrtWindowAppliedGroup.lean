module
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowTail
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAppliedStep
import VerifiedGarbage.Proof.Bignum.CrtWindowFive

/-! The arithmetic composition of all eight windows in a five-byte group. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowFive (appliedGroup)

theorem appliedGroup_ok (W : Window) (n : Nat) {t : State} {P : Addr} {w : Nat}
    {mi : BitVec 64} {X Xc x E V : Nat} {Q : Prop}
    (hn : n ≤ 8) (hc : TableCtx t P w mi X Xc)
    (ht : CrtWindowFive.CTab t.mem P w X Q x)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) X)
    (hy : wv t.mem P (slot w aY) w < X)
    (hyv : Q → wv t.mem P (slot w aY) w % X = x ^ E * 2 ^ (64 * w) % X)
    (hV : word t.mem P (8 * Crt.sV) = BitVec.ofNat 64 V) (hV' : V < 2 ^ 64)
    (hbit : word t.mem P (8 * Crt.sBit) = 0)
    (hnib : word t.mem P (8 * Crt.sNib) = 0) :
    WP isa (appliedGroup W.code n) t fun u =>
      TableCtx u P w mi X Xc ∧ CrtWindowFive.CTab u.mem P w X Q x ∧
      wv u.mem P (slot w aY) w < X ∧
      (Q → wv u.mem P (slot w aY) w % X =
        x ^ (E * 32 ^ n + V % 32 ^ n) * 2 ^ (64 * w) % X) ∧
      word u.mem P (8 * Crt.sV) = BitVec.ofNat 64 V ∧
      word u.mem P (8 * Crt.sBit) = 0 ∧ word u.mem P (8 * Crt.sNib) = 0 ∧
      Frm P (crtWinRanges w) t.mem u.mem ∧ Keep mmRegs t u := by
  induction n generalizing t E with
  | zero =>
    apply WP.block_nil
    exact ⟨hc, ht, hy, by simpa only [Nat.pow_zero, Nat.mul_one, Nat.mod_one, Nat.add_zero] using hyv, hV, hbit, hnib, Frm.refl _ _ _, Keep.refl _ _⟩
  | succ n ih =>
    unfold appliedGroup
    refine WP.seq (WP.mono (appliedStep_ok W hc ht hw hw' hR hy hyv hV hV'
      (shift := 5 * n) (by omega)) fun a ⟨ca, ta, ya, va, hVa, ba, na, fa, ka⟩ => ?_)
    refine WP.mono (ih (by omega) ca ta ya va hVa ba na) fun u ⟨cu, tu, yu, vu, hVu, bu, nu, fu, ku⟩ =>
      ⟨cu, tu, yu, ?_, hVu, bu, nu, fa.trans fu, (ka.trans ku).mono (by decide)⟩
    intro hQ
    rw [vu hQ, CrtWindowFive.group_reconstruct]

end VG.Proof.Bignum.AArch64.WindowFive
