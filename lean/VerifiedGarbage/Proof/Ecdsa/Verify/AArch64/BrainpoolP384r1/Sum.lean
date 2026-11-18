module

public import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP384r1.AArch64
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Fixed
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.SumAll

/-! # General complete addition for brainpoolp384r1 verification: `JointKit.sum_full_ok` (`SumAll.lean`) for this curve's `sum` -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP384r1
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64

variable {c : VG.Impl.Ecdsa.AArch64.Cfg}

abbrev sumR : List Nat := JointKit.sumR
abbrev sumSl : List Nat := JointKit.sumSl

/-- The slots `sum` writes: not `EM` or `T`, which the shared `sumW` (of the
addition by a call of `padd`) includes. -/
abbrev sumW : List Nat := JointKit.sumW

theorem sum_full_ok (hc : BaseCfgOk c) {s : State} {base : Addr} (hs : Scr s base size)
    (hM : ModOkA c.MP' size c.C.p s.mem base) (hlt : ∀ i ∈ sumR, sv c base s i < c.C.p) :
    WP isa (sum c) s fun s' =>
      Scr s' base size ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Unch base (slW c sumW) s.mem s'.mem ∧
      ModOkA c.MP' size c.C.p s'.mem base ∧ (sv c base s' RZ < c.C.p ∧ sv c base s' RX < c.C.p ∧ sv c base s' RY < c.C.p) ∧
      (tmv c.C c.n base s' (c.sl RX), tmv c.C c.n base s' (c.sl RY), tmv c.C c.n base s' (c.sl RZ)) =
        rcbAdd (tmv c.C c.n base s (c.sl AP)) (tmv c.C c.n base s (c.sl EXPP))
          (tmv c.C c.n base s (c.sl UX)) (tmv c.C c.n base s (c.sl UY)) (tmv c.C c.n base s (c.sl UZ))
          (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY)) (tmv c.C c.n base s (c.sl RZ)) :=
  JointKit.sum_full_ok hc hs hM hlt

end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1
