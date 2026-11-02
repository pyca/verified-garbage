module

public import VerifiedGarbage.Impl.Rsa.AArch64.Keys
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
public import VerifiedGarbage.Proof.Rsa.AArch64.Div
public import VerifiedGarbage.Proof.Rsa.Ranges

/-! # The contract of the inverse on AArch64

`InvLaw`: what `Keys.inverse` does (`InvFinish.lean`'s `inverse_ok`), for
its callers to use without importing the algebra of its proof; the
registrations supply the instance (`Instances.lean`).

For `[u] = a` and `[v] = [m]` odd and above 1, `w` words each, it leaves
`gcd(a, m)` in `[v]` and `y < m` with `m ∣ y a - gcd(a, m)` in `[x₂]`;
it writes only the arrays `u`, `v`, `x₁`, `x₂` and `t`, and the registers
`x11`, `x12` and `stepRegs`.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

class InvLaw : Prop where
  inverse_ok {s : State} {B : Addr} {Z w : Nat} {iU iV iX₁ iX₂ iM iT : Nat} (h : Ws s B Z w)
    (hU : iU < 16) (hV : iV < 16) (hX₁ : iX₁ < 16) (hX₂ : iX₂ < 16) (hM : iM < 16) (hT : iT < 16)
    (dUV : iU ≠ iV) (dUX₁ : iU ≠ iX₁) (dUX₂ : iU ≠ iX₂) (dUM : iU ≠ iM) (dUT : iU ≠ iT) (dVX₁ : iV ≠ iX₁)
    (dVX₂ : iV ≠ iX₂) (dVM : iV ≠ iM) (dVT : iV ≠ iT) (dX : iX₁ ≠ iX₂) (dX₁M : iX₁ ≠ iM) (dX₁T : iX₁ ≠ iT)
    (dX₂M : iX₂ ≠ iM) (dX₂T : iX₂ ≠ iT) (dMT : iM ≠ iT) (hU0 : word s.mem B (slot w iU + 8 * w) = 0)
    (hVM : wv s.mem B (slot w iV) w = wv s.mem B (slot w iM) w) (hX1 : wv s.mem B (slot w iX₁) w = 1)
    (hX2 : wv s.mem B (slot w iX₂) w = 0) :
    WP isa (inverse iU iV iX₁ iX₂ iM iT) s fun t =>
      t.gpr .x0 = B ∧ Frm B [ar w iU, ar w iV, ar w iX₁, ar w iX₂, ar w iT] s.mem t.mem ∧
      Keep (.x11 :: .x12 :: stepRegs) s t ∧
      (wv s.mem B (slot w iM) w % 2 = 1 → 1 < wv s.mem B (slot w iM) w →
        wv t.mem B (slot w iV) w = Nat.gcd (wv s.mem B (slot w iU) w) (wv s.mem B (slot w iM) w) ∧
        ((wv s.mem B (slot w iM) w : Nat) : Int) ∣
          (wv t.mem B (slot w iX₂) w : Int) * wv s.mem B (slot w iU) w - wv t.mem B (slot w iV) w ∧
        wv t.mem B (slot w iX₂) w < wv s.mem B (slot w iM) w)

end VG.Proof.Rsa.AArch64
