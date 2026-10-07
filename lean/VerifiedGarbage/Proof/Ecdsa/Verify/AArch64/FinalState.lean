import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Points

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 (RM')

/-- The numerical and frame facts used by the final signature check.
The point-multiplication proof supplies its group result separately. -/
structure FinalState (c : Cfg) (s₀ : State) (base : Addr) (g : Reg → BitVec 64)
    (s : State) : Prop where
  scr : Scr s base size
  wr : s.wr = s₀.wr
  rd : s.rd = s₀.rd
  fixed : Fixed c base g s.mem
  flag : word s.mem base (c.sl FLAG) =
    mask (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n))
  rm_lt : sv c base s RM' < c.C.n
  rm : toM c.C.n (2 ^ (64 * c.n)) (sv c base s RM') = Fin.ofNat c.C.n (sigR c s₀)
  rz_lt : sv c base s RZ < c.C.p
  unch : Unch base [(0, size)] s₀.mem s.mem
  k : sv c base s K = sigR c s₀
  rx_lt : sv c base s RX < c.C.p


theorem Pts.toFinalState {c : Cfg} {s₀ : State} {base : Addr} {g : Reg → BitVec 64}
    {Q₁ Q₂ : Nat → Fe c.C → Fe c.C → Fe c.C → Prop} {s : State}
    (h : Pts c s₀ base g Q₁ Q₂ s) : FinalState c s₀ base g s :=
  ⟨h.scr,h.wr,h.rd,h.fixed,h.flag,h.rm_lt,h.rm,h.rz_lt,h.unch,h.k,h.rx_lt⟩

end VG.Proof.Ecdsa.Verify.AArch64
