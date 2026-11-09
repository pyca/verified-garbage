module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeInvariant
import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch

/-! Invariants retained by the public five-bit Jacobian loop. -/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

/-- The eight odd entries and cached double are initialized; E is a scratch lookup destination. -/
def nafLive (K : WinCfg) : List Nat :=
  winRo K ++ [K.R.x,K.R.y,K.R.z,K.D.x,K.D.y,K.D.z] ++ jacTreeSlots K 9

structure NafStable (K : WinCfg) (C : Curve) (base : Addr) (P : Point C) (β : Nat → BitVec 8) (s : State) : Prop where
  zero : wordsVal s.mem base K.zero K.M.n = 0
  table : ∀ a, 1 ≤ a → a ≤ 8 →
    InvJ C (tmv C K.M.n base s (Jacobian.tablePt K a).x)
      (tmv C K.M.n base s (Jacobian.tablePt K a).y)
      (tmv C K.M.n base s (Jacobian.tablePt K a).z) (mul (2*a-1) P)
  bits : ∀ t<257, s.mem (off base (K.bits+t))=β t

theorem nafLive_R (K : WinCfg) : ∀ x ∈ [K.R.x,K.R.y,K.R.z], x ∈ nafLive K := by
  intro x hx
  simp only [nafLive,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
  grind

end VG.Proof.Weierstrass.AArch64
