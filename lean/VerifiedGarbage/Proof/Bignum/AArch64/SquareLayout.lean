module

public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega

/-! The square reuses exactly the two existing scratch arrays. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.Square
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64

theorem scratch_arrays {s t : State} {B : Addr} {w : Nat}
    (ho : Outside B (slot w aAcc+16) (8*(2*w+2)) s.mem t.mem) :
    Arrays B w [aAcc, aTmp] s.mem t.mem := by
  intro x hx
  have h1 := hx aAcc (by simp)
  have h2 := hx aTmp (by simp)
  exact ho x (by
    have hAT : slot w aAcc+8*(w+2) = slot w aTmp := by unfold slot aAcc aTmp; omega
    omega)

theorem goodW_width {L : Ws} {s : State} (h : GoodW L s) : L.w < 2 ^ 60 := by
  obtain ⟨_, hg, hz⟩ := h
  have hn := hg.scr.nowrap
  unfold slot hdrBytes at hz
  omega_arith

end VG.Proof.Bignum.AArch64.Square
