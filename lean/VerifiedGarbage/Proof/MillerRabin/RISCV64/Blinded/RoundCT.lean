module

public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.CTBase
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.RoundCallCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
meta import VerifiedGarbage.Proof.MillerRabin.RISCV64.Blinded.CTBase
meta import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.RoundCallCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The blinded Miller–Rabin loop on RISC-V: constant time of a round

As on PPC64LE (`Proof/MillerRabin/PPC64LE/Blinded/RoundCT.lean`):
`roundCall_ct`, two runs of `roundCall` with the same witness `a` (public, as
the tape is) leak the same trace, by `Search.roundCall_ct`. `round_ct`: the
round's outcome (`RcPost.a0`), which the branch tests, is a function of `c`
and `a`.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.RISCV64.Blinded

open VG VG.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.MillerRabin.RISCV64.Search VG.Impl.MillerRabin.RISCV64.Blinded
open VG.Proof.MillerRabin.RISCV64 (Env A RoundImpl)
open VG.Proof.MillerRabin.RISCV64.Search (Prep RcPost RcStk roundCall_ok)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Two Pins two_post two_taint two_ite)

/-- A round's start: the prepared candidate, the witness `a < c` in array 4,
and the round's stack. -/
def RS (a : BD × Nat) (s : State) : Prop :=
  Prep s a.1.B a.1.L a.1.w a.1.c ∧ A s.mem a.1.B a.1.w 4 = a.2 ∧ a.2 < a.1.c ∧ RcStk s a.1.B a.1.L ∧
    s.sp = a.1.sp

/-- `RS` as the call's precondition, `Search.RC`. -/
theorem roundCall_ct (Ri : RoundImpl) : RelCT isa (Two RS) (roundCall Ri.name Ri.code) fun _ _ => True :=
  (Search.roundCall_ct Ri).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨⟨a.1.B, a.1.L, a.1.w, a.1.c, a.2⟩,
    ⟨h₁.1, h₁.2.1, h₁.2.2.1, h₁.2.2.2.1⟩, ⟨h₂.1, h₂.2.1, h₂.2.2.1, h₂.2.2.2.1⟩,
    h₁.2.2.2.2.trans h₂.2.2.2.2.symm⟩) fun _ _ h => h

/-- After `roundCall`. -/
def RP (a : BD × Nat) (s : State) : Prop := ∃ s₀, RS a s₀ ∧ RcPost s₀ a.1.B a.1.L a.1.w a.1.c a.2 s

theorem round_ct (Ri : RoundImpl) :
    RelCT isa (Two RS) (Impl.MillerRabin.RISCV64.Blinded.round Ri.name Ri.code) fun _ _ => True := by
  have pP : Pins RP [.a7, .s5, .t0, .s6] := pins_env (fun a => a.1) fun a s ⟨s₀, h₀, hp⟩ =>
    ⟨hp.prep.env, hp.sp.trans h₀.2.2.2.2⟩
  unfold Impl.MillerRabin.RISCV64.Blinded.round
  refine RelCT.seq (two_post (Ψ := RP) (roundCall_ct Ri) fun a s h =>
    WP.mono (roundCall_ok Ri h.1 h.2.1 h.2.2.1 h.2.2.2.1.1 h.2.2.2.1.2.1 h.2.2.2.1.2.2) fun t ht => ⟨s, h, ht⟩) ?_
  refine two_ite (fun a s₁ s₂ ⟨_, _, h₁⟩ ⟨_, _, h₂⟩ => by
    rw [Steps.eval_zero, Steps.eval_zero, h₁.a0, h₂.a0]) ?_ ?_
  · exact two_taint _ (Pins.of_imp pP fun _ _ h => h.1) (by taint_decide)
  · exact two_taint _ (Pins.of_imp pP fun _ _ h => h.1) (by taint_decide)

end VG.Proof.MillerRabin.RISCV64.Blinded
