module

public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Blinded.CTBase
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Blinded.Round
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.RoundCallCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Blinded.CTBase
meta import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Blinded.Round
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.MillerRabin.PPC64LE.Blinded
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.RoundCall

/-!
# The blinded Miller–Rabin loop on PPC64LE: constant time of a round

`roundCall_ct`: two runs of `roundCall` with the same witness `a` (public,
as the tape is) leak the same trace, by `Search.roundCall_ct`. `round_ct`: the round's
outcome (`RcPost.r3`), which the branch tests, is a function of `c` and `a`.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.PPC64LE.Blinded

open VG VG.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.MillerRabin.PPC64LE.Search VG.Impl.MillerRabin.PPC64LE.Blinded
open VG.Proof.MillerRabin.PPC64LE (Env arr RoundImpl)
open VG.Proof.MillerRabin.PPC64LE.Search (Prep RcPost roundCall_ok)
open VG.Proof.Bignum (slot Frm wv word off ofs writeW_outside word_writeW_self)
open VG.Proof.Mont (val32)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Two Pins two_post two_taint two_ite)

/-- A round's start: the prepared candidate, the witness `a < c` in array 4,
and the round's stack. -/
def RS (a : BD × Nat) (s : State) : Prop :=
  Prep s a.1.B a.1.L a.1.w a.1.c ∧ arr s.mem a.1.B a.1.w 4 = a.2 ∧ a.2 < a.1.c ∧ 176 ≤ s.sp.toNat ∧
    (below s.sp 176).Disjoint ⟨a.1.B, 8 * a.1.L⟩ ∧ s.sp = a.1.sp

/-- `RS` as the call's precondition, `Search.RC`. -/
theorem roundCall_ct (Ri : RoundImpl) : RelCT isa (Two RS) (roundCall Ri.name Ri.code) fun _ _ => True :=
  (Search.roundCall_ct Ri).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨⟨a.1.B, a.1.L, a.1.w, a.1.c, a.2⟩,
    ⟨h₁.1, h₁.2.1, h₁.2.2.1, h₁.2.2.2.1, h₁.2.2.2.2.1⟩, ⟨h₂.1, h₂.2.1, h₂.2.2.1, h₂.2.2.2.1, h₂.2.2.2.2.1⟩,
    h₁.2.2.2.2.2.trans h₂.2.2.2.2.2.symm⟩) fun _ _ h => h

/-- After `roundCall`. -/
def RP (a : BD × Nat) (s : State) : Prop := ∃ s₀, RS a s₀ ∧ RcPost s₀ a.1.B a.1.L a.1.w a.1.c a.2 s

theorem round_ct (Ri : RoundImpl) :
    RelCT isa (Two RS) (Impl.MillerRabin.PPC64LE.Blinded.round Ri.name Ri.code) fun _ _ => True := by
  have pP : Pins RP [.r10, .r11, .r29, .r31] := pins_env (fun a => a.1) fun a s ⟨s₀, h₀, hp⟩ =>
    ⟨hp.prep.env, hp.sp.trans h₀.2.2.2.2.2⟩
  unfold Impl.MillerRabin.PPC64LE.Blinded.round
  refine RelCT.seq (two_post (Ψ := RP) (roundCall_ct Ri) fun a s h =>
    WP.mono (roundCall_ok Ri h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1) fun t ht => ⟨s, h, ht⟩) ?_
  refine two_ite (fun a s₁ s₂ ⟨_, _, h₁⟩ ⟨_, _, h₂⟩ => by
    rw [VG.PPC64LE.eval_zero, VG.PPC64LE.eval_zero, h₁.r3, h₂.r3]) ?_ ?_
  · exact two_taint _ (Pins.of_imp pP fun _ _ h => h.1) (by taint_decide)
  · exact two_taint _ (Pins.of_imp pP fun _ _ h => h.1) (by taint_decide)

end VG.Proof.MillerRabin.PPC64LE.Blinded
