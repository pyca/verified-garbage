module

import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Last
public import VerifiedGarbage.Proof.MillerRabin.Contract
import VerifiedGarbage.Proof.Ffdh.MillerRabin
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Eq
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Exp

/-!
# The Miller–Rabin round on PPC64LE: the round

`core_ok`: the table, the windows and the three squarings leave the mask of
`Proof.MillerRabin.Round.round c b` in `r23` (`Proof.Ffdh.window_round_eq`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.MillerRabin.PPC64LE
open VG.Proof.Bignum (slot slot_sep)
open VG.Proof.RsaKeyGen (wRun wEnd mrE)

/-- The registers the round's core writes. -/
abbrev coreRegs : List Reg := expRegs

theorem core_ok {s : State} {B : Addr} {Z w c b : Nat} (h : MCtx s B Z w) (hc : Consts s.mem B w c)
    (hc3 : 3 ≤ c) (hodd : c % 2 = 1) (h5 : arr s.mem B w 5 = b % c * 2 ^ (64 * w) % c) :
    WP isa core s fun t => MCtx t B Z w ∧ t.gpr .r23 = mask (Proof.MillerRabin.Round.round c b) ∧
      Mut B w s.mem t.mem ∧ Keep coreRegs s t := by
  have hcw : c < 16 ^ (16 * w) := by
    rw [← hc.cand, show (16 : Nat) ^ (16 * w) = 2 ^ (32 * (2 * w)) by
      rw [show (16 : Nat) = 2 ^ 4 from rfl, ← Nat.pow_mul]; congr 1; omega]
    exact val32_lt _ _ _ _
  have hE : mrE c < 16 ^ (16 * w) :=
    Nat.lt_of_le_of_lt (Nat.le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)) hcw
  unfold core
  refine WP.seq (WP.mono (table_ok h hc hc3 hodd h5) fun t₁ ⟨f1, _, tab, y1⟩ => ?_)
  have w1 : WSt expRegs t₁ t₁ B Z w c b :=
    ⟨f1.ctx, f1.consts, tab, Outs.refl _ _ _, Keep.refl _ _, by decide, by decide⟩
  refine WP.seq (WP.mono (windows_ok w1 hc3 hodd y1) fun t₂ e2 => ?_)
  refine WP.seq (WP.mono (last_ok e2.ws hc3 hodd e2.y e2.p (j := 1) (by simp)) fun t₃ ⟨w3, y3, _, p3⟩ => ?_)
  refine WP.seq (WP.mono (last_ok w3 hc3 hodd y3 p3 (j := 2) (by simp)) fun t₄ ⟨w4, y4, _, p4⟩ => ?_)
  refine WP.mono (last_ok w4 hc3 hodd y4 p4 (j := 3) (by simp)) fun t ⟨w5, _, _, p5⟩ =>
    ⟨w5.ctx, ?_, Outs.trans f1.muts (winRanges_mut w5.outs), (f1.keep.trans w5.keep).mono (by decide)⟩
  rw [p5]
  congr 1
  show (wEnd c (wRun c b (mrE c) (16 * w) (16 * w))).2 = _
  rw [VG.Proof.Ffdh.window_round_eq (W := 16 * w) b hc3 hodd hE, ← VG.Proof.Ffdh.rsa_round_eq b hc3 hodd]
  rfl

end VG.Proof.MillerRabin.PPC64LE
