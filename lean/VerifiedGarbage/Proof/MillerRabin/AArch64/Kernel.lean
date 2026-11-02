module

import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerResult
public import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerStages
public import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerFrame
import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerCT
import VerifiedGarbage.Proof.MillerRabin.AArch64.Frame
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrRound
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MillerRabin.AArch64.Correct

/-! # A prepared round for generic RSA and FFDH policies -/

@[expose] public section

namespace VG.Proof.MillerRabin.AArch64

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaKeyGen VG.Proof.RsaKeyGen.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Bignum.Public VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.MlKem.AArch64 (Keep)

structure Kernel where
  run : List (Prog isa)
  nonempty : run ≠ []
  ok : ∀ {s : State} {B : Addr} {Z w c bm b : Nat},
    MrCtx s B Z w c bm → ECtx s.mem B w c → 4 ≤ w → w ≤ 128 →
    slot w aE + 8 * (w + 2) ≤ Z → c % 2 = 1 → 3 ≤ c →
    wv s.mem B (slot w aXm) w = b % c * 2 ^ (64 * w) % c →
    WP isa (seqs run) s fun t =>
      (∃ bm', MrCtx t B Z w c bm') ∧ ECtx t.mem B w c ∧
      word t.mem B (8 * kFlag) = mask (Proof.MillerRabin.Round.round c b) ∧
      Frm B (Caller.callRanges w) s.mem t.mem ∧ Keep mmRegs s t
  ct : RelCT isa (Two Caller.Before) (seqs run) fun _ _ => True

/-- A call of the shared entry point, keeping its workspace for the policy. -/
def Kernel.called (M : Mont) (name : String) (hnf : (VG.Impl.MillerRabin.AArch64.round M.mm).noFrames = true) : Kernel where
  run := [VG.Impl.MillerRabin.AArch64.Caller.call name (VG.Impl.MillerRabin.AArch64.round M.mm)]
  nonempty := by simp
  ok := by exact Caller.call_result_ok M name hnf
  ct := by exact Caller.call_ct M name hnf

private theorem exponent_fits {s : State} {B : Addr} {Z w c bm : Nat}
    (hc : MrCtx s B Z w c bm) : mrE c < 16 ^ (16 * w) := by
  change mrE c < (2 ^ 4) ^ (16 * w)
  rw [← Nat.pow_mul, show 4 * (16 * w) = 64 * w by omega_arith]
  have hn : c < 2 ^ (64 * w) := hc.n ▸ wv_lt s.mem B (slot w aN) w
  exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hn)

private theorem core_fit (w : Nat) : ∀ r ∈ coreRanges w, r.1 + r.2 ≤ 8 * (Caller.callWords w) := by
  intro r hr
  have hm : r ∈ roundRanges w := by
    simp only [coreRanges, List.mem_append] at hr
    rcases hr with ht | he
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ht))
    · exact List.mem_append_left _ (List.mem_append_right _ he)
  have h := roundRanges_lt w r hm
  simp only [Caller.callWords, slot, hdrBytes, aE] at h ⊢
  omega_arith

private theorem inline_ok (M : Mont) {s : State} {B : Addr} {Z w c bm b : Nat}
    (hc : MrCtx s B Z w c bm) (he : ECtx s.mem B w c) (h4 : 4 ≤ w) (h128 : w ≤ 128)
    (hEZ : slot w aE + 8 * (w + 2) ≤ Z) (ho : c % 2 = 1) (h3 : 3 ≤ c)
    (hx : wv s.mem B (slot w aXm) w = b % c * 2 ^ (64 * w) % c) :
    WP isa (seqs (preparedRound M.mm)) s fun t =>
      (∃ bm', MrCtx t B Z w c bm') ∧ ECtx t.mem B w c ∧
      word t.mem B (8 * kFlag) = mask (Proof.MillerRabin.Round.round c b) ∧
      Frm B (Caller.callRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hX : wv s.mem B (slot w aXm) w = Spec.Rsa.powMod b 1 c * 2 ^ (64 * w) % c := by
    simpa only [VG.Proof.Bignum.powMod_eq, Nat.pow_one] using hx
  refine WP.mono (core_ok M h128 hEZ hc he ho h3 (exponent_fits hc) hX) ?_
  rintro t ⟨ht, hEt, hf, hfrm, hk⟩
  have hn : 8 * Caller.callWords w ≤ 2 ^ 64 := by unfold Caller.callWords; omega_arith
  have hregion : Frame [⟨B, 8 * Caller.callWords w⟩] s.mem t.mem := by
    intro x hx'
    apply hfrm x
    intro r hr
    have houtside := hx' ⟨B, 8 * Caller.callWords w⟩ (by simp)
    have hfit := core_fit w r hr
    simp only [Region.Contains, ofs] at houtside ⊢
    omega_arith
  have hmut := keeps_to_frm (core_keeps hn hfrm) hregion
  exact ⟨⟨bm, ht⟩, hEt, hf, hmut.mono (fun r hr => List.mem_append_right _ hr), hk⟩

private theorem before_core {L : VG.Proof.Bignum.AArch64.Ws} {s : State}
    (h : Caller.Before L s) : CorePre L s := by
  obtain ⟨h4, h128, hEZ, c, bm, b, hc, he, ho, h3, hx⟩ := h
  refine ⟨h4, h128, hEZ, c, bm, b, hc, he, ho, by omega_arith, ?_⟩
  simpa only [VG.Proof.Bignum.powMod_eq, Nat.pow_one] using hx

/-- The same computation inlined, for the existing policy proofs. -/
def Kernel.inlined (M : Mont) : Kernel where
  run := preparedRound M.mm
  nonempty := by simp [preparedRound, tabBuild]
  ok := by exact inline_ok M
  ct := by
    exact (core_ct M).mono (fun _ _ h => by
      obtain ⟨L, hs, ht, hsp⟩ := h
      exact ⟨L, before_core hs, before_core ht, hsp⟩) (fun _ _ _ => trivial)

end VG.Proof.MillerRabin.AArch64
