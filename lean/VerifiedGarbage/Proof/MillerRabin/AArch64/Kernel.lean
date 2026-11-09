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

end VG.Proof.MillerRabin.AArch64
