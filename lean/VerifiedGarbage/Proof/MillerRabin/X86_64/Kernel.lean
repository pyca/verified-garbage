module

import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerResult
public import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages
public import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerCall
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerCT

/-! # A callable prepared round for generic RSA and FFDH policies -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.MlKem.X86_64 (Keep)

/-- A prepared round, including the memory below the caller's stack pointer
that its actual call may modify. The Montgomery context remains reusable. -/
structure Kernel where
  run : Prog isa
  ok : ∀ {s : State} {B : Addr} {Z w c bm b : Nat} {mi : BitVec 64},
    MrCtx s B Z w mi c bm → ECtx s.mem B w c → MrDims B Z w → slot w 28 ≤ Z →
    Caller.Room s B Z → c % 2 = 1 → 3 ≤ c →
    wv s.mem B (slot w aXm) w = b % c * 2 ^ (64 * w) % c →
    WP isa run s fun t =>
      (∃ bm', MrCtx t B Z w mi c bm') ∧ ECtx t.mem B w c ∧
      word t.mem B (8 * kFlag) = mask (Proof.MillerRabin.Round.round c b) ∧
      WorkFrame B (Caller.callRanges w) [below (s.gpr .rsp) 128] s.mem t.mem ∧
      Keep mmRegs s t
  ct : RelCT isa (Two Caller.Before) run fun _ _ => True

/-- Use the selected Montgomery backend's shared Miller–Rabin entry point. -/
def Kernel.called (v : RoundImpl) : Kernel where
  run := VG.Impl.MillerRabin.X86_64.Caller.call v.name v.code
  ok := by exact Caller.call_result_ok v
  ct := by exact Caller.call_ct v

end VG.Proof.MillerRabin.X86_64
