module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedRound
import VerifiedGarbage.Proof.Framework.Omega

/-! # Workspace bounds and protected headers of an RSA witness round -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.MillerRabin
open VG.Proof.MillerRabin.X86_64

theorem sharedRoundRanges_le (w : Nat) : ∀ r ∈ sharedRoundRanges w, r.1 + r.2 ≤ slot w 28 := by
  simp only [sharedRoundRanges, sharedMidRanges, witnessRanges, witRanges, Caller.callRanges,
    mutRanges, Proof.MillerRabin.Round.extended, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Caller.pad, slot, hdrBytes, aR1, aX, aAcc, aTmp, aXm, kUsed, kU, kI, kUni, kStat,
    kElen, kP, sFn, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
  and_intros <;> omega_arith

theorem sharedRoundRanges_hdr (w : Nat) {k : Nat}
    (hk : k = kRand ∨ k = kLen ∨ k = kRandLen ∨ k = kChecks ∨ k = kOut ∨ k = kUsedP) :
    ∀ r ∈ sharedRoundRanges w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [sharedRoundRanges, sharedMidRanges, witnessRanges, witRanges, Caller.callRanges,
    mutRanges, Proof.MillerRabin.Round.extended, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Caller.pad, slot, hdrBytes, aR1, aX, aAcc, aTmp, aXm, kUsed, kU, kI, kUni, kStat,
    kElen, kP, sFn, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes, kRand, kLen, kRandLen, kChecks, kE, kOut, kUsedP]
    and_intros <;> omega_arith

theorem sharedRoundRanges_low (w : Nat) : ∀ r ∈ sharedRoundRanges w, 48 ≤ r.1 := by
  simp only [sharedRoundRanges, sharedMidRanges, witnessRanges, witRanges, Caller.callRanges,
    mutRanges, Proof.MillerRabin.Round.extended, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Caller.pad, slot, hdrBytes, aR1, aX, aAcc, aTmp, aXm, kUsed, kU, kI, kUni, kStat,
    kElen, kP, sFn, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
  and_intros <;> omega_arith

end VG.Proof.RsaKeyGen.X86_64
