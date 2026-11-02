module
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRound

import VerifiedGarbage.Proof.Framework.Omega

/-! # The shared round preserves DSA's tape pointers and witness counters -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin VG.Proof.MillerRabin.X86_64 VG.Proof.Ffdh.X86_64.ParameterCandidate

theorem round_header_ranges {w k : Nat} (hk : k < 32)
    (hne : k ≠ 22 ∧ k ≠ 26 ∧ k ≠ 27 ∧ k ≠ 28 ∧ k ≠ 31) :
    ∀ r ∈ witnessRoundRanges w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
  simp only [witnessRoundRanges, Caller.callRanges, mutRanges, Proof.MillerRabin.Round.extended,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Caller.pad, slot, hdrBytes, aAcc, aTmp, aXm, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
  and_intros <;> omega

end VG.Proof.Dsa.X86_64.Generation
