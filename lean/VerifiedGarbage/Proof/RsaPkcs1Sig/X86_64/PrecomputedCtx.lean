import VerifiedGarbage.Spec.RsaPkcs1Sig.Precomputed
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCorrect
import VerifiedGarbage.Impl.RsaPkcs1Sig.X86_64.Precomputed

namespace VG.Proof.RsaPkcs1Sig.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum.X86_64 Ver

/-- The precomputed values, in bytes. -/
def preR (s : State) : Region := ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩

/-- All seven stack arguments. -/
def argsR (s : State) : Region := ⟨stackArgAddr s 0, 56⟩

/-- The original padding precondition and the additional read-only cache. -/
structure Pre (s : State) : Prop extends PreV s where
  args : InRegions s.rd (stackArgAddr s 0) 56
  argsScr : (argsR s).Disjoint (scrR s)
  argsStack : (argsR s).Disjoint (stkR s)
  pre : InRegions s.rd (stackArg s 5) ((stackArg s 6).toNat * 8)
  preScr : (preR s).Disjoint (scrR s)
  preStack : (preR s).Disjoint (stkR s)
  preWrap : (stackArg s 5).toNat + (stackArg s 6).toNat * 8 ≤ 2 ^ 64
  preLen : (stackArg s 6).toNat = Spec.Rsa.precomputedWords (s.gpr .rsi).toNat

theorem stackArgs_seven (s : State) :
    (List.range 7).map (stackArg s) = [stackArg s 0, stackArg s 1, stackArg s 2,
      stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6] := rfl

/-- The shared signature supplies the precondition for both the original
padding code and the precomputed public operation. -/
theorem pre_of {s : State}
    (h : (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi verStack).pre s) : Pre s := by
  sig_pre [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig,
    abi, argRegs, verStack, stackArgs_seven, List.append_eq] at h
  sig_pre [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig,
    abi, argRegs, verStack, stackArgs_seven, List.append_eq] at h
  obtain ⟨sp1, sp2, hrd, hwr, dns, des, dds, dgs, dsp, dsa, -, -, -, -, dRs, -, -,
    dKn, dKe, dKd, dKg, dKs, dKp, dKa, wN, wE, wD, wG, wS, wP, ⟨k1, k2⟩, L1, L2, hsl, pl⟩ := h
  have ha : Region.Sub ⟨stackArgAddr s 0, 40⟩ ⟨stackArgAddr s 0, 56⟩ := Region.sub_prefix (by decide)
  refine ⟨⟨sp1, by omega, ?_, hwr, dns, des, dds, dgs, dsa.sub_right ha, dRs,
    dKn, dKe, dKd, dKg, dKs, dKa.sub_right ha, wN, wE, wD, wG, wS, k1, k2, L1, L2, hsl⟩,
    ?_, dsa.symm, dKa.symm, ?_, dsp.symm, dKp.symm, wP, pl⟩
  · rw [hrd]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨⟨stackArgAddr s 0, 56⟩, by simp, 0, (BitVec.add_zero _).symm, by dsimp only; decide⟩
  · exact ⟨_, by rw [hrd]; simp, Region.contains_self _ _⟩
  · exact ⟨_, by rw [hrd]; simp, Region.contains_self _ _⟩

end VG.Proof.RsaPkcs1Sig.X86_64.Pc
