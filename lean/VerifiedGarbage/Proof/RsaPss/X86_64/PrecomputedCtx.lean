import VerifiedGarbage.Spec.RsaPss.Precomputed
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCorrect

namespace VG.Proof.RsaPss.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

variable (G : Spec.Mgf1.Hash)

/-- The precomputed values, in bytes. -/
def preR (s : State) : Region := ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩

/-- All seven stack arguments. -/
def argsR (s : State) : Region := ⟨stackArgAddr s 0, 56⟩

/-- The original padding precondition and the additional read-only cache. -/
structure Pre (s : State) : Prop extends VPre G s where
  args : InRegions s.rd (stackArgAddr s 0) 56
  argsScr : (argsR s).Disjoint (⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ : Region)
  argsStack : (argsR s).Disjoint (vstkR s)
  pre : InRegions s.rd (stackArg s 5) ((stackArg s 6).toNat * 8)
  preScr : (preR s).Disjoint (⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ : Region)
  preStack : (preR s).Disjoint (vstkR s)
  preWrap : (stackArg s 5).toNat + (stackArg s 6).toNat * 8 ≤ 2 ^ 64
  preLen : (stackArg s 6).toNat = Spec.Rsa.precomputedWords (s.gpr .rsi).toNat

theorem stackArgs_seven (s : State) :
    (List.range 7).map (stackArg s) = [stackArg s 0, stackArg s 1, stackArg s 2,
      stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6] := rfl

/-- The shared signature supplies the precondition for both the original
padding code and the precomputed public operation. -/
theorem pre_of {s : State}
    (h : (Spec.RsaPss.verifyPrecomputedContract G G abi verifyStack).pre s) : Pre G s := by
  sig_pre [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig,
    abi, argRegs, verifyStack, stackArgs_seven, List.append_eq] at h
  sig_pre [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig,
    abi, argRegs, verifyStack, stackArgs_seven, List.append_eq] at h
  sig_split h
  rename_i sp1 sp2 hrd hwr dns des dds dgs dsp dsa dRn dRe dRd dRg dRs _ dRa dKn dKe dKd dKg dKs dKp
    dKa wN wE wD wG wS wP _ob1 L1 L2 hsg hsl
  obtain ⟨k1, k2⟩ := _ob1
  have pl := h
  have ha : Region.Sub ⟨stackArgAddr s 0, 40⟩ ⟨stackArgAddr s 0, 56⟩ := Region.sub_prefix (by decide)
  refine ⟨⟨sp1, by omega, ?_, hwr, dns, des, dds, dgs, dsa.sub_right ha,
    dRn, dRe, dRd, dRg, dRs, dRa.sub_right ha,
    dKn, dKe, dKd, dKg, dKs, dKa.sub_right ha, wN, wE, wD, wG, wS, k1, k2, L1, L2, hsg,
    by unfold Spec.RsaPss.scratchWords Spec.Rsa.scratchWords at hsl; omega⟩,
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

end VG.Proof.RsaPss.X86_64.Pc
