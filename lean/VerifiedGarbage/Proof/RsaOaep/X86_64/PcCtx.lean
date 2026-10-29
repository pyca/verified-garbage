module

public import VerifiedGarbage.Spec.RsaOaep.Precomputed
public import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCall
import VerifiedGarbage.Proof.Framework.Omega

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem stackArgs_nine (s : State) :
    (List.range 9).map (stackArg s) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4,
      stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8] := rfl

/-- The precomputed values, in bytes. -/
def preR (s : State) : Region := ⟨stackArg s 7, (stackArg s 8).toNat * 8⟩

/-- All nine stack arguments. -/
def argsR (s : State) : Region := ⟨stackArgAddr s 0, 72⟩

/-- The precondition of the original function, and the cache. -/
structure PPre (H : Spec.Mgf1.Hash) (s : State) : Prop extends EPre H s where
  sp3 : (s.gpr .rsp).toNat + 80 ≤ 2 ^ 64
  args : InRegions s.rd (stackArgAddr s 0) 72
  pre : InRegions s.rd (stackArg s 7) ((stackArg s 8).toNat * 8)
  argsOut : (argsR s).Disjoint (outR s)
  argsScr : (argsR s).Disjoint (scrR s)
  argsStack : (argsR s).Disjoint (stkR s)
  preOut : (preR s).Disjoint (outR s)
  preScr : (preR s).Disjoint (scrR s)
  preStack : (preR s).Disjoint (stkR s)
  preWrap : (stackArg s 7).toNat + (stackArg s 8).toNat * 8 ≤ 2 ^ 64
  preLen : (stackArg s 8).toNat = Spec.Rsa.precomputedWords (s.gpr .rcx).toNat

theorem pre_of {H G : Spec.Mgf1.Hash} {s : State}
    (h : (Spec.RsaOaep.encryptPrecomputedContract H G abi encStack).pre s) : PPre H s := by
  sig_pre [Spec.RsaOaep.encryptPrecomputedContract, Spec.RsaOaep.encryptPrecomputedSig, abi, argRegs, encStack,
    stackArgs_nine, List.append_eq, List.range, List.range.loop] at h
  obtain ⟨sp1, sp3, hrd, hwr, dOn, dOe, dOl, dOm, dOsd, dOs, dOq, dOa, dns, des, dls, dms, dsds, dsq, dsa,
    dRo, dRn, dRe, dRl, dRm, dRsd, dRs, -, dRa, dKo, dKn, dKe, dKl, dKm, dKsd, dKs, dKq, dKa,
    wO, wN, wE, wL, wM, wSd, wS, wQ, ⟨k1, k2⟩, hsi, L1, L2, hsl, pl⟩ := h
  have ha : Region.Sub ⟨stackArgAddr s 0, 56⟩ ⟨stackArgAddr s 0, 72⟩ := Region.sub_prefix (by decide)
  refine ⟨⟨sp1, by omega, ?_, hwr, dOn, dOe, dOl, dOm, dOsd, dOs, dOa.sub_right ha, dns, des, dls, dms, dsds,
    dsa.sub_right ha, dRo, dRn, dRe, dRl, dRm, dRsd, dRs, dRa.sub_right ha, dKo, dKn, dKe, dKl, dKm, dKsd, dKs,
    dKa.sub_right ha, wO, wN, wE, wL, wM, wSd, wS, k1, k2, hsi, L1, L2,
    by unfold Spec.RsaPss.publicScratchWords Spec.Rsa.publicScratchWords Spec.Rsa.modulusWords at hsl; omega⟩,
    sp3, ?_, ?_, dOa.symm, dsa.symm, dKa.symm, dOq.symm, dsq.symm, dKq.symm, wQ, pl⟩
  · rw [hrd]
    apply Covers.of_sub
    intro r hr
    simp only [rdL, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨⟨stackArgAddr s 0, 72⟩, by simp, 0, (BitVec.add_zero _).symm, by dsimp only; decide⟩
  · exact ⟨_, by rw [hrd]; simp, Region.contains_self _ _⟩
  · exact ⟨_, by rw [hrd]; simp, Region.contains_self _ _⟩

end VG.Proof.RsaOaep.X86_64.Pc
