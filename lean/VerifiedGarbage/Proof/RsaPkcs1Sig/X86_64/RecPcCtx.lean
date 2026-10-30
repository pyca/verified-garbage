module

public import VerifiedGarbage.Spec.RsaPkcs1Sig.Precomputed
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecoverFrame

/-!
# `vg_rsa_pkcs1_recover_precomputed` on x86-64: the precondition

The shared contract's precondition, by name (`PPreR`): `PreR` for the
original arguments, which the code reads as `vg_rsa_pkcs1_recover` does, and
the precomputed values `pre` (`pre_len` words), the stack arguments 5 and 6,
which only the call reads.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64.RecPc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64 Rec
open VG.Proof.RsaPkcs1Sig.X86_64.Ver (fb kb stkR scrR)

/-- The precomputed values, in bytes. -/
def preR (s : State) : Region := ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩

/-- All seven stack arguments. -/
def argsR (s : State) : Region := ⟨stackArgAddr s 0, 56⟩

/-- The precondition of the original function, and the cache. -/
structure PPreR (s : State) : Prop extends PreR s where
  sp3 : (s.gpr .rsp).toNat + 64 ≤ 2 ^ 64
  args : InRegions s.rd (stackArgAddr s 0) 56
  pre : InRegions s.rd (stackArg s 5) ((stackArg s 6).toNat * 8)
  argsOut : (argsR s).Disjoint (outR s)
  argsScr : (argsR s).Disjoint (scrR s)
  argsStack : (argsR s).Disjoint (stkR s)
  preOut : (preR s).Disjoint (outR s)
  preScr : (preR s).Disjoint (scrR s)
  preStack : (preR s).Disjoint (stkR s)
  preWrap : (stackArg s 5).toNat + (stackArg s 6).toNat * 8 ≤ 2 ^ 64
  preLen : (stackArg s 6).toNat = Spec.Rsa.precomputedWords (s.gpr .rcx).toNat

theorem stackArgs_seven (s : State) :
    (List.range 7).map (stackArg s) = [stackArg s 0, stackArg s 1, stackArg s 2,
      stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6] := rfl

theorem pre_of {s : State}
    (h : (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi verStack).pre s) : PPreR s := by
  sig_pre [Spec.RsaPkcs1Sig.recoverPrecomputedContract, Spec.RsaPkcs1Sig.recoverPrecomputedSig,
    abi, argRegs, verStack, stackArgs_seven, List.append_eq, List.range, List.range.loop] at h
  obtain ⟨sp1, sp3, hrd, hwr, dOn, dOe, dOg, dOs, dOq, dOa, dns, des, dgs, dsq, dsa,
    dRo, -, -, -, dRs, -, -, dKo, dKn, dKe, dKg, dKs, dKq, dKa,
    wO, wN, wE, wG, wS, wQ, ⟨k1, k2⟩, L1, L2, hash, hsl, pl⟩ := h
  have ha : Region.Sub ⟨stackArgAddr s 0, 40⟩ ⟨stackArgAddr s 0, 56⟩ := Region.sub_prefix (by decide)
  refine ⟨⟨sp1, by omega, ?_, hwr, dOn, dOe, dOg, dOs, dOa.sub_right ha, dns, des, dgs, dsa.sub_right ha, dRo,
    dRs, dKo, dKn, dKe, dKg, dKs, dKa.sub_right ha, wO, wN, wE, wG, wS, k1, k2, L1, L2, hash,
    hsl⟩,
    sp3, ?_, ?_, dOa.symm, dsa.symm, dKa.symm, dOq.symm, dsq.symm, dKq.symm, wQ, pl⟩
  · rw [hrd]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨⟨stackArgAddr s 0, 56⟩, by simp, 0, (BitVec.add_zero _).symm, by dsimp only; decide⟩
  · exact ⟨_, by rw [hrd]; simp, Region.contains_self _ _⟩
  · exact ⟨_, by rw [hrd]; simp, Region.contains_self _ _⟩

end VG.Proof.RsaPkcs1Sig.X86_64.RecPc
