module

public import VerifiedGarbage.Spec.RsaPkcs1Enc.Precomputed
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncFrame

/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on x86-64: the precondition

The shared contract's precondition, by name (`PPre`): `EPre` for the
original arguments, which the code before and after the call reads as
`vg_rsa_pkcs1_encrypt` does, and the precomputed values `pre` (`pre_len`
words), the stack arguments 6 and 7, which only the call reads.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- The precomputed values, in bytes. -/
def preR (s : State) : Region := ⟨stackArg s 6, (stackArg s 7).toNat * 8⟩

/-- All eight stack arguments. -/
def argsR (s : State) : Region := ⟨stackArgAddr s 0, 64⟩

/-- The precondition of the original function, and the cache. -/
structure PPre (s : State) : Prop extends EPre s where
  sp3 : (s.gpr .rsp).toNat + 72 ≤ 2 ^ 64
  args : InRegions s.rd (stackArgAddr s 0) 64
  pre : InRegions s.rd (stackArg s 6) ((stackArg s 7).toNat * 8)
  argsOut : (argsR s).Disjoint (outR s)
  argsScr : (argsR s).Disjoint (scrR s)
  argsStack : (argsR s).Disjoint (stkR s)
  preOut : (preR s).Disjoint (outR s)
  preScr : (preR s).Disjoint (scrR s)
  preStack : (preR s).Disjoint (stkR s)
  preWrap : (stackArg s 6).toNat + (stackArg s 7).toNat * 8 ≤ 2 ^ 64
  preLen : (stackArg s 7).toNat = Spec.Rsa.precomputedWords (s.gpr .rcx).toNat

theorem stackArgs_eight (s : State) :
    (List.range 8).map (stackArg s) = [stackArg s 0, stackArg s 1, stackArg s 2,
      stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7] := rfl

theorem pre_of {s : State}
    (h : (Spec.RsaPkcs1Enc.encryptPrecomputedContract abi encStack).pre s) : PPre s := by
  sig_pre [Spec.RsaPkcs1Enc.encryptPrecomputedContract, Spec.RsaPkcs1Enc.encryptPrecomputedSig,
    abi, argRegs, encStack, Impl.RsaPkcs1Enc.X86_64.Encrypt.frameBytes, stackArgs_eight, List.append_eq] at h
  sig_pre [Spec.RsaPkcs1Enc.encryptPrecomputedContract, Spec.RsaPkcs1Enc.encryptPrecomputedSig,
    abi, argRegs, encStack, Impl.RsaPkcs1Enc.X86_64.Encrypt.frameBytes, stackArgs_eight, List.append_eq] at h
  obtain ⟨sp1, sp3, hrd, hwr, dOn, dOe, dOm, dOp, dOs, dOq, dOa, dns, des, dms, dps, dsq, dsa,
    dRo, -, -, -, -, dRs, -, -, dKo, dKn, dKe, dKm, dKp, dKs, dKq, dKa,
    wO, wN, wE, wM, wP, wS, wQ, ⟨k1, k2⟩, hsi, L1, L2, hml, hpl, hsl, pl⟩ := h
  have ha : Region.Sub ⟨stackArgAddr s 0, 48⟩ ⟨stackArgAddr s 0, 64⟩ := Region.sub_prefix (by decide)
  refine ⟨⟨sp1, by omega, ?_, hwr, dOn, dOe, dOm, dOp, dOs, dOa.sub_right ha, dns, des, dms, dps,
    dsa.sub_right ha, dRo, dRs, dKo, dKn, dKe, dKm, dKp, dKs, dKa.sub_right ha, wO, wN, wE, wM, wP, wS,
    k1, k2, hsi, L1, L2, hml, hpl, hsl⟩,
    sp3, ?_, ?_, dOa.symm, dsa.symm, dKa.symm, dOq.symm, dsq.symm, dKq.symm, wQ, pl⟩
  · rw [hrd]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨⟨stackArgAddr s 0, 64⟩, by simp, 0, (BitVec.add_zero _).symm, by dsimp only; decide⟩
  · exact ⟨_, by rw [hrd]; simp, Region.contains_self _ _⟩
  · exact ⟨_, by rw [hrd]; simp, Region.contains_self _ _⟩

end VG.Proof.RsaPkcs1Enc.X86_64.Pc
