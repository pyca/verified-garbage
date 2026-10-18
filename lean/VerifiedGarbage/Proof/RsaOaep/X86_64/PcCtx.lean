module

public import VerifiedGarbage.Spec.RsaOaep.AnyHash
public import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCT
public import VerifiedGarbage.Impl.RsaOaep.X86_64.Precomputed
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCall

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- The precomputed values, in bytes. -/
def preR (s : State) : Region := ⟨stackArg s 8, (stackArg s 9).toNat * 8⟩

/-- All fourteen stack arguments. -/
def argsR (s : State) : Region := ⟨stackArgAddr s 0, 112⟩

/-- The caller's read-only buffers. -/
def rdP (H : Spec.Mgf1.Hash) (s : State) : List Region :=
  [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 0, (stackArg s 1).toNat⟩,
    ⟨stackArg s 2, (stackArg s 3).toNat⟩, ⟨stackArg s 4, H.len⟩, preR s, ⟨tabH s, 24⟩, ⟨tabG s, 24⟩,
    ⟨stackArgAddr s 0, 112⟩]

/-- The precondition of the original function, and the cache. -/
structure PPre (H : Spec.Mgf1.Hash) (s : State) : Prop extends EPre H s where
  args : InRegions s.rd (stackArgAddr s 0) 112
  pre : InRegions s.rd (stackArg s 8) ((stackArg s 9).toNat * 8)
  preOut : (preR s).Disjoint (outR s)
  preScr : (preR s).Disjoint (scrR s)
  preStack : (preR s).Disjoint (stkR s)
  preWrap : (stackArg s 8).toNat + (stackArg s 9).toNat * 8 ≤ 2 ^ 64
  preLen : (stackArg s 9).toNat = Spec.Rsa.precomputedWords (s.gpr .rcx).toNat
  seedLen : (stackArg s 5).toNat = H.len
  rdEq : s.rd = rdP H s

variable {H : Spec.Mgf1.Hash} {s : State}

theorem PPre.argsOut (hp : PPre H s) : (argsR s).Disjoint (outR s) := hp.d_out_args.symm
theorem PPre.argsScr (hp : PPre H s) : (argsR s).Disjoint (scrR s) := hp.d_scr_args.symm
theorem PPre.argsStack (hp : PPre H s) : (argsR s).Disjoint (stkR s) := hp.d_stk_args.symm

/-- The contract's precondition: the selectors are of `hashIds`, and `PPre`
for the hash function `H` that `hash` names. -/
theorem pre_of (h : (Spec.RsaOaep.encryptAnyContract abi encStack).pre s) :
    selH s ∈ Spec.RsaOaep.hashIds ∧ selG s ∈ Spec.RsaOaep.hashIds ∧
      ∀ H, Spec.HashId.mgf1 (selH s) = some H → PPre H s := by
  sig_pre [Spec.RsaOaep.encryptAnyContract, Spec.RsaOaep.encryptAnySig, abi, argRegs, encStack,
    stackArgs_fourteen, List.append_eq] at h
  sig_pre [Spec.RsaOaep.encryptAnyContract, Spec.RsaOaep.encryptAnySig, abi, argRegs, encStack,
    stackArgs_fourteen, List.append_eq] at h
  obtain ⟨sp1, sp3, hrd, hwr, dOn, dOe, dOl, dOm, dOsd, dOs, dOq, dOtH, dOtG, dOa, dns, des, dls, dms, dsds, dsq,
    dstH, dstG, dsa, dRo, dRn, dRe, dRl, dRm, dRsd, dRs, -, -, -, dRa, dKo, dKn, dKe, dKl, dKm, dKsd, dKs, dKq,
    dKtH, dKtG, dKa, wO, wN, wE, wL, wM, wSd, wS, wQ, wTH, wTG, iH, iG, hsd, ⟨k1, k2⟩, hsi, L1, L2, hsl, pl,
    fH, fG⟩ := h
  refine ⟨iH, iG, fun H hH => ?_⟩
  have e5 : (stackArg s 5).toNat = H.len := hsd H hH
  rw [e5] at hrd dOsd dsds dRsd dKsd wSd
  refine ⟨⟨sp1, by omega, ?_, hwr, dOn, dOe, dOl, dOm, dOsd, dOs, dOa, dns, des, dls,
    dms, dsds, dsa, dRo, dRn, dRe, dRl, dRm, dRsd, dRs, dRa, dKo, dKn, dKe, dKl, dKm, dKsd, dKs, dKa, wO, wN, wE,
    wL, wM, wSd, wS, k1, k2, hsi, L1, L2,
    by unfold Spec.RsaPss.publicScratchWords Spec.Rsa.publicScratchWords Spec.Rsa.modulusWords at hsl; omega,
    dOtH, dOtG, dstH.symm, dstG.symm, dKtH, dKtG, wTH, wTG, fH, fG⟩,
    ?_, ?_, dOq.symm, dsq.symm, dKq.symm, wQ, pl, e5, hrd⟩
  · rw [hrd]
    apply Covers.of_sub
    intro r hr
    simp only [rdL, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · exact ⟨_, by rw [hrd]; simp, Region.contains_self _ _⟩
  · exact ⟨_, by rw [hrd]; simp, Region.contains_self _ _⟩

end VG.Proof.RsaOaep.X86_64.Pc
