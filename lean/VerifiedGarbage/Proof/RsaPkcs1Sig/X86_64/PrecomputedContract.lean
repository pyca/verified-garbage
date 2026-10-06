import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.PrecomputedCorrect

namespace VG.Proof.RsaPkcs1Sig.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 Ver

def contract : Contract isa where
  pre := (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi verStack).pre
  post := post
  pub a s := verContract.pub a s ∧ stackArg a 5 = stackArg s 5 ∧ stackArg a 6 = stackArg s 6 ∧
    Spec.Rsa.wordsAt a.mem (stackArg a 5) (stackArg a 6).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 5) (stackArg s 6).toNat

def satState : State := { verSatState with
  mem := fun a => if a = 0x10031 then 0x50 else if a = 0x10038 then 16 else verSatState.mem a
  rd := [⟨0x1000, 64⟩, ⟨0x2000, 1⟩, ⟨0x3000, 1⟩, ⟨0x4000, 1⟩, ⟨0x5000, 128⟩, ⟨0x10008, 56⟩] }

theorem implies : contract.Implies (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi verStack) where
  pre := fun _ h => h
  post := by sig_implies_post [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig,
    abi, argRegs, contract, post, verContract, verStack, stackArgs_seven, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig,
      abi, argRegs, contract, verStack, stackArgs_seven, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6⟩ := h
    obtain ⟨hb, hp⟩ := List.append_inj hl (by simp [Spec.Rsa.bytesAt, hsi, hcx, a0, a2])
    have hp' := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hp
    obtain ⟨hn, he, hd, hs⟩ := leak_eq4 (by simp [Spec.Rsa.bytesAt, hsi]) (by simp [Spec.Rsa.bytesAt, hcx])
      (by simp [Spec.Rsa.bytesAt, a0]) hb
    refine ⟨⟨?_, h8, by simp only [stackArgs_five, a0, a1, a2, a3, a4], hn, he, hd, hs⟩, a5, a6, hp'⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h9, hsp⟩
  sat := by sig_implies_sat [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig,
    abi, argRegs, contract, verStack, stackArgs_seven, List.append_eq]
    [satState, verSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState

end VG.Proof.RsaPkcs1Sig.X86_64.Pc
