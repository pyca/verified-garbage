import VerifiedGarbage.Proof.RsaPss.X86_64.PrecomputedCorrect

namespace VG.Proof.RsaPss.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

variable (G : Spec.Mgf1.Hash)

def contract : Contract isa where
  pre := (Spec.RsaPss.verifyPrecomputedContract G G abi verifyStack).pre
  post s t := validCache s → (verifyK G).post s t
  pub a s := (verifyK G).pub a s ∧ stackArg a 5 = stackArg s 5 ∧ stackArg a 6 = stackArg s 6 ∧
    Spec.Rsa.wordsAt a.mem (stackArg a 5) (stackArg a 6).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 5) (stackArg s 6).toNat

def satState : State := { verifySatState G with
  mem := fun a => if a = 0x10031 then 0x50 else if a = 0x10038 then 16 else (verifySatState G).mem a
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4600, G.len⟩, ⟨0x4000, 64⟩, ⟨0x5000, 128⟩, ⟨0x10008, 56⟩] }

theorem sat (hG : G ∈ Pbkdf2.Md.X86_64.mdHashes) :
    ∃ s, (contract G).pre s := by
  simp only [Pbkdf2.Md.X86_64.mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hG
  rcases hG with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · sig_implies_sat [Spec.Rsa.lenValid, Spec.Rsa.precomputedWords, Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi, argRegs, contract, verifyStack, stackArgs_seven, List.append_eq] [satState, verifySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState Spec.Mgf1.md5
  · sig_implies_sat [Spec.Rsa.lenValid, Spec.Rsa.precomputedWords, Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi, argRegs, contract, verifyStack, stackArgs_seven, List.append_eq] [satState, verifySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState Spec.Mgf1.sha1
  · sig_implies_sat [Spec.Rsa.lenValid, Spec.Rsa.precomputedWords, Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi, argRegs, contract, verifyStack, stackArgs_seven, List.append_eq] [satState, verifySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState Spec.Mgf1.sha224
  · sig_implies_sat [Spec.Rsa.lenValid, Spec.Rsa.precomputedWords, Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi, argRegs, contract, verifyStack, stackArgs_seven, List.append_eq] [satState, verifySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState Spec.Mgf1.sha256
  · sig_implies_sat [Spec.Rsa.lenValid, Spec.Rsa.precomputedWords, Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi, argRegs, contract, verifyStack, stackArgs_seven, List.append_eq] [satState, verifySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState Spec.Mgf1.sha384
  · sig_implies_sat [Spec.Rsa.lenValid, Spec.Rsa.precomputedWords, Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi, argRegs, contract, verifyStack, stackArgs_seven, List.append_eq] [satState, verifySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState Spec.Mgf1.sha512
  · sig_implies_sat [Spec.Rsa.lenValid, Spec.Rsa.precomputedWords, Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi, argRegs, contract, verifyStack, stackArgs_seven, List.append_eq] [satState, verifySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState Spec.Mgf1.sha512_224
  · sig_implies_sat [Spec.Rsa.lenValid, Spec.Rsa.precomputedWords, Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig, abi, argRegs, contract, verifyStack, stackArgs_seven, List.append_eq] [satState, verifySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState Spec.Mgf1.sha512_256

theorem implies (hG : G ∈ Pbkdf2.Md.X86_64.mdHashes) :
    (contract G).Implies (Spec.RsaPss.verifyPrecomputedContract G G abi verifyStack) where
  pre := fun _ h => h
  post := by sig_implies_post [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig,
    abi, argRegs, contract, validCache, verifyK, verifyStack, stackArgs_seven, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaPss.verifyPrecomputedContract, Spec.RsaPss.verifyPrecomputedSig,
      abi, argRegs, contract, verifyStack, stackArgs_seven, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6⟩ := h
    obtain ⟨hb, hp⟩ := List.append_inj hl (by simp [Spec.Rsa.bytesAt, hsi, hcx])
    have hp' := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hp
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, hsi]) hb
    refine ⟨⟨?_, a0, a1, a2, a3, a4, hn, he⟩, a5, a6, hp'⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := sat G hG

end VG.Proof.RsaPss.X86_64.Pc
