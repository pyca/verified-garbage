module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.PcCorrect
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCall
public import VerifiedGarbage.Proof.HashFns.X86_64.Witness

/-!
# RSAES-OAEP encryption with a precomputed public key on x86-64: the contract

`contract` is the shared contract's precondition, `post` (`encK`'s
postcondition for the hash functions the selectors name), and `encPub` with
`pre`'s words; it implies the shared contract (`implies`), which is
satisfiable (`sat`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

def contract : Contract isa where
  pre := (Spec.RsaOaep.encryptAnyContract abi encStack).pre
  post := post
  pub a s := encPub a s ∧
    Spec.Rsa.wordsAt a.mem (stackArg a 8) (stackArg a 9).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 8) (stackArg s 9).toNat

/-- An entry state: SHA-1 for both hash functions, with the table at
`0x6000` of the witnesses' streaming functions (`Witness.funs`), 16 words of
`pre` at `0x5000`, and the stack arguments at `0x10008`. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 64 | .r8 => 0x3000 | .r9 => 1
    | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x10009 then 0x41 else if a = 0x10019 then 0x42 else if a = 0x10029 then 0x46
    else if a = 0x10030 then 20 else if a = 0x1003A then 0x02 else if a = 0x10040 then 0x20
    else if a = 0x10041 then 0x08 else if a = 0x10049 then 0x50 else if a = 0x10050 then 16
    else if a = 0x10058 then 1 else if a = 0x10060 then 1 else if a = 0x10069 then 0x60
    else if a = 0x10071 then 0x60 else if a = 0x6001 then 0x70 else if a = 0x6009 then 0x71
    else if a = 0x6011 then 0x72 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4100, 0⟩, ⟨0x4200, 0⟩, ⟨0x4600, 20⟩, ⟨0x5000, 128⟩, ⟨0x6000, 24⟩,
    ⟨0x6000, 24⟩, ⟨0x10008, 112⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 2080 * 8⟩]
  funs := HashFns.X86_64.Witness.funs

theorem sat : ∃ s, (Spec.RsaOaep.encryptAnyContract abi encStack).pre s := by
  refine ⟨satState, ?_⟩
  sig_pre [Spec.RsaOaep.encryptAnyContract, Spec.RsaOaep.encryptAnySig, abi, argRegs,
    encStack, stackArgs_fourteen, List.append_eq]
  sig_and_intros
  all_goals first
    | ((first | rw [show (stackArg satState 10).toNat = 1 from by decide]
              | rw [show (stackArg satState 11).toNat = 1 from by decide])
       exact HashFns.X86_64.Witness.tableOf_one (s := satState) (a₀ := 0x7000) (a₁ := 0x7100) (a₂ := 0x7200)
         rfl rfl rfl (by decide) (by decide) (by decide))
    | (unfold Spec.Rsa.lenValid; decide)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro a h₁ h₂
       sig_simp_only [Region.Contains, satState, stackArg, stackArgAddr, Mem.readW, Mem.read] at h₁ h₂
       bv_omega)

theorem implies : contract.Implies (Spec.RsaOaep.encryptAnyContract abi encStack) where
  pre := fun _ h => h
  post := by
    intro s s' hpre h
    sig_post [Spec.RsaOaep.encryptAnyContract, Spec.RsaOaep.encryptAnySig, abi, argRegs, contract, post,
      Consistent, encK, encStack, stackArgs_fourteen, List.append_eq]
    sig_reduce [Spec.RsaOaep.encryptAnyContract, Spec.RsaOaep.encryptAnySig, abi, argRegs, contract, post,
      Consistent, encK, encStack, stackArgs_fourteen, List.append_eq] at h
    sig_simp [Spec.RsaOaep.encryptAnyContract, Spec.RsaOaep.encryptAnySig, abi, argRegs, contract, post,
      Consistent, encK, encStack, stackArgs_fourteen, List.append_eq] [] at h
    intro H G eH eG hc
    obtain ⟨-, -, hpp⟩ := pre_of hpre
    rw [(hpp H eH).seedLen]
    exact h hc H G eH eG
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaOaep.encryptAnyContract, Spec.RsaOaep.encryptAnySig, abi, argRegs, contract,
      encStack, stackArgs_fourteen, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hsw, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12,
      a13⟩ := h
    obtain ⟨h3, hG⟩ := List.append_inj hl (by simp [Spec.Rsa.bytesAt, Spec.Rsa.wordsAt, Spec.HashFns.tableWords,
      hcx, h9, a9])
    obtain ⟨h2, hT⟩ := List.append_inj h3 (by simp [Spec.Rsa.bytesAt, Spec.Rsa.wordsAt, hcx, h9, a9])
    obtain ⟨hb, hq⟩ := List.append_inj h2 (by simp [Spec.Rsa.bytesAt, hcx, h9])
    have hq' := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hq
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, hcx]) hb
    refine ⟨⟨?_, by simp only [stackArgs_fourteen, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13], hn, he,
      hT, hG, hsw⟩, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
    · exact hq'
  sat := sat

end VG.Proof.RsaOaep.X86_64.Pc
