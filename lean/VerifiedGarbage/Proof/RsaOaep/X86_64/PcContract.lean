module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.PcCorrect
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCall

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

/-- An entry state: SHA-1 for both hash functions, 16 words of `pre` at
`0x5000`, and the stack arguments at `0x10008`. -/
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
    else if a = 0x10058 then 1 else if a = 0x10060 then 1 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4100, 0⟩, ⟨0x4200, 0⟩, ⟨0x4600, 20⟩, ⟨0x5000, 128⟩, ⟨0x10008, 96⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 2080 * 8⟩]

theorem sat : ∃ s, (Spec.RsaOaep.encryptAnyContract abi encStack).pre s := by
  sig_implies_sat [Spec.RsaOaep.encryptAnyContract, Spec.RsaOaep.encryptAnySig, abi, argRegs,
    encStack, stackArgs_twelve, List.append_eq] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using satState

theorem implies : contract.Implies (Spec.RsaOaep.encryptAnyContract abi encStack) where
  pre := fun _ h => h
  post := by
    intro s s' hpre h
    sig_post [Spec.RsaOaep.encryptAnyContract, Spec.RsaOaep.encryptAnySig, abi, argRegs, contract, post,
      Consistent, encK, encStack, stackArgs_twelve, List.append_eq]
    sig_reduce [Spec.RsaOaep.encryptAnyContract, Spec.RsaOaep.encryptAnySig, abi, argRegs, contract, post,
      Consistent, encK, encStack, stackArgs_twelve, List.append_eq] at h
    sig_simp [Spec.RsaOaep.encryptAnyContract, Spec.RsaOaep.encryptAnySig, abi, argRegs, contract, post,
      Consistent, encK, encStack, stackArgs_twelve, List.append_eq] [] at h
    intro H G eH eG hc
    obtain ⟨-, -, hpp⟩ := pre_of hpre
    rw [(hpp H eH).seedLen]
    exact h hc H G eH eG
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaOaep.encryptAnyContract, Spec.RsaOaep.encryptAnySig, abi, argRegs, contract,
      encStack, stackArgs_twelve, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h
    obtain ⟨hb, hq⟩ := List.append_inj hl (by simp [Spec.Rsa.bytesAt, hcx, h9])
    have hq' := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hq
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, hcx]) hb
    refine ⟨⟨?_, by simp only [stackArgs_twelve, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11], hn, he⟩, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
    · exact hq'
  sat := sat

end VG.Proof.RsaOaep.X86_64.Pc
