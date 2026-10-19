module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.PcCorrect
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.PcCtx
import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified

/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on x86-64: the contract

`contract` is the shared contract's precondition, `post`, and `encK`'s public
data with `pre` and its words; it implies the shared contract (`implies`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

def contract : Contract isa where
  pre := (Spec.RsaPkcs1Enc.encryptPrecomputedContract abi encStack).pre
  post := post
  pub a s := encK.pub a s ∧ stackArg a 6 = stackArg s 6 ∧ stackArg a 7 = stackArg s 7 ∧
    Spec.Rsa.wordsAt a.mem (stackArg a 6) (stackArg a 7).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 6) (stackArg s 7).toNat

/-- `encSatState`, with 16 words of `pre` at `0x5000`. -/
def satState : State := { encSatState with
  mem := fun a => if a = 0x10039 then 0x50 else if a = 0x10040 then 16 else encSatState.mem a
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 0⟩, ⟨0x4100, 61⟩, ⟨0x5000, 128⟩, ⟨0x10008, 64⟩] }

theorem implies : contract.Implies (Spec.RsaPkcs1Enc.encryptPrecomputedContract abi encStack) where
  pre := fun _ h => h
  post := by sig_implies_post [Spec.RsaPkcs1Enc.encryptPrecomputedContract,
    Spec.RsaPkcs1Enc.encryptPrecomputedSig, abi, argRegs, contract, post, encK, encStack,
    Impl.RsaPkcs1Enc.X86_64.Encrypt.frameBytes, stackArgs_eight, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaPkcs1Enc.encryptPrecomputedContract, Spec.RsaPkcs1Enc.encryptPrecomputedSig,
      abi, argRegs, contract, encStack, Impl.RsaPkcs1Enc.X86_64.Encrypt.frameBytes, stackArgs_eight,
      List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7⟩ := h
    obtain ⟨hb, hq⟩ := List.append_inj hl (by simp [Spec.Rsa.bytesAt, hcx, h9])
    have hq' := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hq
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, hcx]) hb
    refine ⟨⟨?_, by simp only [stackArgs_six, a0, a1, a2, a3, a4, a5], hn, he⟩, a6, a7, hq'⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.RsaPkcs1Enc.encryptPrecomputedContract,
    Spec.RsaPkcs1Enc.encryptPrecomputedSig, abi, argRegs, contract, encStack,
    Impl.RsaPkcs1Enc.X86_64.Encrypt.frameBytes, stackArgs_eight, List.append_eq]
    [satState, encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState

end VG.Proof.RsaPkcs1Enc.X86_64.Pc
