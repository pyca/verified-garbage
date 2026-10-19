module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecPcCorrect
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified

/-!
# `vg_rsa_pkcs1_recover_precomputed` on x86-64: the contract

`contract` is the shared contract's precondition, `post`, and
`recContract`'s public data with `pre` and its words; it implies the shared
contract (`implies`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64.RecPc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64

def contract : Contract isa where
  pre := (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi verStack).pre
  post := post
  pub a s := recContract.pub a s ∧ stackArg a 5 = stackArg s 5 ∧ stackArg a 6 = stackArg s 6 ∧
    Spec.Rsa.wordsAt a.mem (stackArg a 5) (stackArg a 6).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 5) (stackArg s 6).toNat

/-- `recSatState`, with 16 words of `pre` at `0x6000`. -/
def satState : State := { recSatState with
  mem := fun a => if a = 0x10031 then 0x60 else if a = 0x10038 then 16 else recSatState.mem a
  rd := [⟨0x1000, 64⟩, ⟨0x2000, 1⟩, ⟨0x4000, 1⟩, ⟨0x6000, 128⟩, ⟨0x10008, 56⟩] }

theorem implies : contract.Implies (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi verStack) where
  pre := fun _ h => h
  post := by sig_implies_post [Spec.RsaPkcs1Sig.recoverPrecomputedContract,
    Spec.RsaPkcs1Sig.recoverPrecomputedSig, abi, argRegs, contract, post, Consistent, recContract, verStack,
    stackArgs_seven, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaPkcs1Sig.recoverPrecomputedContract, Spec.RsaPkcs1Sig.recoverPrecomputedSig,
      abi, argRegs, contract, verStack, stackArgs_seven, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6⟩ := h
    obtain ⟨hb, hq⟩ := List.append_inj hl (by simp [Spec.Rsa.bytesAt, hcx, h9, a2])
    have hq' := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hq
    obtain ⟨hn, he, hs⟩ := leak_eq3 (by simp [Spec.Rsa.bytesAt, hcx]) (by simp [Spec.Rsa.bytesAt, h9]) hb
    refine ⟨⟨?_, a0, by rw [a1, a2, a3, a4], hn, he, hs⟩, a5, a6, hq'⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.RsaPkcs1Sig.recoverPrecomputedContract,
    Spec.RsaPkcs1Sig.recoverPrecomputedSig, abi, argRegs, contract, verStack, stackArgs_seven, List.append_eq]
    [satState, recSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState

end VG.Proof.RsaPkcs1Sig.X86_64.RecPc
