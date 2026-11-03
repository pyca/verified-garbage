module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.PcCorrect
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified

/-!
# RSAES-OAEP encryption with a precomputed public key on x86-64: the contract

`contract` is the shared contract's precondition (with the tables `ts` of
MGF1's hash function), `postT`, and `encK`'s public data with `pre` and its
words and the table; it implies the shared contract (`implies`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

variable (H : Spec.Mgf1.Hash) (ts : List FnTable)

/-- The shared contract's precondition, `postT`, and `encK`'s public data
with `pre` and its words, the table's address, the tables' functions'
addresses, and which table it is. -/
def contract : Contract isa where
  pre := (encC H ts).pre
  post := postT H
  pub a s := (encK H H).pub a s ∧ stackArg a 7 = stackArg s 7 ∧ stackArg a 8 = stackArg s 8 ∧
    Spec.Rsa.wordsAt a.mem (stackArg a 7) (stackArg a 8).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 7) (stackArg s 8).toNat ∧ stackArg a 9 = stackArg s 9 ∧
    (∀ f ∈ tabFnsE ts, a.syms f = s.syms f) ∧
    ∀ T ∈ ts, (Abi.tableHeld 64 a.mem (stackArg a 9) (FnTable.words isa a T) ↔
      Abi.tableHeld 64 s.mem (stackArg s 9) (FnTable.words isa s T))

theorem implies (hsat : ∃ s, (encC H ts).pre s) : (contract H ts).Implies (encC H ts) where
  pre := fun _ h => h
  post := by sig_implies_post [Spec.RsaOaep.encryptTableContract, Spec.RsaOaep.encryptTableSig,
      Spec.RsaOaep.encryptPrecomputedSig, Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns,
      Abi.withTables, Sig.wordIndex, abi, argRegs, contract, postT, post, Consistent, encK, encStack, stackArgs_ten,
      List.append_eq, tabFnsE]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaOaep.encryptTableContract, Spec.RsaOaep.encryptTableSig,
      Spec.RsaOaep.encryptPrecomputedSig, Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns,
      Abi.withTables, Sig.wordIndex, abi, argRegs, contract, postT, post, Consistent, encK, encStack, stackArgs_ten,
      List.append_eq, tabFnsE] at h
    simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
      List.getD_cons_zero, Option.some.injEq] at h
    obtain ⟨hsp, hsy, htab, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
    obtain ⟨hb, hq⟩ := List.append_inj hl (by simp [Spec.Rsa.bytesAt, hcx, h9])
    have hq' := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hq
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, hcx]) hb
    refine ⟨⟨?_, by simp only [stackArgs_seven, a0, a1, a2, a3, a4, a5, a6], hn, he⟩, a7, a8, hq', a9, hsy,
      fun T hT => htab _ _ rfl rfl T hT⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := hsat

end VG.Proof.RsaOaep.X86_64.Pc
