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

variable (ts : List FnTable)

/-- The shared contract's precondition, `postT`, and `encK`'s public data
with `pre` and its words, the tables' addresses, the tables' functions'
addresses, and which tables they are. -/
def contract : Contract isa where
  pre := (encC ts).pre
  post := postT
  pub a s := encPub a s ∧ stackArg a 8 = stackArg s 8 ∧ stackArg a 9 = stackArg s 9 ∧
    Spec.Rsa.wordsAt a.mem (stackArg a 8) (stackArg a 9).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 8) (stackArg s 9).toNat ∧ stackArg a 10 = stackArg s 10 ∧
    stackArg a 11 = stackArg s 11 ∧ (∀ f ∈ tabFnsE ts, a.syms f = s.syms f) ∧
    (∀ T ∈ ts, (Abi.tableHeld 64 a.mem (stackArg a 10) (FnTable.words isa a T) ↔
      Abi.tableHeld 64 s.mem (stackArg s 10) (FnTable.words isa s T))) ∧
    ∀ T ∈ ts, (Abi.tableHeld 64 a.mem (stackArg a 11) (FnTable.words isa a T) ↔
      Abi.tableHeld 64 s.mem (stackArg s 11) (FnTable.words isa s T))

theorem implies (hsat : ∃ s, (encC ts).pre s) : (contract ts).Implies (encC ts) where
  pre := fun _ h => h
  post := by sig_implies_post [Spec.RsaOaep.encryptTablesContract, Spec.RsaOaep.encryptTablesSig,
      Spec.RsaOaep.seedLenOk, Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns,
      Abi.withTables, Sig.wordIndex, abi, argRegs, contract, postT, post, Consistent, encK, encStack, stackArgs_twelve,
      List.append_eq, tabFnsE]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaOaep.encryptTablesContract, Spec.RsaOaep.encryptTablesSig,
      Spec.RsaOaep.seedLenOk, Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns,
      Abi.withTables, Sig.wordIndex, abi, argRegs, contract, postT, post, Consistent, encK, encStack, stackArgs_twelve,
      List.append_eq, tabFnsE] at h
    simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
      List.getD_cons_zero, Option.some.injEq] at h
    obtain ⟨hsp, hsy, htab, htab', hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
      a11⟩ := h
    obtain ⟨hb, hq⟩ := List.append_inj hl (by simp [Spec.Rsa.bytesAt, hcx, h9])
    have hq' := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hq
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, hcx]) hb
    refine ⟨⟨?_, by simp only [stackArgs_eight, a0, a1, a2, a3, a4, a5, a6, a7], hn, he⟩, a8, a9, hq', a10, a11.1,
      fun f hf => hsy f (List.mem_append_left _ hf), fun T hT => htab _ _ rfl rfl T hT,
      fun T hT => htab' _ _ rfl rfl T hT⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := hsat

end VG.Proof.RsaOaep.X86_64.Pc
