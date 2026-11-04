module

import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
public import VerifiedGarbage.Spec.RsaPss.Contract
public import VerifiedGarbage.Spec.RsaPss.Table
public import VerifiedGarbage.Proof.RsaPss.X86_64.ChkCtx
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCtx
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hash
public import VerifiedGarbage.Proof.Framework.Contract
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual

/-!
# RSASSA-PSS verification on x86-64: the contract on the registers

`verifyK tsH tsG` states `Spec.RsaPss.verifyPrecomputedTableContract` with
the tables `tsH` of `MdHash` and `tsG` of `Hash` (`Abi.withTables`, with the
stack the frame and the calls use, `verifyStack`) on the registers and the
stack (`verify_implies`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- The stack below the stack pointer: the frame, the return address of its
calls, and the stack of `checkEncoding`, the one that uses the most. -/
def verifyStack : Nat := 392 + 8 + chkStack

theorem stackArgs_ten (s : State) :
    List.map (stackArg s) (List.range 10) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9] := rfl

variable (tsH tsG : List FnTable)

/-- `verify(n = rdi, n_len = rsi, e = rdx, e_len = rcx, digest = r8,
digest_len = r9, sig = [rsp + 8], sig_len, salt_len, any_salt_len, scratch,
scratch_len, pre, pre_len, hash, mgf1 = [rsp + 80])`, `hash` one of the
tables `tsH` and `mgf1` one of `tsG`. -/
def verifyK : Contract isa where
  pre s :=
    let n : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let e : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let dg : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let sg : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let scr : Region := ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
    let pre : Region := ⟨stackArg s 6, (stackArg s 7).toNat * 8⟩
    let tH : Region := ⟨stackArg s 8, 88⟩
    let tG : Region := ⟨stackArg s 9, 40⟩
    let args : Region := ⟨stackArgAddr s 0, 80⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 verifyStack, verifyStack⟩
    verifyStack ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 88 ≤ 2 ^ 64 ∧
      (∃ T ∈ tsH, Abi.tableHeld 64 s.mem (stackArg s 8) (FnTable.words isa s T)) ∧
      (∃ T ∈ tsG, Abi.tableHeld 64 s.mem (stackArg s 9) (FnTable.words isa s T)) ∧
      (tabFns tsH ++ tabFns tsG).Pairwise (fun f g => f ≠ g → s.syms f ≠ s.syms g) ∧
      s.rd = [n, e, dg, sg, pre, tH, tG, args] ∧ s.wr = [scr] ∧
      n.Disjoint scr ∧ e.Disjoint scr ∧ dg.Disjoint scr ∧ sg.Disjoint scr ∧ scr.Disjoint pre ∧
      scr.Disjoint tH ∧ scr.Disjoint tG ∧ scr.Disjoint args ∧
      ret.Disjoint n ∧ ret.Disjoint e ∧ ret.Disjoint dg ∧ ret.Disjoint sg ∧ ret.Disjoint scr ∧ ret.Disjoint pre ∧
      ret.Disjoint tH ∧ ret.Disjoint tG ∧ ret.Disjoint args ∧
      stk.Disjoint n ∧ stk.Disjoint e ∧ stk.Disjoint dg ∧ stk.Disjoint sg ∧ stk.Disjoint scr ∧ stk.Disjoint pre ∧
      stk.Disjoint tH ∧ stk.Disjoint tG ∧ stk.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
      (stackArg s 4).toNat + (stackArg s 5).toNat * 8 ≤ 2 ^ 64 ∧
      (stackArg s 6).toNat + (stackArg s 7).toNat * 8 ≤ 2 ^ 64 ∧ (stackArg s 8).toNat + 88 ≤ 2 ^ 64 ∧
      (stackArg s 9).toNat + 40 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .rsi).toNat ∧ 1 ≤ (s.gpr .rcx).toNat ∧ (s.gpr .rcx).toNat ≤ (s.gpr .rsi).toNat ∧
      (stackArg s 1).toNat = (s.gpr .rsi).toNat ∧
      Spec.RsaPss.publicScratchWords (s.gpr .rsi).toNat ≤ (stackArg s 5).toNat ∧
      (stackArg s 7).toNat = Spec.Rsa.precomputedWords (s.gpr .rsi).toNat ∧
      Spec.RsaPss.digestLenOk 64 s.mem (stackArg s 8) (s.gpr .r9)
  post s s' := ∀ H G, Spec.MdHashTable.hashAt 64 s.mem (stackArg s 8) = some H →
    Spec.HashTable.hashAt 64 s.mem (stackArg s 9) = some G →
    Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) =
      some (Spec.Rsa.wordsAt s.mem (stackArg s 6) (stackArg s 7).toNat) →
    (s'.gpr .rax).setWidth 32 = if Spec.RsaPss.verify H G (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .r8) H.len)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rsi).toNat)
        (Spec.RsaPss.expectedSaltLen (stackArg s 2) ((stackArg s 3).setWidth 32)) then 1 else 0
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧
      (stackArg s₁ 3).setWidth 32 = (stackArg s₂ 3).setWidth 32 ∧ stackArg s₁ 4 = stackArg s₂ 4 ∧
      stackArg s₁ 5 = stackArg s₂ 5 ∧ stackArg s₁ 6 = stackArg s₂ 6 ∧ stackArg s₁ 7 = stackArg s₂ 7 ∧
      stackArg s₁ 8 = stackArg s₂ 8 ∧ stackArg s₁ 9 = stackArg s₂ 9 ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdi) (s₁.gpr .rsi).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdi) (s₂.gpr .rsi).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdx) (s₂.gpr .rcx).toNat ∧
      Spec.Rsa.wordsAt s₁.mem (stackArg s₁ 6) (stackArg s₁ 7).toNat =
        Spec.Rsa.wordsAt s₂.mem (stackArg s₂ 6) (stackArg s₂ 7).toNat ∧
      (∀ f ∈ tabFns tsH ++ tabFns tsG, s₁.syms f = s₂.syms f) ∧
      (∀ T ∈ tsH, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 8) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 8) (FnTable.words isa s₂ T))) ∧
      ∀ T ∈ tsG, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 9) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 9) (FnTable.words isa s₂ T))

/-- The contract, with the tables `tsH` and `tsG`. -/
abbrev verifyC : Contract isa :=
  Spec.RsaPss.verifyPrecomputedTableContract
    (abi.withTables Spec.RsaPss.verifyPrecomputedTableSig [("hash", tsH), ("mgf1", tsG)]) verifyStack

theorem verify_implies (hsat : ∃ s, (verifyC tsH tsG).pre s) : (verifyK tsH tsG).Implies (verifyC tsH tsG) where
  pre := by
    intro s h
    sig_pre [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig, Spec.MdHashTable.param,
      Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.HashTable.param,
      Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argRegs, verifyK, verifyStack,
      chkStack, stackArgs_ten, List.append_eq, tabFns] at h
    sig_pre [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig, Spec.MdHashTable.param,
      Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.HashTable.param,
      Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argRegs, verifyK, verifyStack,
      chkStack, stackArgs_ten, List.append_eq, tabFns, Sig.tableRegion] at h
    simp only [Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
      List.getD_cons_zero, Option.some.injEq, exists_eq_left'] at h
    sig_split h
    sig_reduce [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig, Spec.MdHashTable.param,
      Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.HashTable.param,
      Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argRegs, verifyK, verifyStack,
      chkStack, stackArgs_ten, List.append_eq, tabFns, Sig.tableRegion]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig, Spec.MdHashTable.param,
      Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.HashTable.param,
      Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argRegs, verifyK, verifyStack,
      chkStack, stackArgs_ten, List.append_eq, tabFns]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig, Spec.MdHashTable.param,
      Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.HashTable.param,
      Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argRegs, verifyK, verifyStack,
      chkStack, stackArgs_ten, List.append_eq, tabFns] at h
    simp only [String.reduceEq, ↓reduceIte, Option.map_some, ↓reduceIte, Nat.reduceAdd, List.getD_cons_succ,
      List.getD_cons_zero, Option.some.injEq] at h
    obtain ⟨hsp, hsy, htab, htab', hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, -⟩ := h
    obtain ⟨hb, hp⟩ := List.append_inj hl (by simp [Spec.Rsa.bytesAt, hsi, hcx])
    have hp' := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hp
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, hsi]) hb
    refine ⟨?_, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, hn, he, hp', hsy, fun T hT => htab _ _ rfl rfl T hT,
      fun T hT => htab' _ _ rfl rfl T hT⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := hsat

end VG.Proof.RsaPss.X86_64
