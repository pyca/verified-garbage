module

public import VerifiedGarbage.Proof.Rsa.X86_64.PrivCtx
import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
public import VerifiedGarbage.Spec.RsaPss.Contract
public import VerifiedGarbage.Spec.RsaPss.Table
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hash

/-!
# RSASSA-PSS signing on x86-64: the contract on the registers

`signK tsH tsG` states `Spec.RsaPss.signTableContract` with the tables
`tsH` of `MdHash` and `tsG` of `Hash` (`Abi.withTables`, with the stack the
frame and the calls use, `signStack`) on the registers and the stack
(`sign_implies`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- The stack below the stack pointer: the frame, the return address of
its calls, and what `vg_rsa_private_checked` uses below that. -/
def signStack : Nat := 392 + 8 + Proof.Rsa.X86_64.stackBytes

theorem stackArgs_eighteen (s : State) :
    List.map (stackArg s) (List.range 18) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16,
      stackArg s 17] := rfl

/-- The functions of the tables `ts`. -/
def tabFns (ts : List FnTable) : List String := (ts.map (·.fns)).flatten

variable (tsH tsG : List FnTable)

/-- `sign(out = rdi, out_len = rsi, n = rdx, n_len = rcx, e = r8, e_len = r9,
p = [rsp + 8], p_len, q, q_len, dp, dp_len, dq, dq_len, qinv, qinv_len,
digest = [rsp + 88], digest_len, salt, salt_len, scratch, scratch_len,
hash = [rsp + 136], mgf1 = [rsp + 144])`, `hash` one of the tables `tsH`
and `mgf1` one of `tsG`. -/
def signK : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let n : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let e : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let p : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let q : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
    let dp : Region := ⟨stackArg s 4, (stackArg s 5).toNat⟩
    let dq : Region := ⟨stackArg s 6, (stackArg s 7).toNat⟩
    let qi : Region := ⟨stackArg s 8, (stackArg s 9).toNat⟩
    let dg : Region := ⟨stackArg s 10, (stackArg s 11).toNat⟩
    let sa : Region := ⟨stackArg s 12, (stackArg s 13).toNat⟩
    let scr : Region := ⟨stackArg s 14, (stackArg s 15).toNat * 8⟩
    let tH : Region := ⟨stackArg s 16, 88⟩
    let tG : Region := ⟨stackArg s 17, 40⟩
    let args : Region := ⟨stackArgAddr s 0, 144⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 signStack, signStack⟩
    signStack ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 152 ≤ 2 ^ 64 ∧
      (∃ T ∈ tsH, Abi.tableHeld 64 s.mem (stackArg s 16) (FnTable.words isa s T)) ∧
      (∃ T ∈ tsG, Abi.tableHeld 64 s.mem (stackArg s 17) (FnTable.words isa s T)) ∧
      (tabFns tsH ++ tabFns tsG).Pairwise (fun f g => f ≠ g → s.syms f ≠ s.syms g) ∧
      s.rd = [n, e, p, q, dp, dq, qi, dg, sa, tH, tG, args] ∧ s.wr = [out, scr] ∧
      out.Disjoint n ∧ out.Disjoint e ∧ out.Disjoint p ∧ out.Disjoint q ∧ out.Disjoint dp ∧
      out.Disjoint dq ∧ out.Disjoint qi ∧ out.Disjoint dg ∧ out.Disjoint sa ∧ out.Disjoint scr ∧
      out.Disjoint tH ∧ out.Disjoint tG ∧ out.Disjoint args ∧
      n.Disjoint scr ∧ e.Disjoint scr ∧ p.Disjoint scr ∧ q.Disjoint scr ∧ dp.Disjoint scr ∧
      dq.Disjoint scr ∧ qi.Disjoint scr ∧ dg.Disjoint scr ∧ sa.Disjoint scr ∧ scr.Disjoint tH ∧
      scr.Disjoint tG ∧ scr.Disjoint args ∧
      ret.Disjoint out ∧ ret.Disjoint n ∧ ret.Disjoint e ∧ ret.Disjoint p ∧ ret.Disjoint q ∧
      ret.Disjoint dp ∧ ret.Disjoint dq ∧ ret.Disjoint qi ∧ ret.Disjoint dg ∧ ret.Disjoint sa ∧
      ret.Disjoint scr ∧ ret.Disjoint tH ∧ ret.Disjoint tG ∧ ret.Disjoint args ∧
      stk.Disjoint out ∧ stk.Disjoint n ∧ stk.Disjoint e ∧ stk.Disjoint p ∧ stk.Disjoint q ∧
      stk.Disjoint dp ∧ stk.Disjoint dq ∧ stk.Disjoint qi ∧ stk.Disjoint dg ∧ stk.Disjoint sa ∧
      stk.Disjoint scr ∧ stk.Disjoint tH ∧ stk.Disjoint tG ∧ stk.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
      (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64 ∧ (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64 ∧
      (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64 ∧ (stackArg s 8).toNat + (stackArg s 9).toNat ≤ 2 ^ 64 ∧
      (stackArg s 10).toNat + (stackArg s 11).toNat ≤ 2 ^ 64 ∧
      (stackArg s 12).toNat + (stackArg s 13).toNat ≤ 2 ^ 64 ∧
      (stackArg s 14).toNat + (stackArg s 15).toNat * 8 ≤ 2 ^ 64 ∧ (stackArg s 16).toNat + 88 ≤ 2 ^ 64 ∧
      (stackArg s 17).toNat + 40 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .rcx).toNat ∧ (s.gpr .rsi).toNat = (s.gpr .rcx).toNat ∧
      1 ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat ≤ (s.gpr .rcx).toNat ∧
      1 ≤ (stackArg s 1).toNat ∧ (stackArg s 1).toNat < (s.gpr .rcx).toNat ∧ 1 ≤ (stackArg s 3).toNat ∧
      (stackArg s 3).toNat < (s.gpr .rcx).toNat ∧ (stackArg s 5).toNat = (stackArg s 1).toNat ∧
      (stackArg s 9).toNat = (stackArg s 1).toNat ∧ (stackArg s 7).toNat = (stackArg s 3).toNat ∧
      Spec.RsaPss.scratchWords (s.gpr .rcx).toNat ≤ (stackArg s 15).toNat ∧
      Spec.RsaPss.digestLenOk 64 s.mem (stackArg s 16) (stackArg s 11)
  post s s' := ∀ H G, Spec.MdHashTable.hashAt 64 s.mem (stackArg s 16) = some H →
    Spec.HashTable.hashAt 64 s.mem (stackArg s 17) = some G →
    Spec.Rsa.writtenOutcome s'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((s'.gpr .rax).setWidth 32)
      (Spec.RsaPss.sign H G (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 10) H.len)
        (Spec.Rsa.bytesAt s.mem (stackArg s 12) (stackArg s 13).toNat))
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      (List.range 18).map (stackArg s₁) = (List.range 18).map (stackArg s₂) ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdx) (s₂.gpr .rcx).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r8) (s₁.gpr .r9).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r8) (s₂.gpr .r9).toNat ∧
      (∀ f ∈ tabFns tsH ++ tabFns tsG, s₁.syms f = s₂.syms f) ∧
      (∀ T ∈ tsH, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 16) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 16) (FnTable.words isa s₂ T))) ∧
      ∀ T ∈ tsG, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 17) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 17) (FnTable.words isa s₂ T))

/-- The contract, with the tables `tsH` and `tsG`. -/
abbrev signC : Contract isa :=
  Spec.RsaPss.signTableContract (abi.withTables Spec.RsaPss.signTableSig [("hash", tsH), ("mgf1", tsG)]) signStack

theorem sign_implies (hsat : ∃ s, (signC tsH tsG).pre s) : (signK tsH tsG).Implies (signC tsH tsG) where
  pre := by
    intro s h
    sig_pre [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount,
      Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.HashTable.param, Spec.HashTable.wordCount,
      Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argRegs, signK, signStack, stackArgs_eighteen,
      List.append_eq, tabFns] at h
    sig_pre [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount,
      Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.HashTable.param, Spec.HashTable.wordCount,
      Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argRegs, signK, signStack, stackArgs_eighteen,
      List.append_eq, tabFns, Sig.tableRegion] at h
    simp only [Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
      List.getD_cons_zero, Option.some.injEq, exists_eq_left'] at h
    sig_split h
    sig_reduce [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount,
      Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.HashTable.param, Spec.HashTable.wordCount,
      Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argRegs, signK, signStack, stackArgs_eighteen,
      List.append_eq, tabFns, Sig.tableRegion]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount,
      Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.HashTable.param, Spec.HashTable.wordCount,
      Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argRegs, signK, signStack, stackArgs_eighteen,
      List.append_eq, tabFns]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount,
      Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.HashTable.param, Spec.HashTable.wordCount,
      Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argRegs, signK, signStack, stackArgs_eighteen,
      List.append_eq, tabFns] at h
    simp only [String.reduceEq, ↓reduceIte, Option.map_some, ↓reduceIte, Nat.reduceAdd, List.getD_cons_succ,
      List.getD_cons_zero, Option.some.injEq] at h
    obtain ⟨hsp, hsy, htab, htab', hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12,
      a13, a14, a15, a16, a17⟩ := h
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, hcx]) hl
    refine ⟨?_, by simp only [stackArgs_eighteen, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14,
      a15, a16, a17], hn, he, hsy, fun T hT => htab _ _ rfl rfl T hT, fun T hT => htab' _ _ rfl rfl T hT⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := hsat

end VG.Proof.RsaPss.X86_64
