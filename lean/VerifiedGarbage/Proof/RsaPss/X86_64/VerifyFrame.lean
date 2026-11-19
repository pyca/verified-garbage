module

public import VerifiedGarbage.Proof.RsaPss.X86_64.SignPro
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
public import VerifiedGarbage.Spec.RsaPss
public import VerifiedGarbage.Spec.RsaPss.Contract
public import VerifiedGarbage.Spec.RsaPss.MdTable
public import VerifiedGarbage.Proof.RsaPss.X86_64.ChkCtx
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hash
public import VerifiedGarbage.Proof.Framework.Contract
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual

/-! ### `RsaPss.X86_64.VerifyCtx`, which this module and modules that import it used -/

section

/-!
# RSASSA-PSS verification on x86-64: the contract on the registers

`verifyK tsH tsG` states `Spec.RsaPss.verifyPrecomputedMdTableContract` with
the tables `tsH` of `MdHash` and `tsG` of `MdHash` (`Abi.withTables`, with the
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
    let tG : Region := ⟨stackArg s 9, 88⟩
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
      (stackArg s 9).toNat + 88 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .rsi).toNat ∧ 1 ≤ (s.gpr .rcx).toNat ∧ (s.gpr .rcx).toNat ≤ (s.gpr .rsi).toNat ∧
      (stackArg s 1).toNat = (s.gpr .rsi).toNat ∧
      Spec.RsaPss.publicScratchWords (s.gpr .rsi).toNat ≤ (stackArg s 5).toNat ∧
      (stackArg s 7).toNat = Spec.Rsa.precomputedWords (s.gpr .rsi).toNat ∧
      Spec.RsaPss.digestLenOk 64 s.mem (stackArg s 8) (s.gpr .r9)
  post s s' := ∀ H G, Spec.MdHashTable.hashAt 64 s.mem (stackArg s 8) = some H →
    Spec.MdHashTable.hashAt 64 s.mem (stackArg s 9) = some G →
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
  Spec.RsaPss.verifyPrecomputedMdTableContract
    (abi.withTables Spec.RsaPss.verifyPrecomputedMdTableSig [("hash", tsH), ("mgf1", tsG)]) verifyStack

theorem verify_implies (hsat : ∃ s, (verifyC tsH tsG).pre s) : (verifyK tsH tsG).Implies (verifyC tsH tsG) where
  pre := by
    intro s h
    sig_pre [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
      Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
      Abi.withTables, Sig.wordIndex, abi, argRegs, verifyK, verifyStack, chkStack, List.append_eq,
      tabFns, List.range, List.range.loop] at h
    sig_pre [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
      Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
      Abi.withTables, Sig.wordIndex, abi, argRegs, verifyK, verifyStack, chkStack, List.append_eq,
      tabFns, Sig.tableRegion, List.range, List.range.loop] at h
    simp only [Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
      List.getD_cons_zero, Option.some.injEq, exists_eq_left'] at h
    sig_split h
    sig_reduce [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig,
      Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
      Abi.withTables, Sig.wordIndex, abi, argRegs, verifyK, verifyStack, chkStack, List.append_eq,
      tabFns, Sig.tableRegion, List.range, List.range.loop]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig, Spec.MdHashTable.param,
      Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.MdHashTable.param,
      Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs, verifyK, verifyStack,
      chkStack, stackArgs_ten, List.append_eq, tabFns]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaPss.verifyPrecomputedMdTableContract, Spec.RsaPss.verifyPrecomputedMdTableSig, Spec.MdHashTable.param,
      Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Spec.MdHashTable.param,
      Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi, argRegs, verifyK, verifyStack,
      chkStack, List.append_eq, tabFns, List.range, List.range.loop] at h
    simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ, List.getD_cons_zero,
      Option.some.injEq] at h
    obtain ⟨hsp, hsy, htab, htab', hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
    obtain ⟨hb, hp⟩ := List.append_inj hl (by simp [Spec.Rsa.bytesAt, hsi, hcx])
    have hp' := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hp
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, hsi]) hb
    refine ⟨?_, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, hn, he, hp', hsy, fun T hT => htab _ _ rfl rfl T hT,
      fun T hT => htab' _ _ rfl rfl T hT⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := hsat

end VG.Proof.RsaPss.X86_64

end

end

/-!
# RSASSA-PSS verification on x86-64: the precondition by name, the frame
and the prologue

`VPre` names the facts of `verifyK.pre`; the frame is the `frameBytes` bytes
below `rsp` (`fb`), within the stack the function uses (`vstkR`). From the
entry state, after the frame's push, `verifyPrologue` saves `rbx`, `rbp` and
`r12` and the arguments to their slots (`verifyPro_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)

variable (tsH tsG : List FnTable)

/-- `verifyK.pre`, by name. -/
structure VPre (s : State) : Prop where
  sp1 : verifyStack ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 88 ≤ 2 ^ 64
  tabH : ∃ T ∈ tsH, Abi.tableHeld 64 s.mem (stackArg s 8) (FnTable.words isa s T)
  tabG : ∃ T ∈ tsG, Abi.tableHeld 64 s.mem (stackArg s 9) (FnTable.words isa s T)
  hsy : (tabFns tsH ++ tabFns tsG).Pairwise (fun f g => f ≠ g → s.syms f ≠ s.syms g)
  hrdE : s.rd = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 0, (stackArg s 1).toNat⟩, ⟨stackArg s 6, (stackArg s 7).toNat * 8⟩, ⟨stackArg s 8, 88⟩, ⟨stackArg s 9, 88⟩, ⟨stackArgAddr s 0, 80⟩]
  hwr : s.wr = [⟨stackArg s 4, (stackArg s 5).toNat * 8⟩]
  dns : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
  des : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
  ddgs : (⟨s.gpr .r8, (s.gpr .r9).toNat⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
  dsgs : (⟨stackArg s 0, (stackArg s 1).toNat⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
  dsp : (⟨stackArg s 4, (stackArg s 5).toNat * 8⟩ : Region).Disjoint ⟨stackArg s 6, (stackArg s 7).toNat * 8⟩
  dstH : (⟨stackArg s 4, (stackArg s 5).toNat * 8⟩ : Region).Disjoint ⟨stackArg s 8, 88⟩
  dstG : (⟨stackArg s 4, (stackArg s 5).toNat * 8⟩ : Region).Disjoint ⟨stackArg s 9, 88⟩
  dsa : (⟨stackArg s 4, (stackArg s 5).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 80⟩
  dRn : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dRe : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dRdg : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  dRsg : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩
  dRs : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
  dRp : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 6, (stackArg s 7).toNat * 8⟩
  dRtH : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 8, 88⟩
  dRtG : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 9, 88⟩
  dRa : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 80⟩
  dKn : (⟨s.gpr .rsp - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dKe : (⟨s.gpr .rsp - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dKdg : (⟨s.gpr .rsp - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  dKsg : (⟨s.gpr .rsp - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩
  dKs : (⟨s.gpr .rsp - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
  dKp : (⟨s.gpr .rsp - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨stackArg s 6, (stackArg s 7).toNat * 8⟩
  dKtH : (⟨s.gpr .rsp - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨stackArg s 8, 88⟩
  dKtG : (⟨s.gpr .rsp - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨stackArg s 9, 88⟩
  dKa : (⟨s.gpr .rsp - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨stackArgAddr s 0, 80⟩
  wN : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  wE : (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64
  wDg : (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64
  wSg : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  wS : (stackArg s 4).toNat + (stackArg s 5).toNat * 8 ≤ 2 ^ 64
  preWrap : (stackArg s 6).toNat + (stackArg s 7).toNat * 8 ≤ 2 ^ 64
  wTH : (stackArg s 8).toNat + 88 ≤ 2 ^ 64
  wTG : (stackArg s 9).toNat + 88 ≤ 2 ^ 64
  lv : Spec.Rsa.lenValid (s.gpr .rsi).toNat
  L1 : 1 ≤ (s.gpr .rcx).toNat
  L2 : (s.gpr .rcx).toNat ≤ (s.gpr .rsi).toNat
  hsg : (stackArg s 1).toNat = (s.gpr .rsi).toNat
  hsw : Spec.RsaPss.publicScratchWords (s.gpr .rsi).toNat ≤ (stackArg s 5).toNat
  preLen : (stackArg s 7).toNat = Spec.Rsa.precomputedWords (s.gpr .rsi).toNat
  hdl : Spec.RsaPss.digestLenOk 64 s.mem (stackArg s 8) (s.gpr .r9)

theorem VPre.of {s : State} (h : (verifyK tsH tsG).pre s) : VPre tsH tsG s := by
  simp only [verifyK] at h
  obtain ⟨sp1, sp2, tabH, tabG, hsy, hrdE, hwr, dns, des, ddgs, dsgs, dsp, dstH, dstG, dsa, dRn, dRe, dRdg, dRsg, dRs, dRp, dRtH, dRtG, dRa, dKn, dKe, dKdg, dKsg, dKs, dKp, dKtH, dKtG, dKa, wN, wE, wDg, wSg, wS, preWrap, wTH, wTG, lv, L1, L2, hsg, hsw, preLen, hdl⟩ := h
  exact ⟨sp1, sp2, tabH, tabG, hsy, hrdE, hwr, dns, des, ddgs, dsgs, dsp, dstH, dstG, dsa, dRn, dRe, dRdg, dRsg, dRs, dRp, dRtH, dRtG, dRa, dKn, dKe, dKdg, dKsg, dKs, dKp, dKtH, dKtG, dKa, wN, wE, wDg, wSg, wS, preWrap, wTH, wTG, lv, L1, L2, hsg, hsw, preLen, hdl⟩

variable {tsH tsG}

theorem VPre.k1 {s : State} (hp : VPre tsH tsG s) : 64 ≤ (s.gpr .rsi).toNat := hp.lv.1
theorem VPre.k2 {s : State} (hp : VPre tsH tsG s) : (s.gpr .rsi).toNat ≤ 1024 := hp.lv.2
theorem VPre.hsl {s : State} (hp : VPre tsH tsG s) :
    8 * (((s.gpr .rsi).toNat + 7) / 8) + 48 + 1024 ≤ (stackArg s 5).toNat := by
  have := hp.hsw
  unfold Spec.RsaPss.publicScratchWords Spec.Rsa.publicScratchWords Spec.Rsa.modulusWords at this; omega_using [this]

/-- The regions read: those of the inputs, and of the arguments. -/
theorem VPre.hrd {s : State} (hp : VPre tsH tsG s) :
    Covers [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 0, (stackArg s 1).toNat⟩, ⟨stackArgAddr s 0, 80⟩] s.rd := by
  rw [hp.hrdE]
  apply Covers.of_sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩

theorem VPre.pre {s : State} (hp : VPre tsH tsG s) : InRegions s.rd (stackArg s 6) ((stackArg s 7).toNat * 8) := by
  rw [hp.hrdE]; exact ⟨_, by simp, Region.contains_self _ _⟩

theorem VPre.args {s : State} (hp : VPre tsH tsG s) : InRegions s.rd (stackArgAddr s 0) 80 := by
  rw [hp.hrdE]; exact ⟨_, by simp, Region.contains_self _ _⟩

/-! ## The frame -/

/-- The stack the function uses, below `rsp`. -/
def vstkR (s : State) : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 verifyStack, verifyStack⟩

theorem vframe_sub (s : State) : Region.Sub ⟨fb s, frameBytes⟩ (vstkR s) :=
  Offset.sub_below _ (by decide) (by decide)

theorem vret_sub (s : State) : Region.Sub (below (fb s) 16) (vstkR s) := by
  simp only [below, fb, sub_sub']
  exact Offset.sub_below _ (by decide) (by decide)

theorem vret8_sub (s : State) : Region.Sub (below (fb s) 8) (vstkR s) := by
  simp only [below, fb, sub_sub']
  exact Offset.sub_below _ (by decide) (by decide)

/-- The region the function writes: its stack and `scratch`. -/
def vscrR (s : State) : Region := ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩

abbrev vwrR (s : State) : List Region := [vstkR s, vscrR s]

/-- An input, apart from them. -/
theorem vin_apart {s : State} {R : Region} (hK : (vstkR s).Disjoint R) (hS : R.Disjoint (vscrR s)) :
    ∀ r ∈ vwrR s, R.Disjoint r := by
  intro r hr
  simp only [vwrR, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hK.symm
  · exact hS


theorem vfb_toNat {s : State} (hp : VPre tsH tsG s) : (fb s).toNat + frameBytes = (s.gpr .rsp).toNat := by
  have := hp.sp1; unfold verifyStack at this
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold frameBytes at *; omega_using [this]

theorem VPre.geo {s : State} (hp : VPre tsH tsG s) : Geo (fb s) (stackArg s 4) := by
  have hF := vfb_toNat hp
  have := hp.sp2
  have hsl := hp.hsl
  have hk := hp.k1
  have wS := hp.wS
  have sS : Region.Sub ⟨stackArg s 4, oRsa⟩ ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩ :=
    Region.sub_prefix (by unfold oRsa; omega_using [hsl])
  refine ⟨by omega_using [hF, this], by unfold oRsa; omega_using [hsl, wS], ((hp.dKs.sub_left (vframe_sub s)).sub_right sS),
    ((hp.dKs.sub_left (vret_sub s)).sub_right sS)⟩

/-- Stack argument `j`, read from memory changed only in the frame. -/
theorem varg_read {s : State} (hp : VPre tsH tsG s) {m : Mem} (hf : Frame [frR s] s.mem m) {j : Nat} (hj : j < 10) :
    m.readW (off (fb s) (frameBytes + 8 + 8 * j)) 64 = stackArg s j := by
  rw [argAddr]
  refine hf.readW (r := ⟨stackArgAddr s 0, 80⟩) ?_ (fun r' hr' => ?_) (by decide)
  · rw [show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
      simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega_using []]
    have := hp.sp2
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])
  · simp only [List.mem_singleton] at hr'; subst hr'
    exact (hp.dKa.sub_left (vframe_sub s)).symm

/-- The address of stack argument `j` is readable. -/
theorem varg_in {s : State} (hp : VPre tsH tsG s) {u : State} (hrd : u.rd = s.rd) {j : Nat} (hj : j < 10)
    (n : Nat := 8) (hn : n ≤ 8 := by decide) :
    InRegions (u.rd ++ u.wr) (off (fb s) (frameBytes + 8 + 8 * j)) n := by
  have := hp.sp2
  rw [hrd]
  apply hp.hrd.left
  refine ⟨⟨stackArgAddr s 0, 80⟩, by simp, ?_⟩
  rw [argAddr, show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
    simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega_using []]
  exact Offset.contains_base _ (by omega) (by omega_using [hj])

theorem vframe_w {s : State} (hp : VPre tsH tsG s) {m m' : Mem} (hf : Frame [frR s] m m') {d : Nat}
    (hd : d + 8 ≤ frameBytes) (v : BitVec 64) : Frame [frR s] m (m'.writeW (off (fb s) d) v) := by
  have hF := vfb_toNat hp
  have := hp.sp2
  exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using [hd]) (by omega_using [hd, hF]))

/-- One stack argument copied to a slot. -/
theorem vcopy1_ok {s : State} (hp : VPre tsH tsG s) {u : State} (hsp : u.gpr .rsp = fb s) (hfr : frR s ∈ u.wr)
    (hrd : u.rd = s.rd) (hf : Frame [frR s] s.mem u.mem) {j d : Nat} (hj : j < 10) (hd : d + 8 ≤ frameBytes) :
    WP isa (.block [.mov .rax (.mem (arg j)), .store (sp d) .rax]) u fun u' => Keep [.rax] u u' ∧
      u'.mem = u.mem.writeW (off (fb s) d) (stackArg s j) ∧ Frame [frR s] s.mem u'.mem := by
  have hF := vfb_toNat hp
  have := hp.sp2
  have hsc : Scr u (fb s) frameBytes := Scr.of_mem hfr (by omega_using [hF])
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = u.mem.writeW (off (fb s) d) (stackArg s j)) ?_ rfl)
    fun u' ⟨hm, k⟩ => ⟨k, hm, hm ▸ vframe_w hp hf hd _⟩
  xrun [arg, ea_sp, hsp, varg_in hp hrd hj, varg_read hp hf hj, hsc.st (d := d) hd]

/-- The slots `verifyPrologue` stores to, and what. -/
def vproW (s : State) : Nat → BitVec 64 :=
  upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (fun k => word s.mem (fb s) (8 * k))
    41 (s.gpr .rbx)) 42 (s.gpr .rbp)) 43 (s.gpr .r12)) 18 (s.gpr .rdi)) 17 (s.gpr .rsi)) 19 (s.gpr .rdx))
    20 (s.gpr .rcx)) 37 (s.gpr .r8)) 38 (stackArg s 0)) 21 (stackArg s 4)) 22 (stackArg s 5)

theorem verifyPrologue_eq : verifyPrologue =
    ([.store (sp sRbx) .rbx, .store (sp sRbp) .rbp, .store (sp sR12) .r12, .store (sp sN) .rdi,
      .store (sp sK) .rsi, .store (sp sE) .rdx, .store (sp sEl) .rcx, .store (sp sDig) .r8] : List Instr) ++
    ([.mov .rax (.mem (arg 0)), .store (sp sSig) .rax] : List Instr) ++
    ([.mov .rax (.mem (arg 4)), .store (sp sScr) .rax] : List Instr) ++
    ([.mov .rax (.mem (arg 5)), .store (sp sScrLen) .rax] : List Instr) := rfl

/-- The prologue: the slots as `vproW` says, the working space untouched. -/
theorem verifyPro_ok {s : State} (hp : VPre tsH tsG s) :
    WP isa (.block verifyPrologue) (allocState frameBytes s) fun t => Keep [.rax] (allocState frameBytes s) t ∧
      Lay t (fb s) (stackArg s 4) ∧ Rep t.mem (fb s) (stackArg s 4) (fun o => s.mem (off (stackArg s 4) o)) (vproW s) ∧
      Frame [frR s] s.mem t.mem := by
  have hF := vfb_toNat hp
  have := hp.sp2
  have G' := hp.geo
  set A := allocState frameBytes s with hA
  have hsp : A.gpr .rsp = fb s := rfl
  have hfr : frR s ∈ A.wr := List.mem_cons_self ..
  have hsc : Scr A (fb s) frameBytes := Scr.of_mem hfr (by omega_using [hF])
  have R0 : Rep s.mem (fb s) (stackArg s 4) (fun o => s.mem (off (stackArg s 4) o))
      (fun k => word s.mem (fb s) (8 * k)) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  rw [verifyPrologue_eq, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  have R1 := ((((((((R0.wf G' (k := 41) (by decide) (s.gpr .rbx)).wf G' (k := 42) (by decide) (s.gpr .rbp)).wf G'
    (k := 43) (by decide) (s.gpr .r12)).wf G' (k := 18) (by decide) (s.gpr .rdi)).wf G' (k := 17) (by decide)
    (s.gpr .rsi)).wf G' (k := 19) (by decide) (s.gpr .rdx)).wf G' (k := 20) (by decide) (s.gpr .rcx)).wf G'
    (k := 37) (by decide) (s.gpr .r8))
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = (((((((s.mem.writeW (off (fb s) (8 * 41)) (s.gpr .rbx)).writeW
      (off (fb s) (8 * 42)) (s.gpr .rbp)).writeW (off (fb s) (8 * 43)) (s.gpr .r12)).writeW (off (fb s) (8 * 18))
      (s.gpr .rdi)).writeW (off (fb s) (8 * 17)) (s.gpr .rsi)).writeW (off (fb s) (8 * 19)) (s.gpr .rdx)).writeW
      (off (fb s) (8 * 20)) (s.gpr .rcx)).writeW (off (fb s) (8 * 37)) (s.gpr .r8)) ?_ rfl) fun t1 ⟨hm1, k1⟩ => ?_
  · xrun [ea_sp, hsp, hsc.st (d := sRbx) (by decide), hsc.st (d := sRbp) (by decide), hsc.st (d := sR12) (by decide),
      hsc.st (d := sN) (by decide), hsc.st (d := sK) (by decide), hsc.st (d := sE) (by decide),
      hsc.st (d := sEl) (by decide), hsc.st (d := sDig) (by decide), allocState_gpr']
    rfl
  have f1 : Frame [frR s] s.mem t1.mem := by
    rw [hm1]
    exact vframe_w hp (vframe_w hp (vframe_w hp (vframe_w hp (vframe_w hp (vframe_w hp (vframe_w hp (vframe_w hp
      (Frame.refl _ _) (by decide) _) (by decide) _) (by decide) _) (by decide) _) (by decide) _)
      (by decide) _) (by decide) _) (by decide) _
  have sp1 : t1.gpr .rsp = fb s := k1.gpr (by decide)
  refine WP.mono (vcopy1_ok hp sp1 (k1.2.2 ▸ hfr) k1.2.1 f1 (j := 0) (d := sSig) (by decide) (by decide))
    fun t2 ⟨k2, hm2, f2⟩ => ?_
  refine WP.mono (vcopy1_ok hp ((k2.gpr (by decide)).trans sp1) (k2.2.2 ▸ k1.2.2 ▸ hfr) (k2.2.1.trans k1.2.1) f2
    (j := 4) (d := sScr) (by decide) (by decide)) fun t3 ⟨k3, hm3, f3⟩ => ?_
  have k23 := k2.trans k3
  refine WP.mono (vcopy1_ok hp ((k23.gpr (by decide)).trans sp1) (k23.2.2 ▸ k1.2.2 ▸ hfr) (k23.2.1.trans k1.2.1) f3
    (j := 5) (d := sScrLen) (by decide) (by decide)) fun t4 ⟨k4, hm4, f4⟩ => ?_
  have k13 : Keep [.rax] A t4 := (k1.trans (k23.trans k4)).mono (by decide)
  have R3 : Rep t4.mem (fb s) (stackArg s 4) (fun o => s.mem (off (stackArg s 4) o)) (vproW s) := by
    rw [hm4, hm3, hm2, hm1]
    exact ((R1.wf G' (k := 38) (by decide) (stackArg s 0)).wf G' (k := 21) (by decide) (stackArg s 4)).wf G'
      (k := 22) (by decide) (stackArg s 5)
  have := hp.sp1
  have h392 : frameBytes = 392 := rfl
  have hvs : verifyStack = 808 := rfl
  refine ⟨k13, ⟨(k13.gpr (by decide)).trans hsp, k13.2.2 ▸ hfr, by omega_using [hF, this, h392, hvs], by omega_arith, ?_, ?_, G'.dFS, G'.dRS⟩, R3, f4⟩
  · have hsl := hp.hsl
    have hk := hp.k1
    refine ⟨⟨stackArg s 4, 0, (stackArg s 5).toNat * 8, by rw [k13.2.2, hA]; simp [allocState, hp.hwr],
      (BitVec.add_zero _).symm, by unfold oRsa; omega_using [hsl], Nat.le_trans (by omega_using []) hp.wS⟩, G'.Sw⟩
  · rw [show sScr = 8 * 21 from rfl]
    exact (R3.fr 21 (by decide)).trans (by simp [vproW, upd])

/-! ## The salt length's arguments -/

theorem zext32_beq_zero (x : BitVec 32) : (BitVec.setWidth 64 x == 0) = decide (x = 0) := by
  by_cases h : x = 0
  · subst h; rfl
  · have : BitVec.setWidth 64 x ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_setWidth] at this
      rw [Nat.mod_eq_of_lt (by omega_using [])] at this
      exact this))
    rw [beq_eq_false_iff_ne.mpr this, decide_eq_false h]

end VG.Proof.RsaPss.X86_64
