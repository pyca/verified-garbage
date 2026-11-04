module

public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Impl.Ffdh.X86_64.VettedValidation
import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.PrecomputeSat
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratchConsts
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified

/-! # FFDH's reusable key-generation context on x86-64: the internal contract -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached

open VG VG.X86_64 VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt wordsAt)
open VG.Impl.Ffdh.X86_64.VettedValidation

/-- `(ctx, ctx_len, domain, domain_len, p_len, scratch, scratch_len)`. -/
def pcPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8⟩
  let dom : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  let scr : Region := ⟨s.gpr .r9, (stackArg s 0).toNat * 8⟩
  let args : Region := ⟨stackArgAddr s 0, 8⟩
  (s.gpr .rsp).toNat + 16 ≤ 2 ^ 64 ∧ s.rd = [dom, args] ∧ s.wr = [ctx, scr] ∧
    ctx.Disjoint dom ∧ ctx.Disjoint scr ∧ ctx.Disjoint args ∧ dom.Disjoint scr ∧ scr.Disjoint args ∧
    (s.gpr .rdi).toNat + (s.gpr .rsi).toNat * 8 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r9).toNat + (stackArg s 0).toNat * 8 ≤ 2 ^ 64 ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ctx ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint dom ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint scr ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint args ∧
    pLenValid (s.gpr .r8).toNat ∧ domainLenValid (s.gpr .r8).toNat (s.gpr .rcx).toNat ∧
    (s.gpr .rsi).toNat = generationPrecomputedWords (s.gpr .r8).toNat ∧
    Spec.Rsa.scratchWords (s.gpr .r8).toNat ≤ (stackArg s 0).toNat ∧
    domainValid (s.gpr .r8).toNat (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)

/-- The domain on entry. -/
abbrev pcDom (s : State) : List Byte := bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat

def pcPost (s s' : State) : Prop :=
  (s'.gpr .rax).setWidth 32 = 1 ∧
    generationPrecompute (s.gpr .r8).toNat (pcDom s) = some (wordsAt s'.mem (s.gpr .rdi) (s.gpr .rsi).toNat)

def pcPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rsp = s₂.gpr .rsp ∧ (pcDom s₁).map (·.toNat) = (pcDom s₂).map (·.toNat) ∧
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    stackArg s₁ 0 = stackArg s₂ 0

/-- With the vetted groups' table: the precondition holds without its region. -/
def pcContract : Contract isa where
  pre s := pcPre (stripConsts tableConsts s) ∧ ConstsOk tableConsts 0 s
  post := pcPost
  pub s₁ s₂ := pcPub s₁ s₂ ∧ s₁.syms tableSym = s₂.syms tableSym

theorem stackArgs_one (s : State) : List.map (stackArg s) (List.range 1) = [stackArg s 0] := rfl

theorem pc_pre0 {s : State} (h : (generationPrecomputeContract abi).pre s) : pcPre s := by
  sig_pre [generationPrecomputeContract, generationPrecomputeSig, abi, argRegs, stackArgs_one,
    List.append_eq, pLenValid, domainLenValid] at h
  sig_pre [generationPrecomputeContract, generationPrecomputeSig, abi, argRegs, stackArgs_one,
    List.append_eq, pLenValid, domainLenValid] at h
  sig_split h
  sig_reduce [pcPre, pLenValid, domainLenValid]
  sig_and_intros
  sig_close
  all_goals first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›

theorem pc_post0 {s t : State} (h : pcPost s t) : (generationPrecomputeContract abi 8).post s t := by
  sig_post [generationPrecomputeContract, generationPrecomputeSig, abi, argRegs, stackArgs_one,
    List.append_eq]
  sig_reduce [pcPost, pcDom] at h
  exact h

theorem pc_pub0 {s₁ s₂ : State} (h : (generationPrecomputeContract abi 8).pub s₁ s₂) : pcPub s₁ s₂ := by
  sig_pub [generationPrecomputeContract, generationPrecomputeSig, abi, argRegs, stackArgs_one,
    List.append_eq, pLenValid, domainLenValid] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  exact h

theorem pc_implies : pcContract.Implies (generationPrecomputeContract (abi.withConsts tableConsts) 8) where
  pre s h := by
    obtain ⟨hp, hc⟩ := pre_consts.mp (Sig.pre_stack0 h)
    exact ⟨pc_pre0 hp, hc⟩
  post _ _ _ h := post_consts.mpr (pc_post0 h)
  pub _ _ _ _ h := ⟨pc_pub0 (pub_consts.mp h).1, (pub_consts.mp h).2 _ List.mem_cons_self⟩
  sat := precompute_sat

end VG.Proof.Ffdh.X86_64.Cached
