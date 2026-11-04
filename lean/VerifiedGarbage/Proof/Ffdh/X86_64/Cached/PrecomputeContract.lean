module

public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PowLit

/-! # FFDH's reusable key-generation context on x86-64: the internal contract -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached

open VG VG.X86_64 VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt wordsAt)

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

def pcContract : Contract isa where
  pre := pcPre
  post := pcPost
  pub := pcPub

theorem stackArgs_one (s : State) : List.map (stackArg s) (List.range 1) = [stackArg s 0] := rfl

theorem pc_implies : pcContract.Implies (generationPrecomputeContract abi) where
  pre := by
    intro s h
    sig_pre [generationPrecomputeContract, generationPrecomputeSig, abi, argRegs, stackArgs_one,
      List.append_eq, pLenValid, domainLenValid] at h
    sig_pre [generationPrecomputeContract, generationPrecomputeSig, abi, argRegs, stackArgs_one,
      List.append_eq, pLenValid, domainLenValid] at h
    sig_split h
    sig_reduce [pcContract, pcPre, pLenValid, domainLenValid]
    sig_and_intros
    sig_close
    all_goals first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›
  post := by
    intro s t _ h
    sig_post [generationPrecomputeContract, generationPrecomputeSig, abi, argRegs, stackArgs_one,
      List.append_eq]
    sig_reduce [pcContract, pcPost, pcDom] at h
    exact h
  pub := by
    intro s₁ s₂ _ _ h
    sig_pub [generationPrecomputeContract, generationPrecomputeSig, abi, argRegs, stackArgs_one,
      List.append_eq, pLenValid, domainLenValid] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    exact h
  sat := by
    sorry

end VG.Proof.Ffdh.X86_64.Cached
