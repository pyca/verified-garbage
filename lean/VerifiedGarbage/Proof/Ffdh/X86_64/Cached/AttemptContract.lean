module

public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Ffdh.CachedSat
import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.AttemptSat
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
meta import VerifiedGarbage.TCB.X86_64.Target

/-! # FFDH key generation from the context on x86-64: the attempt's internal contract -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached

open VG VG.X86_64 VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt wordsAt i2osp powMod)

/-- `(x, x_len, y, y_len, domain, domain_len, p_len, rand, rand_len,
scratch, scratch_len, ctx, ctx_len)`. -/
def cgPre (s : State) : Prop :=
  let xr : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  let yr : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  let dom : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let rnd : Region := ⟨stackArg s 1, (stackArg s 2).toNat⟩
  let scr : Region := ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  let ctx : Region := ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩
  let args : Region := ⟨stackArgAddr s 0, 56⟩
  (s.gpr .rsp).toNat + 64 ≤ 2 ^ 64 ∧ s.rd = [dom, rnd, ctx, args] ∧ s.wr = [xr, yr, scr] ∧
    xr.Disjoint yr ∧ xr.Disjoint dom ∧ xr.Disjoint rnd ∧ xr.Disjoint scr ∧ xr.Disjoint ctx ∧
    xr.Disjoint args ∧ yr.Disjoint dom ∧ yr.Disjoint rnd ∧ yr.Disjoint scr ∧ yr.Disjoint ctx ∧
    yr.Disjoint args ∧ dom.Disjoint scr ∧ rnd.Disjoint scr ∧ scr.Disjoint ctx ∧ scr.Disjoint args ∧
    (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64 ∧
    (stackArg s 3).toNat + (stackArg s 4).toNat * 8 ≤ 2 ^ 64 ∧
    (stackArg s 5).toNat + (stackArg s 6).toNat * 8 ≤ 2 ^ 64 ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint xr ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint yr ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint dom ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint rnd ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint scr ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ctx ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint args ∧
    pLenValid (stackArg s 0).toNat ∧ domainLenValid (stackArg s 0).toNat (s.gpr .r9).toNat ∧
    (s.gpr .rsi).toNat = (stackArg s 0).toNat ∧ (s.gpr .rcx).toNat = (stackArg s 0).toNat ∧
    (stackArg s 2).toNat = (stackArg s 0).toNat ∧ Spec.Rsa.scratchWords (stackArg s 0).toNat ≤ (stackArg s 4).toNat ∧
    domainValid (stackArg s 0).toNat (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) ∧
    generationContextAt s.mem (stackArg s 5) (stackArg s 6).toNat (stackArg s 0).toNat
      (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)

/-- The parameters and the scalar on entry. -/
abbrev cgDom (s : State) : List Byte := bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat
abbrev cgA (s : State) : Parameters := domainOf (stackArg s 0).toNat (cgDom s)
abbrev cgRand (s : State) : List Byte := bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat
abbrev cgS (s : State) : Nat := vettedScalarOfOctets (cgA s) (cgRand s)

def cgPost (s s' : State) : Prop :=
  ((s'.gpr .rax).setWidth 32).toNat = keyStatus (cgA s) (cgS s) ∧
    if keyStatus (cgA s) (cgS s) = 1 then
      bytesAt s'.mem (s.gpr .rdi) (stackArg s 0).toNat = i2osp (cgS s) (stackArg s 0).toNat ∧
        bytesAt s'.mem (s.gpr .rdx) (stackArg s 0).toNat =
          i2osp (powMod (cgA s).g (cgS s) (cgA s).p) (stackArg s 0).toNat
    else bytesAt s'.mem (s.gpr .rdi) (stackArg s 0).toNat = List.replicate (stackArg s 0).toNat 0 ∧
      bytesAt s'.mem (s.gpr .rdx) (stackArg s 0).toNat = List.replicate (stackArg s 0).toNat 0

/-- What timing may depend on, beyond the arguments. -/
def cgLeak (s : State) : List Nat := (cgDom s).map (·.toNat) ++ [keyStatus (cgA s) (cgS s)]

def cgPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rsp = s₂.gpr .rsp ∧ cgLeak s₁ = cgLeak s₂ ∧
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧
    stackArg s₁ 3 = stackArg s₂ 3 ∧ stackArg s₁ 4 = stackArg s₂ 4 ∧ stackArg s₁ 5 = stackArg s₂ 5 ∧
    stackArg s₁ 6 = stackArg s₂ 6

def cgContract : Contract isa where
  pre := cgPre
  post := cgPost
  pub := cgPub

theorem stackArgs_seven (s : State) : List.map (stackArg s) (List.range 7) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6] := rfl

theorem cg_pre0 {s : State} (h : (cachedGenerateKeyContract abi).pre s) : cgPre s := by
  sig_pre [cachedGenerateKeyContract, cachedGenerateKeySig, generateKeySig, abi, argRegs, stackArgs_seven,
    List.append_eq, pLenValid, domainLenValid] at h
  sig_pre [cachedGenerateKeyContract, cachedGenerateKeySig, generateKeySig, abi, argRegs, stackArgs_seven,
    List.append_eq, pLenValid, domainLenValid] at h
  sig_split h
  sig_reduce [cgPre, pLenValid, domainLenValid, generationContextAt]
  sig_and_intros
  sig_close
  all_goals first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›

theorem cg_post0 {s t : State} (h : cgPost s t) : (cachedGenerateKeyContract abi).post s t := by
  sig_post [cachedGenerateKeyContract, cachedGenerateKeySig, generateKeySig, abi, argRegs, stackArgs_seven,
    List.append_eq]
  sig_reduce [cgPost, cgDom, cgA, cgRand, cgS] at h
  exact h

theorem cg_pub0 {s₁ s₂ : State} (h : (cachedGenerateKeyContract abi).pub s₁ s₂) : cgPub s₁ s₂ := by
  sig_pub [cachedGenerateKeyContract, cachedGenerateKeySig, generateKeySig, abi, argRegs, stackArgs_seven,
    List.append_eq, pLenValid, domainLenValid] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  exact h

theorem cg_implies : cgContract.Implies (cachedGenerateKeyContract abi) where
  pre _ h := cg_pre0 h
  post _ _ _ h := cg_post0 h
  pub _ _ _ _ h := cg_pub0 h
  sat := attempt_sat

end VG.Proof.Ffdh.X86_64.Cached
