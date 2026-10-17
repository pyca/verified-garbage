module

public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PowLit

/-! # FFDH domain validation on x86-64: internal contract -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Spec.Ffdh

def cdPre (s : State) : Prop :=
  let dom : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  let scr : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat * 8⟩
  s.rd = [dom] ∧ s.wr = [scr] ∧ dom.Disjoint scr ∧
    (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧
    (s.gpr .rcx).toNat + (s.gpr .r8).toNat * 8 ≤ 2 ^ 64 ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint dom ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint scr ∧
    pLenValid (s.gpr .rdx).toNat ∧ domainLenValid (s.gpr .rdx).toNat (s.gpr .rsi).toNat ∧
    Spec.Rsa.scratchWords (s.gpr .rdx).toNat ≤ (s.gpr .r8).toNat

abbrev cdDom (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat

def cdPost (s t : State) : Prop :=
  ((t.gpr .rax).setWidth 32).toNat = if domainValid (s.gpr .rdx).toNat (cdDom s) then 1 else 0

def cdPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rsp = s₂.gpr .rsp ∧ (cdDom s₁).map (·.toNat) = (cdDom s₂).map (·.toNat) ∧
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8

def cdContract : Contract isa where
  pre := cdPre
  post := cdPost
  pub := cdPub

def cdSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 128 | .rdx => 64 | .rcx => 0x4000 | .r8 => 1056
    | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x4000, 8448⟩]

theorem cd_implies : cdContract.Implies (checkDomainContract abi) where
  pre := by
    intro s h
    sig_pre [checkDomainContract, checkDomainSig, abi, argRegs, List.append_eq, pLenValid, domainLenValid] at h
    sig_pre [checkDomainContract, checkDomainSig, abi, argRegs, List.append_eq, pLenValid, domainLenValid] at h
    sig_split h
    sig_reduce [cdContract, cdPre, pLenValid, domainLenValid]
    sig_and_intros
    sig_close
    all_goals first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›
  post := by
    intro s t _ h
    sig_post [checkDomainContract, checkDomainSig, abi, argRegs, List.append_eq]
    sig_reduce [cdContract, cdPost, cdDom] at h
    exact h
  pub := by
    intro s₁ s₂ _ _ h
    sig_pub [checkDomainContract, checkDomainSig, abi, argRegs, List.append_eq, pLenValid, domainLenValid] at h
    exact h
  sat := by
    sig_implies_sat [checkDomainContract, checkDomainSig, abi, argRegs, List.append_eq, pLenValid, domainLenValid]
      [cdSat] using cdSat

end VG.Proof.Ffdh.X86_64.CheckDomain
