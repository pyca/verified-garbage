module

public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PowLit

/-! # FFDH private-key validation on x86-64: internal contract -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPrivate

open VG VG.X86_64 VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt os2ip)

def kpPre (s : State) : Prop :=
  let dom : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  let y : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  let x : Region := ⟨s.gpr .r9, (stackArg s 0).toNat⟩
  let scr : Region := ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
  let args : Region := ⟨stackArgAddr s 0, 24⟩
  (s.gpr .rsp).toNat + 32 ≤ 2 ^ 64 ∧ s.rd = [dom, y, x, args] ∧ s.wr = [scr] ∧
    dom.Disjoint scr ∧ y.Disjoint scr ∧ x.Disjoint scr ∧ scr.Disjoint args ∧
    (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r9).toNat + (stackArg s 0).toNat ≤ 2 ^ 64 ∧ (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64 ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint dom ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint y ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint x ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint scr ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint args ∧
    pLenValid (s.gpr .rdx).toNat ∧ domainLenValid (s.gpr .rdx).toNat (s.gpr .rsi).toNat ∧
    (s.gpr .r8).toNat = (s.gpr .rdx).toNat ∧ 1 ≤ (stackArg s 0).toNat ∧ (stackArg s 0).toNat ≤ (s.gpr .rdx).toNat ∧
    Spec.Rsa.scratchWords (s.gpr .rdx).toNat ≤ (stackArg s 2).toNat

/-- The domain on entry. -/
abbrev kpDom (s : State) : List Byte := bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat

/-- y on entry. -/
abbrev kpY (s : State) : List Byte := bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat

/-- x on entry. -/
abbrev kpX (s : State) : List Byte := bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat

def kpPost (s s' : State) : Prop :=
  domainValid (s.gpr .rdx).toNat (kpDom s) →
    ((s'.gpr .rax).setWidth 32).toNat = privateStatus (domainOf (s.gpr .rdx).toNat (kpDom s)) (os2ip (kpY s))
      (os2ip (kpX s))

/-- What timing may depend on, beyond the arguments. -/
def kpLeak (s : State) : List Nat :=
  (kpDom s).map (·.toNat) ++ (kpY s).map (·.toNat) ++
    [privateStatus (domainOf (s.gpr .rdx).toNat (kpDom s)) (os2ip (kpY s)) (os2ip (kpX s))]

def kpPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rsp = s₂.gpr .rsp ∧ kpLeak s₁ = kpLeak s₂ ∧
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2

def kpContract : Contract isa where
  pre := kpPre
  post := kpPost
  pub := kpPub

def kpSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 128 | .rdx => 64 | .rcx => 0x2000 | .r8 => 64 | .r9 => 0x3000
    | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8008 then 1 else if a = 0x8011 then 0x40
    else if a = 0x8018 then 0x20 else if a = 0x8019 then 0x04 else 0
  rd := [⟨0x1000, 128⟩, ⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x8008, 24⟩]
  wr := [⟨0x4000, 8448⟩]

theorem stackArgs_three (s : State) : List.map (stackArg s) (List.range 3) =
    [stackArg s 0, stackArg s 1, stackArg s 2] := rfl

theorem kp_implies : kpContract.Implies (checkPrivateContract abi) where
  pre := by
    intro s h
    sig_pre [checkPrivateContract, checkPrivateSig, abi, argRegs, stackArgs_three, List.append_eq, pLenValid, domainLenValid] at h
    sig_pre [checkPrivateContract, checkPrivateSig, abi, argRegs, stackArgs_three, List.append_eq, pLenValid, domainLenValid] at h
    sig_split h
    sig_reduce [kpContract, kpPre, pLenValid, domainLenValid]
    sig_and_intros
    sig_close
    all_goals first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›
  post := by
    intro s t _ h
    sig_post [checkPrivateContract, checkPrivateSig, abi, argRegs, stackArgs_three, List.append_eq]
    sig_reduce [kpContract, kpPost, kpDom, kpX, kpY] at h
    exact h
  pub := by
    intro s₁ s₂ _ _ h
    sig_pub [checkPrivateContract, checkPrivateSig, abi, argRegs, stackArgs_three, List.append_eq, pLenValid, domainLenValid] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    exact h
  sat := by
    sig_implies_sat [checkPrivateContract, checkPrivateSig, abi, argRegs, stackArgs_three, List.append_eq, pLenValid, domainLenValid]
      [kpSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using kpSat

end VG.Proof.Ffdh.X86_64.CheckPrivate
