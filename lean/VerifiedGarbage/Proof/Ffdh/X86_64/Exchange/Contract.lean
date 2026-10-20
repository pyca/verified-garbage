module

public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PowLit

/-! # FFDH exchange on x86-64: the internal contract -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Exchange

open VG VG.X86_64 VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt os2ip written)

def exPre (s : State) : Prop :=
  let out : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  let dom : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  let xr : Region := ⟨s.gpr .r9, (stackArg s 0).toNat⟩
  let peer : Region := ⟨stackArg s 1, (stackArg s 2).toNat⟩
  let scr : Region := ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  let args : Region := ⟨stackArgAddr s 0, 40⟩
  (s.gpr .rsp).toNat + 48 ≤ 2 ^ 64 ∧ s.rd = [dom, xr, peer, args] ∧ s.wr = [out, scr] ∧
    out.Disjoint dom ∧ out.Disjoint xr ∧ out.Disjoint peer ∧ out.Disjoint scr ∧ out.Disjoint args ∧
    dom.Disjoint scr ∧ xr.Disjoint scr ∧ peer.Disjoint scr ∧ scr.Disjoint args ∧
    (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r9).toNat + (stackArg s 0).toNat ≤ 2 ^ 64 ∧ (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64 ∧
    (stackArg s 3).toNat + (stackArg s 4).toNat * 8 ≤ 2 ^ 64 ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint out ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint dom ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint xr ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint peer ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint scr ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint args ∧
    pLenValid (s.gpr .r8).toNat ∧ domainLenValid (s.gpr .r8).toNat (s.gpr .rcx).toNat ∧
    (s.gpr .rsi).toNat = (s.gpr .r8).toNat ∧ (stackArg s 2).toNat = (s.gpr .r8).toNat ∧ 1 ≤ (stackArg s 0).toNat ∧
    (stackArg s 0).toNat ≤ (s.gpr .r8).toNat ∧ Spec.Rsa.scratchWords (s.gpr .r8).toNat ≤ (stackArg s 4).toNat

/-- The domain on entry. -/
abbrev exDom (s : State) : List Byte := bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat

/-- The peer's value on entry. -/
abbrev exY (s : State) : List Byte := bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat

/-- The scalar on entry. -/
abbrev exX (s : State) : List Byte := bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat

def exPost (s s' : State) : Prop :=
  domainValid (s.gpr .r8).toNat (exDom s) → publicValid ⟨domainOf (s.gpr .r8).toNat (exDom s), os2ip (exY s)⟩ →
    written s'.mem (s.gpr .rdi) (s.gpr .rsi).toNat ((s'.gpr .rax).setWidth 32)
      (exchangeOp (domainOf (s.gpr .r8).toNat (exDom s)) (os2ip (exX s)) (os2ip (exY s)))

def exLeak (s : State) : List Nat :=
  (exDom s).map (·.toNat) ++ (exY s).map (·.toNat) ++
    [if (exchangeOp (domainOf (s.gpr .r8).toNat (exDom s)) (os2ip (exX s)) (os2ip (exY s))).isSome then 1 else 0]

def exPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rsp = s₂.gpr .rsp ∧ exLeak s₁ = exLeak s₂ ∧
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧
    stackArg s₁ 3 = stackArg s₂ 3 ∧ stackArg s₁ 4 = stackArg s₂ 4

def exContract : Contract isa where
  pre := exPre
  post := exPost
  pub := exPub

def exSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 128 | .r8 => 64 | .r9 => 0x3000
    | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6008 then 1 else if a = 0x6010 then 0x00 else if a = 0x6011 then 0x31
    else if a = 0x6018 then 64 else if a = 0x6021 then 0x80 else if a = 0x6028 then 0x20
    else if a = 0x6029 then 0x04 else 0
  rd := [⟨0x2000, 128⟩, ⟨0x3000, 1⟩, ⟨0x3100, 64⟩, ⟨0x6008, 40⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x8000, 1056 * 8⟩]

theorem stackArgs_five (s : State) : List.map (stackArg s) (List.range 5) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4] := rfl

theorem ex_implies : exContract.Implies (exchangeContract abi) where
  pre := by
    intro s h
    sig_pre [exchangeContract, exchangeSig, abi, argRegs, stackArgs_five, List.append_eq, pLenValid, domainLenValid] at h
    sig_pre [exchangeContract, exchangeSig, abi, argRegs, stackArgs_five, List.append_eq, pLenValid, domainLenValid] at h
    sig_split h
    sig_reduce [exContract, exPre, pLenValid, domainLenValid]
    sig_and_intros
    sig_close
    all_goals first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›
  post := by
    intro s t _ h
    sig_post [exchangeContract, exchangeSig, abi, argRegs, stackArgs_five, List.append_eq]
    sig_reduce [exContract, exPost, exDom, exX, exY] at h
    exact h
  pub := by
    intro s₁ s₂ _ _ h
    sig_pub [exchangeContract, exchangeSig, abi, argRegs, stackArgs_five, List.append_eq, pLenValid, domainLenValid] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    exact h
  sat := by
    sig_implies_sat [exchangeContract, exchangeSig, abi, argRegs, stackArgs_five, List.append_eq, pLenValid, domainLenValid]
      [exSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using exSat

end VG.Proof.Ffdh.X86_64.Exchange
