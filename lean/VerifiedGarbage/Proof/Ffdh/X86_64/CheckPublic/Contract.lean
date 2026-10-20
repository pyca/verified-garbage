module

public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PowLit

/-! # FFDH public-key validation on x86-64: internal contract -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPublic

open VG VG.X86_64 VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt os2ip)

abbrev scrLen (s : State) : BitVec 64 := stackArg s 0
abbrev args (s : State) : Region := ⟨stackArgAddr s 0, 8⟩
abbrev retAddr (s : State) : Region := ⟨s.gpr .rsp, 8⟩

def cpPre (s : State) : Prop :=
  let dom : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  let y : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  let scr : Region := ⟨s.gpr .r9, (scrLen s).toNat * 8⟩
  (s.gpr .rsp).toNat + 16 ≤ 2 ^ 64 ∧
    s.rd = [dom, y, args s] ∧ s.wr = [scr] ∧
    dom.Disjoint scr ∧ y.Disjoint scr ∧ scr.Disjoint (args s) ∧
    (retAddr s).Disjoint dom ∧ (retAddr s).Disjoint y ∧ (retAddr s).Disjoint scr ∧
    (retAddr s).Disjoint (args s) ∧
    (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧
    (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r9).toNat + (scrLen s).toNat * 8 ≤ 2 ^ 64 ∧
    pLenValid (s.gpr .rdx).toNat ∧ domainLenValid (s.gpr .rdx).toNat (s.gpr .rsi).toNat ∧
    (s.gpr .r8).toNat = (s.gpr .rdx).toNat ∧ Spec.Rsa.scratchWords (s.gpr .rdx).toNat ≤ (scrLen s).toNat

abbrev cpDom (s : State) : List Byte := bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat

def cpPost (s t : State) : Prop :=
  domainValid (s.gpr .rdx).toNat (cpDom s) →
    ((t.gpr .rax).setWidth 32).toNat =
      if publicValid ⟨domainOf (s.gpr .rdx).toNat (cpDom s),
        os2ip (bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)⟩ then 1 else 0

def cpLeak (s : State) : List Nat :=
  (cpDom s).map (·.toNat) ++ (bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat).map (·.toNat)

def cpPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rsp = s₂.gpr .rsp ∧ cpLeak s₁ = cpLeak s₂ ∧
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧ scrLen s₁ = scrLen s₂

def cpContract : Contract isa where
  pre := cpPre
  post := cpPost
  pub := cpPub

def cpSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 128 | .rdx => 64 | .rcx => 0x2000 | .r8 => 64 | .r9 => 0x4000 | .rsp => 0x8000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8008 then 0x20 else if a = 0x8009 then 0x04 else 0
  rd := [⟨0x1000, 128⟩, ⟨0x2000, 64⟩, ⟨0x8008, 8⟩]
  wr := [⟨0x4000, 8448⟩]

theorem stackArgs_one (s : State) : List.map (stackArg s) (List.range 1) = [stackArg s 0] := rfl

theorem cp_implies : cpContract.Implies (checkPublicContract abi) where
  pre := by
    intro s h
    sig_pre [checkPublicContract, checkPublicSig, abi, argRegs, stackArgs_one, List.append_eq, pLenValid, domainLenValid] at h
    sig_pre [checkPublicContract, checkPublicSig, abi, argRegs, stackArgs_one, List.append_eq, pLenValid, domainLenValid] at h
    sig_split h
    sig_reduce [cpContract, cpPre, scrLen, args, retAddr, pLenValid, domainLenValid]
    sig_and_intros
    sig_close
    all_goals first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›
  post := by
    intro s t _ h
    sig_post [checkPublicContract, checkPublicSig, abi, argRegs, stackArgs_one, List.append_eq]
    sig_reduce [cpContract, cpPost, cpDom] at h
    exact h
  pub := by
    intro s₁ s₂ _ _ h
    sig_pub [checkPublicContract, checkPublicSig, abi, argRegs, stackArgs_one, List.append_eq, pLenValid, domainLenValid] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    exact h
  sat := by
    sig_implies_sat [checkPublicContract, checkPublicSig, abi, argRegs, stackArgs_one, List.append_eq, pLenValid, domainLenValid]
      [cpSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using cpSat

end VG.Proof.Ffdh.X86_64.CheckPublic
