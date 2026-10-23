module

public import VerifiedGarbage.Spec.Ffdh.DerivePublicContract
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PowLit

/-! # FFDH public-value derivation on x86-64: internal contract -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.DerivePublic

open VG VG.X86_64 VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt os2ip i2osp powMod)

def dvPre (s : State) : Prop :=
  let y : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  let dom : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  let x : Region := ⟨s.gpr .r9, (stackArg s 0).toNat⟩
  let scr : Region := ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
  let args : Region := ⟨stackArgAddr s 0, 24⟩
  (s.gpr .rsp).toNat + 32 ≤ 2 ^ 64 ∧ s.rd = [dom, x, args] ∧ s.wr = [y, scr] ∧
    y.Disjoint dom ∧ y.Disjoint x ∧ y.Disjoint scr ∧ y.Disjoint args ∧
    dom.Disjoint scr ∧ x.Disjoint scr ∧ scr.Disjoint args ∧
    (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r9).toNat + (stackArg s 0).toNat ≤ 2 ^ 64 ∧ (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64 ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint y ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint dom ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint x ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint scr ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint args ∧
    pLenValid (s.gpr .r8).toNat ∧ domainLenValid (s.gpr .r8).toNat (s.gpr .rcx).toNat ∧
    (s.gpr .rsi).toNat = (s.gpr .r8).toNat ∧ 1 ≤ (stackArg s 0).toNat ∧ (stackArg s 0).toNat ≤ (s.gpr .r8).toNat ∧
    Spec.Rsa.scratchWords (s.gpr .r8).toNat ≤ (stackArg s 2).toNat

/-- The domain on entry. -/
abbrev dvDom (s : State) : List Byte := bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat

/-- x on entry. -/
abbrev dvX (s : State) : List Byte := bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat

/-- The parameters. -/
abbrev dvA (s : State) : Parameters := domainOf (s.gpr .r8).toNat (dvDom s)

def dvPost (s s' : State) : Prop :=
  domainValid (s.gpr .r8).toNat (dvDom s) →
    ((s'.gpr .rax).setWidth 32).toNat = keyStatus (dvA s) (os2ip (dvX s)) ∧
      if keyStatus (dvA s) (os2ip (dvX s)) = 1 then
        bytesAt s'.mem (s.gpr .rdi) (s.gpr .r8).toNat =
          i2osp (powMod (dvA s).g (os2ip (dvX s)) (dvA s).p) (s.gpr .r8).toNat
      else bytesAt s'.mem (s.gpr .rdi) (s.gpr .r8).toNat = List.replicate (s.gpr .r8).toNat 0

/-- What timing may depend on, beyond the arguments. -/
def dvLeak (s : State) : List Nat := (dvDom s).map (·.toNat) ++ [keyStatus (dvA s) (os2ip (dvX s))]

def dvPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rsp = s₂.gpr .rsp ∧ dvLeak s₁ = dvLeak s₂ ∧
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2

def dvContract : Contract isa where
  pre := dvPre
  post := dvPost
  pub := dvPub

theorem stackArgs_three (s : State) : List.map (stackArg s) (List.range 3) =
    [stackArg s 0, stackArg s 1, stackArg s 2] := rfl

/-- A 64-byte domain without q, a one-byte scalar, and disjoint output and workspace. -/
def dvSat : State where
  gpr r := match r with
    | .rdi => 0x2000 | .rsi => 64 | .rdx => 0x1000 | .rcx => 128 | .r8 => 64 | .r9 => 0x3000
    | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8008 then 1 else if a = 0x8011 then 0x40
    else if a = 0x8018 then 0x20 else if a = 0x8019 then 0x04 else 0
  rd := [⟨0x1000, 128⟩, ⟨0x3000, 1⟩, ⟨0x8008, 24⟩]
  wr := [⟨0x2000, 64⟩, ⟨0x4000, 8448⟩]

theorem dv_implies : dvContract.Implies (derivePublicContract abi) where
  pre := by
    intro s h
    sig_pre [derivePublicContract, derivePublicSig, abi, argRegs, stackArgs_three, List.append_eq,
      pLenValid, domainLenValid] at h
    sig_pre [derivePublicContract, derivePublicSig, abi, argRegs, stackArgs_three, List.append_eq,
      pLenValid, domainLenValid] at h
    sig_split h
    sig_reduce [dvContract, dvPre, pLenValid, domainLenValid]
    sig_and_intros
    sig_close
    all_goals first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›
  post := by
    sig_implies_post [derivePublicContract, derivePublicSig, abi, argRegs, dvContract, dvPost,
      stackArgs_three, List.append_eq]
  pub := by
    intro s₁ s₂ _ _ h
    sig_pub [derivePublicContract, derivePublicSig, abi, argRegs, stackArgs_three, List.append_eq,
      pLenValid, domainLenValid] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    exact h
  sat := by
    sig_implies_sat [derivePublicContract, derivePublicSig, abi, argRegs, dvContract, dvPre,
      stackArgs_three, List.append_eq, pLenValid, domainLenValid]
      [dvSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using dvSat

end VG.Proof.Ffdh.X86_64.DerivePublic
