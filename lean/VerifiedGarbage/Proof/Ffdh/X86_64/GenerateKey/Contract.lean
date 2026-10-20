module

public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PowLit

/-! # FFDH key-generation attempts on x86-64: internal contract -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt os2ip i2osp powMod)

def gkPre (s : State) : Prop :=
  let xr : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  let yr : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  let dom : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let rnd : Region := ⟨(stackArg s 1), (stackArg s 2).toNat⟩
  let scr : Region := ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  let args : Region := ⟨stackArgAddr s 0, 40⟩
  (s.gpr .rsp).toNat + 48 ≤ 2 ^ 64 ∧ s.rd = [dom, rnd, args] ∧ s.wr = [xr, yr, scr] ∧
    xr.Disjoint yr ∧ xr.Disjoint dom ∧ xr.Disjoint rnd ∧ xr.Disjoint scr ∧ xr.Disjoint args ∧
    yr.Disjoint dom ∧ yr.Disjoint rnd ∧ yr.Disjoint scr ∧ yr.Disjoint args ∧
    dom.Disjoint scr ∧ rnd.Disjoint scr ∧ scr.Disjoint args ∧
    (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ ((stackArg s 1)).toNat + (stackArg s 2).toNat ≤ 2 ^ 64 ∧
    (stackArg s 3).toNat + (stackArg s 4).toNat * 8 ≤ 2 ^ 64 ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint xr ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint yr ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint dom ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint rnd ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint scr ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint args ∧
    pLenValid ((stackArg s 0)).toNat ∧ domainLenValid ((stackArg s 0)).toNat (s.gpr .r9).toNat ∧
    (s.gpr .rsi).toNat = ((stackArg s 0)).toNat ∧ (s.gpr .rcx).toNat = ((stackArg s 0)).toNat ∧
    (stackArg s 2).toNat = ((stackArg s 0)).toNat ∧ Spec.Rsa.scratchWords ((stackArg s 0)).toNat ≤ (stackArg s 4).toNat

/-- The domain on entry. -/
abbrev gkDom (s : State) : List Byte := bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat

/-- The random octets on entry. -/
abbrev gkRand (s : State) : List Byte := bytesAt s.mem ((stackArg s 1)) (stackArg s 2).toNat

/-- The parameters. -/
abbrev gkA (s : State) : Parameters := domainOf ((stackArg s 0)).toNat (gkDom s)

/-- The attempt's scalar. -/
abbrev gkS (s : State) : Nat := scalarOfOctets (gkA s) (gkRand s)

def gkPost (s s' : State) : Prop :=
  domainValid ((stackArg s 0)).toNat (gkDom s) →
    ((s'.gpr .rax).setWidth 32).toNat = keyStatus (gkA s) (gkS s) ∧
      if keyStatus (gkA s) (gkS s) = 1 then
        bytesAt s'.mem (s.gpr .rdi) ((stackArg s 0)).toNat = i2osp (gkS s) ((stackArg s 0)).toNat ∧
          bytesAt s'.mem (s.gpr .rdx) ((stackArg s 0)).toNat = i2osp (powMod (gkA s).g (gkS s) (gkA s).p) ((stackArg s 0)).toNat
      else bytesAt s'.mem (s.gpr .rdi) ((stackArg s 0)).toNat = List.replicate ((stackArg s 0)).toNat 0 ∧
        bytesAt s'.mem (s.gpr .rdx) ((stackArg s 0)).toNat = List.replicate ((stackArg s 0)).toNat 0

/-- What timing may depend on, beyond the arguments. -/
def gkLeak (s : State) : List Nat := (gkDom s).map (·.toNat) ++ [keyStatus (gkA s) (gkS s)]

def gkPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rsp = s₂.gpr .rsp ∧ gkLeak s₁ = gkLeak s₂ ∧
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧
    stackArg s₁ 3 = stackArg s₂ 3 ∧ stackArg s₁ 4 = stackArg s₂ 4

def gkContract : Contract isa where
  pre := gkPre
  post := gkPost
  pub := gkPub

theorem stackArgs_five (s : State) : List.map (stackArg s) (List.range 5) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4] := rfl

/-- A 64-byte domain and disjoint output, random and workspace buffers. -/
def gkSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x1100 | .rcx => 64 | .r8 => 0x2000 | .r9 => 128
    | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6008 then 64 else if a = 0x6011 then 0x30 else if a = 0x6018 then 64
    else if a = 0x6021 then 0x80 else if a = 0x6028 then 0x20 else if a = 0x6029 then 0x04 else 0
  rd := [⟨0x2000, 128⟩, ⟨0x3000, 64⟩, ⟨0x6008, 40⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1100, 64⟩, ⟨0x8000, 1056 * 8⟩]

theorem gk_implies : gkContract.Implies (generateKeyContract abi) where
  pre := by
    intro s h
    sig_pre [generateKeyContract, generateKeySig, abi, argRegs, gkContract, gkPre, stackArgs_five, List.append_eq,
      pLenValid, domainLenValid] at h
    sig_pre [generateKeyContract, generateKeySig, abi, argRegs, gkContract, gkPre, stackArgs_five, List.append_eq,
      pLenValid, domainLenValid] at h
    sig_split h
    sig_reduce [generateKeyContract, generateKeySig, abi, argRegs, gkContract, gkPre, stackArgs_five,
      List.append_eq, pLenValid, domainLenValid]
    sig_and_intros
    sig_close
    all_goals first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›
  post := by
    sig_implies_post [generateKeyContract, generateKeySig, abi, argRegs, gkContract, gkPost, stackArgs_five,
      List.append_eq]
  pub := by
    intro s₁ s₂ _ _ h
    sig_pub [generateKeyContract, generateKeySig, abi, argRegs, stackArgs_five, List.append_eq,
      pLenValid, domainLenValid] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    exact h
  sat := by
    sig_implies_sat [generateKeyContract, generateKeySig, abi, argRegs, gkContract, gkPre, stackArgs_five,
      List.append_eq, pLenValid, domainLenValid] [gkSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using gkSat

end VG.Proof.Ffdh.X86_64.GenerateKey
