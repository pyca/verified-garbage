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

end VG.Proof.Ffdh.X86_64.GenerateKey
