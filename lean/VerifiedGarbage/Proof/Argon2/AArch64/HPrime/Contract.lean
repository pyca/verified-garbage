module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Spec.Argon2.Contract
public import VerifiedGarbage.Proof.Argon2.Contract

/-! # H′: a local ARM64 contract -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64

def inputR (s : State) : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
def outputR (s : State) : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
def workR (s : State) : Region := ⟨s.gpr .x4, 16384⟩
def stackR (s : State) : Region := below s.sp 16

def localContract : Contract isa where
  pre s := s.rd = [inputR s] ∧ s.wr = [outputR s, workR s] ∧
    (s.gpr .x1).toNat < 2 ^ 32 ∧ 1 ≤ (s.gpr .x3).toNat ∧ (s.gpr .x3).toNat < 2 ^ 32 ∧
    16 ≤ s.sp.toNat ∧
    (inputR s).Disjoint (workR s) ∧ (outputR s).Disjoint (workR s) ∧
    (stackR s).Disjoint (inputR s) ∧ (stackR s).Disjoint (outputR s) ∧ (stackR s).Disjoint (workR s)
  post s t := Spec.Blake2.bytesAt t.mem (s.gpr .x2) (s.gpr .x3).toNat =
    Spec.Argon2.hPrime (s.gpr .x3).toNat (Spec.Blake2.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
  pub s t := s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧
    s.gpr .x2 = t.gpr .x2 ∧ s.gpr .x3 = t.gpr .x3 ∧ s.gpr .x4 = t.gpr .x4 ∧ s.sp = t.sp

end VG.Proof.Argon2.AArch64.HPrime
