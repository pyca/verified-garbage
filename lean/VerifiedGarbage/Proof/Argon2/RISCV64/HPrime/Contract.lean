module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Spec.Argon2

/-!
# H′ on RISC-V: its contract

`vg_argon2_hprime` is an internal function, which only the derivation
calls, with its rounded scratch: the contract its proof is of, and the
derivation's proof composes, states that `scratch` is 8-byte aligned. H′ uses
no stack.
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.HPrime

open VG VG.RISCV64

def inputR (s : State) : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
def outputR (s : State) : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
def workR (s : State) : Region := ⟨s.gpr .a4, 16384⟩

def localContract : Contract isa where
  pre s := s.rd = [inputR s] ∧ s.wr = [outputR s, workR s] ∧
    (s.gpr .a1).toNat < 2 ^ 32 ∧ 1 ≤ (s.gpr .a3).toNat ∧ (s.gpr .a3).toNat < 2 ^ 32 ∧
    (s.gpr .a4).toNat % 8 = 0 ∧
    (inputR s).Disjoint (workR s) ∧ (outputR s).Disjoint (workR s)
  post s t := Spec.Blake2.bytesAt t.mem (s.gpr .a2) (s.gpr .a3).toNat =
    Spec.Argon2.hPrime (s.gpr .a3).toNat (Spec.Blake2.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat)
  pub s t := s.gpr .a0 = t.gpr .a0 ∧ s.gpr .a1 = t.gpr .a1 ∧
    s.gpr .a2 = t.gpr .a2 ∧ s.gpr .a3 = t.gpr .a3 ∧ s.gpr .a4 = t.gpr .a4 ∧ s.sp = t.sp

end VG.Proof.Argon2.RISCV64.HPrime
