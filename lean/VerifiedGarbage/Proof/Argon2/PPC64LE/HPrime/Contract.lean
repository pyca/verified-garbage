module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Spec.Argon2.Contract
public import VerifiedGarbage.Proof.Argon2.Contract

/-! # H′ on PPC64LE: a local contract -/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.HPrime

open VG VG.PPC64LE

def inputR (s : State) : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
def outputR (s : State) : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
def workR (s : State) : Region := ⟨s.gpr .r7, 16384⟩
/-- The frames of the streaming functions H′ calls. -/
def stackR (s : State) : Region := below s.sp 48

def localContract : Contract isa where
  pre s := s.rd = [inputR s] ∧ s.wr = [outputR s, workR s] ∧
    (s.gpr .r4).toNat < 2 ^ 32 ∧ 1 ≤ (s.gpr .r6).toNat ∧ (s.gpr .r6).toNat < 2 ^ 32 ∧
    48 ≤ s.sp.toNat ∧
    (inputR s).Disjoint (workR s) ∧ (outputR s).Disjoint (workR s) ∧
    (stackR s).Disjoint (inputR s) ∧ (stackR s).Disjoint (outputR s) ∧ (stackR s).Disjoint (workR s)
  post s t := Spec.Blake2.bytesAt t.mem (s.gpr .r5) (s.gpr .r6).toNat =
    Spec.Argon2.hPrime (s.gpr .r6).toNat (Spec.Blake2.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)
  pub s t := s.gpr .r3 = t.gpr .r3 ∧ s.gpr .r4 = t.gpr .r4 ∧
    s.gpr .r5 = t.gpr .r5 ∧ s.gpr .r6 = t.gpr .r6 ∧ s.gpr .r7 = t.gpr .r7 ∧ s.sp = t.sp

end VG.Proof.Argon2.PPC64LE.HPrime
