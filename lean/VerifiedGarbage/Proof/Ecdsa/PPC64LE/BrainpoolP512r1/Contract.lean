module

public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Spec.BrainpoolP512r1
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Ecdsa.Contract

/-!
# ECDSA signatures over brainpoolP512r1 on PPC64LE: the contract the proof is written against

The facts of `Proof.Ecdsa.Instance.signContract Spec.Ecdsa.BrainpoolP512r1.inst` for PPC64LE, by name:
`vg_ecdsa_brainpoolp512r1_sign(out, d, digest, k, scratch)`, with the arguments in
`r3`–`r7` and the result in `r3` (ELFv2).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE.BrainpoolP512r1

open VG VG.PPC64LE Spec.Weierstrass Spec.Ecdsa

/-- The signature of the arguments, as the specification computes it. -/
abbrev sig (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  signWith Spec.BrainpoolP512r1.curve (ofBytes (bytesAt m d 64)) (hashToInt Spec.BrainpoolP512r1.curve (bytesAt m digest 64))
    (ofBytes (bytesAt m k 64))

def signPPC : Contract PPC64LE.isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 128⟩
    let d : Region := ⟨s.gpr .r4, 64⟩
    let digest : Region := ⟨s.gpr .r5, 64⟩
    let k : Region := ⟨s.gpr .r6, 64⟩
    let scratch : Region := ⟨s.gpr .r7, 8192⟩
    s.rd = [d, digest, k] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ k.Disjoint scratch ∧
      (s.gpr .r3).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 64 ≤ 2 ^ 64 ∧
      (s.gpr .r6).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .r7).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match sig s.mem (s.gpr .r4) (s.gpr .r5) (s.gpr .r6) with
    | some rs => s'.gpr .r3 = 1 ∧ bytesAt s'.mem (s.gpr .r3) 128 = encode Spec.BrainpoolP512r1.curve rs
    | none => s'.gpr .r3 = 0 ∧ bytesAt s'.mem (s.gpr .r3) 128 = List.replicate 128 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
    s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7

end VG.Proof.Ecdsa.PPC64LE.BrainpoolP512r1
