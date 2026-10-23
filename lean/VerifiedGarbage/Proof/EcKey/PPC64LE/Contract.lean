module

public import VerifiedGarbage.Spec.EcKey.Generic
public import VerifiedGarbage.Spec.P256
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Proof.Framework.PowLit

/-!
# P-256 public keys on PPC64LE: the contract the proof is written against

The facts of `Spec.EcKey.P256.inst.publicKeyContract` for PPC64LE, by name:
`vg_ec_p256_public_key(out, d, scratch)`, with the arguments in `r3`–`r5`
and the result in `r3` (ELFv2).
-/

@[expose] public section

namespace VG.Proof.EcKey.PPC64LE

open VG VG.PPC64LE Spec.Weierstrass Spec.EcKey

/-- The public key of the private key at `d`, as the specification computes it. -/
abbrev pk (m : Mem) (d : Addr) : Option (Point Spec.P256.curve) :=
  publicKey Spec.P256.curve (ofBytes (bytesAt m d 32))

def pkPPC : Contract PPC64LE.isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 65⟩
    let d : Region := ⟨s.gpr .r4, 32⟩
    let scratch : Region := ⟨s.gpr .r5, 8192⟩
    s.rd = [d] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ d.Disjoint scratch ∧
      (s.gpr .r3).toNat + 65 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match pk s.mem (s.gpr .r4) with
    | some (.affine x y) => s'.gpr .r3 = 1 ∧ bytesAt s'.mem (s.gpr .r3) 65 = encodePoint (.affine x y)
    | _ => s'.gpr .r3 = 0 ∧ bytesAt s'.mem (s.gpr .r3) 65 = List.replicate 65 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5

end VG.Proof.EcKey.PPC64LE
