import VerifiedGarbage.Spec.EcKey.P256
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Contract

/-!
# P-256 public keys on 32-bit ARM: the contract the proof is written against

The facts of `Spec.EcKey.P256.inst.publicKeyContract` for 32-bit ARM, by
name: `vg_ec_p256_public_key(out, d, scratch)`, with the arguments in
`r0`–`r2` (AAPCS), the result in `r0` (the low word of `r1:r0`).
-/

namespace VG.Proof.EcKey.Arm

open VG VG.Arm Spec.Weierstrass Spec.EcKey

/-- The public key of the private key at `d`, as the specification computes it. -/
abbrev pk (m : Mem) (d : Addr) : Option (Point Spec.P256.curve) :=
  publicKey Spec.P256.curve (ofBytes (bytesAt m d 32))

def pkArm : Contract Arm.isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 65⟩
    let d : Region := ⟨State.addr (s.gpr .r1), 32⟩
    let scratch : Region := ⟨State.addr (s.gpr .r2), 8192⟩
    s.rd = [d] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ d.Disjoint scratch ∧
      (s.gpr .r0).toNat + 65 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 32 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 8192 ≤ 2 ^ 32
  post s s' :=
    match pk s.mem (State.addr (s.gpr .r1)) with
    | some (.affine x y) => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 1 ∧
      bytesAt s'.mem (State.addr (s.gpr .r0)) 65 = encodePoint (.affine x y)
    | _ => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 0 ∧
      bytesAt s'.mem (State.addr (s.gpr .r0)) 65 = List.replicate 65 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2

end VG.Proof.EcKey.Arm
