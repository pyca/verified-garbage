import VerifiedGarbage.Spec.Ecdsa.Verify.P224
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ECDSA verification over P-224 on 32-bit ARM: the contract the proof is written against

The facts of `Spec.Ecdsa.P224.inst.verifyContract` for 32-bit ARM, by name:
`vg_ecdsa_p224_verify(public, digest, sig, scratch)`, with the arguments in
`r0`–`r3` (AAPCS), the result in `r0` (the low word of `r1:r0`). Only the
pointers are public here: the proof shows that nothing else affects timing,
although the contract would let the contents of the three buffers.
-/

namespace VG.Proof.Ecdsa.Verify.Arm.P224

open VG VG.Arm Spec.Weierstrass Spec.Ecdsa

/-- Whether the signature at `sig` of the hash at `digest` is valid for the
public key at `pk`, as the specification says. -/
abbrev vf (m : Mem) (pk digest sig : Addr) : Bool :=
  verify Spec.P224.curve (bytesAt m pk 57) (hashToInt Spec.P224.curve (bytesAt m digest 28)) (bytesAt m sig 56)

def verifyArm : Contract Arm.isa where
  pre s :=
    let pk : Region := ⟨State.addr (s.gpr .r0), 57⟩
    let digest : Region := ⟨State.addr (s.gpr .r1), 28⟩
    let sig : Region := ⟨State.addr (s.gpr .r2), 56⟩
    let scratch : Region := ⟨State.addr (s.gpr .r3), 8192⟩
    s.rd = [pk, digest, sig] ∧ s.wr = [scratch] ∧ pk.Disjoint scratch ∧ digest.Disjoint scratch ∧
      sig.Disjoint scratch ∧ (s.gpr .r0).toNat + 57 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 28 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 56 ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + 8192 ≤ 2 ^ 32
  post s s' := BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) =
    if vf s.mem (State.addr (s.gpr .r0)) (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2)) then 1 else 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3

end VG.Proof.Ecdsa.Verify.Arm.P224
