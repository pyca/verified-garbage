import VerifiedGarbage.Spec.Ecdsa.P224
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ECDSA over P-224 on 32-bit ARM: the contract the proof is written against

The facts of `Spec.Ecdsa.P224.inst.signContract` for 32-bit ARM, by name:
`vg_ecdsa_p224_sign(out, d, digest, k, scratch)`, with `out`, `d`, `digest`
and `k` in `r0`–`r3` and `scratch` on the stack (AAPCS), the result in `r0`
(the low word of `r1:r0`).
-/

namespace VG.Proof.Ecdsa.Arm.P224

open VG VG.Arm Spec.Weierstrass Spec.Ecdsa

/-- The signature of the arguments, as the specification computes it. -/
abbrev sig (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  signWith Spec.P224.curve (ofBytes (bytesAt m d 28)) (hashToInt Spec.P224.curve (bytesAt m digest 28))
    (ofBytes (bytesAt m k 28))

def signArm : Contract Arm.isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 56⟩
    let d : Region := ⟨State.addr (s.gpr .r1), 28⟩
    let digest : Region := ⟨State.addr (s.gpr .r2), 28⟩
    let k : Region := ⟨State.addr (s.gpr .r3), 28⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 8192⟩
    let args : Region := ⟨State.addr s.sp, 4⟩
    s.rd = [d, digest, k, args] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ k.Disjoint scratch ∧
      out.Disjoint args ∧ scratch.Disjoint args ∧
      (s.gpr .r0).toNat + 56 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 28 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 28 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 28 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 8192 ≤ 2 ^ 32 ∧ s.sp.toNat + 4 ≤ 2 ^ 32
  post s s' :=
    match sig s.mem (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2)) (State.addr (s.gpr .r3)) with
    | some rs => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 1 ∧
      bytesAt s'.mem (State.addr (s.gpr .r0)) 56 = encode Spec.P224.curve rs
    | none => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 0 ∧
      bytesAt s'.mem (State.addr (s.gpr .r0)) 56 = List.replicate 56 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

end VG.Proof.Ecdsa.Arm.P224
