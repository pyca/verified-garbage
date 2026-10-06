import VerifiedGarbage.Spec.Ecdsa.P192
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ECDSA over P-192 on 32-bit ARM: the contract the proof is written against

The facts of `Spec.Ecdsa.P192.inst.signContract` for 32-bit ARM, by name:
`vg_ecdsa_p192_sign(out, d, digest, k, scratch)`, with `out`, `d`, `digest`
and `k` in `r0`–`r3` and `scratch` on the stack (AAPCS), the result in `r0`
(the low word of `r1:r0`).
-/

namespace VG.Proof.Ecdsa.Arm.P192

open VG VG.Arm Spec.Weierstrass Spec.Ecdsa

/-- The signature of the arguments, as the specification computes it. -/
abbrev sig (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  signWith Spec.P192.curve (ofBytes (bytesAt m d 24)) (hashToInt Spec.P192.curve (bytesAt m digest 24))
    (ofBytes (bytesAt m k 24))

def signArm : Contract Arm.isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 48⟩
    let d : Region := ⟨State.addr (s.gpr .r1), 24⟩
    let digest : Region := ⟨State.addr (s.gpr .r2), 24⟩
    let k : Region := ⟨State.addr (s.gpr .r3), 24⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 8192⟩
    let args : Region := ⟨State.addr s.sp, 4⟩
    s.rd = [d, digest, k, args] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ k.Disjoint scratch ∧
      out.Disjoint args ∧ scratch.Disjoint args ∧
      (s.gpr .r0).toNat + 48 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 24 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 24 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 24 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 8192 ≤ 2 ^ 32 ∧ s.sp.toNat + 4 ≤ 2 ^ 32
  post s s' :=
    match sig s.mem (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2)) (State.addr (s.gpr .r3)) with
    | some rs => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 1 ∧
      bytesAt s'.mem (State.addr (s.gpr .r0)) 48 = encode Spec.P192.curve rs
    | none => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 0 ∧
      bytesAt s'.mem (State.addr (s.gpr .r0)) 48 = List.replicate 48 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

end VG.Proof.Ecdsa.Arm.P192
