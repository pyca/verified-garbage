import VerifiedGarbage.Spec.Ecdh.P521
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ECDH over P-521 on 32-bit ARM: the contract the proof is written against

The facts of `Spec.Ecdh.P521.inst.exchangeContract` for 32-bit ARM, by
name: `vg_ecdh_p521(out, d, peer, scratch)`, with the arguments in `r0`–`r3`
(AAPCS), the result in `r0` (the low word of `r1:r0`).
-/

namespace VG.Proof.Ecdh.Arm.P521

open VG VG.Arm Spec.Weierstrass Spec.EcKey

/-- The shared secret of the private key at `d` and the public key at
`peer`, as the specification computes it. -/
abbrev ex (m : Mem) (d peer : Addr) : Option (List Byte) :=
  Spec.Ecdh.exchange Spec.P521.curve (ofBytes (bytesAt m d 66)) (bytesAt m peer 133)

def ecdhArm : Contract Arm.isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 66⟩
    let d : Region := ⟨State.addr (s.gpr .r1), 66⟩
    let peer : Region := ⟨State.addr (s.gpr .r2), 133⟩
    let scratch : Region := ⟨State.addr (s.gpr .r3), 8192⟩
    s.rd = [d, peer] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ d.Disjoint scratch ∧
      peer.Disjoint scratch ∧ (s.gpr .r0).toNat + 66 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 66 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 133 ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + 8192 ≤ 2 ^ 32
  post s s' :=
    match ex s.mem (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2)) with
    | some z => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 1 ∧
      bytesAt s'.mem (State.addr (s.gpr .r0)) 66 = z
    | none => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 0 ∧
      bytesAt s'.mem (State.addr (s.gpr .r0)) 66 = List.replicate 66 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3

end VG.Proof.Ecdh.Arm.P521
