import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Generic
import VerifiedGarbage.Spec.Ecdsa.P256
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Deterministic ECDSA over P-256 on 32-bit ARM: the contract the proof is written against

The facts of `I.signContract` for an instance `I` of P-256 with a hash of
`I.hashLen` bytes, for 32-bit ARM and 224 bytes of stack, by name:
`vg_ecdsa_p256_<hash>_sign(out = r0, d = r1, digest = r2, scratch = r3)`,
the result in `r0` (the low word of `r1:r0`). Each instance's file shows
`I.signContract` implies it.
-/

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm Spec.Weierstrass Spec.Ecdsa

/-- RFC 6979's signature of the arguments, and the number of candidates tried. -/
abbrev result (I : Spec.Ecdsa.Rfc6979.Instance) (m : Mem) (d digest : Addr) : Option (Nat × Nat) × Nat :=
  I.result m d digest

/-- The 224 bytes of stack below `sp`. -/
abbrev stkR (sp : BitVec 32) : Region := ⟨State.addr sp - BitVec.ofNat 64 224, 224⟩

def rfcArm (I : Spec.Ecdsa.Rfc6979.Instance) : Contract Arm.isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 64⟩
    let d : Region := ⟨State.addr (s.gpr .r1), 32⟩
    let digest : Region := ⟨State.addr (s.gpr .r2), I.hashLen⟩
    let scratch : Region := ⟨State.addr (s.gpr .r3), 8192⟩
    let stk : Region := stkR s.sp
    s.rd = [d, digest] ∧ s.wr = [out, scratch] ∧
      out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint scratch ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧
      stk.Disjoint out ∧ stk.Disjoint d ∧ stk.Disjoint digest ∧ stk.Disjoint scratch ∧
      (s.gpr .r0).toNat + 64 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 32 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + I.hashLen ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + 8192 ≤ 2 ^ 32 ∧ 224 ≤ s.sp.toNat
  post s s' :=
    match (result I s.mem (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2))).1 with
    | some rs => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 1 ∧
        bytesAt s'.mem (State.addr (s.gpr .r0)) 64 = encode Spec.P256.curve rs
    | none => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 0 ∧
        bytesAt s'.mem (State.addr (s.gpr .r0)) 64 = List.replicate 64 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    (result I s₁.mem (State.addr (s₁.gpr .r1)) (State.addr (s₁.gpr .r2))).2 =
      (result I s₂.mem (State.addr (s₂.gpr .r1)) (State.addr (s₂.gpr .r2))).2

/-- A state satisfying the precondition, for a digest of `D` bytes. -/
def satState (D : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x8000 | _ => 0
  sp := 0x20000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 32⟩, ⟨0x3000, D⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x8000, 8192⟩]

end VG.Proof.Ecdsa.Rfc6979.Arm
