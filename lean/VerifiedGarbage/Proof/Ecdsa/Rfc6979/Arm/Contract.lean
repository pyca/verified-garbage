import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Generic
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Deterministic ECDSA on 32-bit ARM: the contract the proof is written against

The facts of `I.signContract` for an instance `I` of a curve of `len`-byte
scalars with a hash of `I.hashLen` bytes, for 32-bit ARM and `N` bytes of
stack, by name:
`vg_ecdsa_<curve>_<hash>_sign(out = r0, d = r1, digest = r2, scratch = r3)`,
the result in `r0` (the low word of `r1:r0`). Each instance's file shows
`I.signContract` implies it.
-/

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm Spec.Weierstrass Spec.Ecdsa

/-- RFC 6979's signature of the arguments, and the number of candidates tried. -/
abbrev result (I : Spec.Ecdsa.Rfc6979.Instance) (m : Mem) (d digest : Addr) : Option (Nat × Nat) × Nat :=
  I.result m d digest

/-- The `N` bytes of stack below `sp`. -/
abbrev stkR (sp : BitVec 32) (N : Nat) : Region := ⟨State.addr sp - BitVec.ofNat 64 N, N⟩

def rfcArm (I : Spec.Ecdsa.Rfc6979.Instance) (N : Nat) : Contract Arm.isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 2 * I.ecdsa.curve.len⟩
    let d : Region := ⟨State.addr (s.gpr .r1), I.ecdsa.curve.len⟩
    let digest : Region := ⟨State.addr (s.gpr .r2), I.hashLen⟩
    let scratch : Region := ⟨State.addr (s.gpr .r3), 8192⟩
    let stk : Region := stkR s.sp N
    s.rd = [d, digest] ∧ s.wr = [out, scratch] ∧
      out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint scratch ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧
      stk.Disjoint out ∧ stk.Disjoint d ∧ stk.Disjoint digest ∧ stk.Disjoint scratch ∧
      (s.gpr .r0).toNat + 2 * I.ecdsa.curve.len ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + I.ecdsa.curve.len ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + I.hashLen ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + 8192 ≤ 2 ^ 32 ∧ N ≤ s.sp.toNat
  post s s' :=
    match (result I s.mem (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2))).1 with
    | some rs => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 1 ∧
        bytesAt s'.mem (State.addr (s.gpr .r0)) (2 * I.ecdsa.curve.len) = encode I.ecdsa.curve rs
    | none => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 0 ∧
        bytesAt s'.mem (State.addr (s.gpr .r0)) (2 * I.ecdsa.curve.len) = List.replicate (2 * I.ecdsa.curve.len) 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    (result I s₁.mem (State.addr (s₁.gpr .r1)) (State.addr (s₁.gpr .r2))).2 =
      (result I s₂.mem (State.addr (s₂.gpr .r1)) (State.addr (s₂.gpr .r2))).2

/-- A state satisfying the precondition, for scalars of `Q` bytes and a
digest of `D` bytes. -/
def satState (Q D : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x8000 | _ => 0
  sp := 0x20000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, Q⟩, ⟨0x3000, D⟩]
  wr := [⟨0x1000, 2 * Q⟩, ⟨0x8000, 8192⟩]

end VG.Proof.Ecdsa.Rfc6979.Arm
