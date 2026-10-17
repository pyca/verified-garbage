module

public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.AnyHash
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.Contract
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# Deterministic ECDSA on 32-bit ARM: the contract the proof is written against

The facts of `I.signAnyContract` for an instance `I` of a curve of
`len`-byte scalars, for 32-bit ARM and `N` bytes of stack, by name:
`vg_ecdsa_<curve>_rfc6979_sign(out = r0, d = r1, digest = r2,
digest_len = r3, scratch, hash)`, `scratch` and `hash` on the stack (AAPCS),
the result in `r0` (the low word of `r1:r0`). Each curve's file shows
`I.signAnyContract` implies it.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm Spec.Weierstrass Spec.Ecdsa

/-- The `N` bytes of stack below `sp`. -/
abbrev stkR (sp : BitVec 32) (N : Nat) : Region := ⟨State.addr sp - BitVec.ofNat 64 N, N⟩

/-- RFC 6979's signature of the arguments with the hash function `hash`
names, and the number of candidates tried, if it names one. -/
abbrev anyResult (I : Spec.Ecdsa.Rfc6979.Instance) (s : State) : Option (Option (Nat × Nat) × Nat) :=
  I.anyResult s.mem (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2)) (s.gpr .r3).toNat (stackArg s 1).toNat

def rfcArm (I : Spec.Ecdsa.Rfc6979.Instance) (N : Nat) : Contract Arm.isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 2 * I.ecdsa.curve.len⟩
    let d : Region := ⟨State.addr (s.gpr .r1), I.ecdsa.curve.len⟩
    let digest : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 8192⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    let stk : Region := stkR s.sp N
    s.rd = [d, digest, args] ∧ s.wr = [out, scratch] ∧
      out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint scratch ∧ out.Disjoint args ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ scratch.Disjoint args ∧
      stk.Disjoint out ∧ stk.Disjoint d ∧ stk.Disjoint digest ∧ stk.Disjoint scratch ∧
      (s.gpr .r0).toNat + 2 * I.ecdsa.curve.len ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + I.ecdsa.curve.len ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 8192 ≤ 2 ^ 32 ∧
      N ≤ s.sp.toNat ∧ s.sp.toNat + 8 ≤ 2 ^ 32 ∧
      (stackArg s 1).toNat ∈ Spec.Ecdsa.Rfc6979.hashIds ∧
      ∀ H, Spec.HashId.mgf1 (stackArg s 1).toNat = some H → (s.gpr .r3).toNat = H.len
  post s s' :=
    match anyResult I s with
    | some (some rs, _) => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 1 ∧
        bytesAt s'.mem (State.addr (s.gpr .r0)) (2 * I.ecdsa.curve.len) = encode I.ecdsa.curve rs
    | _ => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 0 ∧
        bytesAt s'.mem (State.addr (s.gpr .r0)) (2 * I.ecdsa.curve.len) = List.replicate (2 * I.ecdsa.curve.len) 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
    stackArg s₁ 1 = stackArg s₂ 1 ∧
    ((anyResult I s₁).map (·.2)).getD 0 = ((anyResult I s₂).map (·.2)).getD 0

/-- The stack arguments of `satState`: `scratch` at `0x8000`, then `hash`. -/
def satMem (hash : Nat) : Mem := fun a =>
  if a = 0x20000 then 0 else if a = 0x20001 then 0x80 else
    if a = 0x20004 then BitVec.ofNat 8 hash else 0

/-- A state satisfying the precondition, for scalars of `Q` bytes and a
digest of `D` bytes with the hash function `hash`. -/
def satState (Q D hash : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => BitVec.ofNat 32 D | _ => 0
  sp := 0x20000
  n := false
  z := false
  c := false
  v := false
  mem := satMem hash
  rd := [⟨0x2000, Q⟩, ⟨0x3000, D⟩, ⟨0x20000, 8⟩]
  wr := [⟨0x1000, 2 * Q⟩, ⟨0x8000, 8192⟩]

end VG.Proof.Ecdsa.Rfc6979.Arm
