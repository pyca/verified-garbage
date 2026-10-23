module

public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Generic
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call

/-!
# Deterministic ECDSA on PPC64LE: the contract the proof is written against

The facts of `I.signContract` for an instance `I` of a curve of `len`-byte
scalars with a hash of `I.hashLen` bytes, for PPC64LE and `N` bytes of
stack, by name: `vg_ecdsa_<curve>_<hash>_sign(out = r3, d = r4, digest = r5,
scratch = r6)`, the result in `r3` (ELFv2). Each instance's file shows
`I.signContract` implies it.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE Spec.Weierstrass Spec.Ecdsa

/-- RFC 6979's signature of the arguments, and the number of candidates tried. -/
abbrev result (I : Spec.Ecdsa.Rfc6979.Instance) (m : Mem) (d digest : Addr) : Option (Nat × Nat) × Nat :=
  I.result m d digest

def rfcPPC (I : Spec.Ecdsa.Rfc6979.Instance) (N : Nat) : Contract PPC64LE.isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 2 * I.ecdsa.curve.len⟩
    let d : Region := ⟨s.gpr .r4, I.ecdsa.curve.len⟩
    let digest : Region := ⟨s.gpr .r5, I.hashLen⟩
    let scratch : Region := ⟨s.gpr .r6, 8192⟩
    let stk : Region := below s.sp N
    s.rd = [d, digest] ∧ s.wr = [out, scratch] ∧
      out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint scratch ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧
      stk.Disjoint out ∧ stk.Disjoint d ∧ stk.Disjoint digest ∧ stk.Disjoint scratch ∧
      (s.gpr .r3).toNat + 2 * I.ecdsa.curve.len ≤ 2 ^ 64 ∧
      (s.gpr .r4).toNat + I.ecdsa.curve.len ≤ 2 ^ 64 ∧
      (s.gpr .r5).toNat + I.hashLen ≤ 2 ^ 64 ∧ (s.gpr .r6).toNat + 8192 ≤ 2 ^ 64 ∧ N ≤ s.sp.toNat
  post s s' :=
    match (result I s.mem (s.gpr .r4) (s.gpr .r5)).1 with
    | some rs => (s'.gpr .r3).setWidth 32 = 1 ∧
        bytesAt s'.mem (s.gpr .r3) (2 * I.ecdsa.curve.len) = encode I.ecdsa.curve rs
    | none => (s'.gpr .r3).setWidth 32 = 0 ∧
        bytesAt s'.mem (s.gpr .r3) (2 * I.ecdsa.curve.len) = List.replicate (2 * I.ecdsa.curve.len) 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
    s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.gpr .r6 = s₂.gpr .r6 ∧
    (result I s₁.mem (s₁.gpr .r4) (s₁.gpr .r5)).2 = (result I s₂.mem (s₂.gpr .r4) (s₂.gpr .r5)).2

/-- A state satisfying the precondition, for scalars of `Q` bytes and a
digest of `D` bytes. -/
def satState (Q D : Nat) : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x8000 | _ => 0
  lr := 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, Q⟩, ⟨0x3000, D⟩]
  wr := [⟨0x1000, 2 * Q⟩, ⟨0x8000, 8192⟩]

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
