import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Generic
import VerifiedGarbage.Spec.Ecdsa.P256
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-!
# Deterministic ECDSA over P-256 on AArch64: the contract the proof is written against

The facts of `I.signContract` for an instance `I` of P-256 with a hash of
`I.hashLen` bytes, for AArch64 and 240 bytes of stack, by name:
`vg_ecdsa_p256_<hash>_sign(out = x0, d = x1, digest = x2, scratch = x3)`,
the result in `w0`. Each instance's file shows `I.signContract` implies it.
-/

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 Spec.Weierstrass Spec.Ecdsa

/-- RFC 6979's signature of the arguments, and the number of candidates tried. -/
abbrev result (I : Spec.Ecdsa.Rfc6979.Instance) (m : Mem) (d digest : Addr) : Option (Nat × Nat) × Nat :=
  I.result m d digest

def rfcAArch64 (I : Spec.Ecdsa.Rfc6979.Instance) : Contract AArch64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 64⟩
    let d : Region := ⟨s.gpr .x1, 32⟩
    let digest : Region := ⟨s.gpr .x2, I.hashLen⟩
    let scratch : Region := ⟨s.gpr .x3, 8192⟩
    let stk : Region := below s.sp 240
    s.rd = [d, digest] ∧ s.wr = [out, scratch] ∧
      out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint scratch ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧
      stk.Disjoint out ∧ stk.Disjoint d ∧ stk.Disjoint digest ∧ stk.Disjoint scratch ∧
      (s.gpr .x0).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 32 ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + I.hashLen ≤ 2 ^ 64 ∧ (s.gpr .x3).toNat + 8192 ≤ 2 ^ 64 ∧ 240 ≤ s.sp.toNat
  post s s' :=
    match (result I s.mem (s.gpr .x1) (s.gpr .x2)).1 with
    | some rs => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x0) 64 = encode Spec.P256.curve rs
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .x0) 64 = List.replicate 64 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧
    (result I s₁.mem (s₁.gpr .x1) (s₁.gpr .x2)).2 = (result I s₂.mem (s₂.gpr .x1) (s₂.gpr .x2)).2

/-- A state satisfying the precondition, for a digest of `D` bytes. -/
def satState (D : Nat) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x8000 | _ => 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, 32⟩, ⟨0x3000, D⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x8000, 8192⟩]

end VG.Proof.Ecdsa.Rfc6979.AArch64
