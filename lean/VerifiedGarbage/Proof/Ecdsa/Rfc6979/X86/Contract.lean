import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Generic
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Deterministic ECDSA on x86 (32-bit): the contract the proof is written against

The facts of `I.signContract` for an instance `I` of a curve of `len`-byte
scalars with a hash of `I.hashLen` bytes, for x86 and 272 bytes of stack, by
name: `vg_ecdsa_<curve>_<hash>_sign(out, d, digest, scratch)`, whose arguments are
on the stack (cdecl), the result in `eax`. Its arguments' slots are
readable here; the shared contract makes them writable
(`Verified.narrowTo`). Each instance's file shows `I.signContract` implies
it.
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 Spec.Weierstrass Spec.Ecdsa

/-- RFC 6979's signature of the arguments, and the number of candidates tried. -/
abbrev result (I : Spec.Ecdsa.Rfc6979.Instance) (m : Mem) (d digest : Addr) : Option (Nat × Nat) × Nat :=
  I.result m d digest

def rfcX86 (I : Spec.Ecdsa.Rfc6979.Instance) : Contract X86.isa where
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 2 * I.ecdsa.curve.len⟩
    let d : Region := ⟨(arg s 1).setWidth 64, I.ecdsa.curve.len⟩
    let digest : Region := ⟨(arg s 2).setWidth 64, I.hashLen⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 272, 272⟩
    272 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧
    s.rd = [d, digest, args] ∧ s.wr = [out, scratch] ∧
      out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint scratch ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧
      args.Disjoint out ∧ args.Disjoint scratch ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      stack.Disjoint out ∧ stack.Disjoint d ∧ stack.Disjoint digest ∧ stack.Disjoint scratch ∧
      (arg s 0).toNat + 2 * I.ecdsa.curve.len ≤ 2 ^ 32 ∧ (arg s 1).toNat + I.ecdsa.curve.len ≤ 2 ^ 32 ∧
      (arg s 2).toNat + I.hashLen ≤ 2 ^ 32 ∧ (arg s 3).toNat + 8192 ≤ 2 ^ 32
  post s s' :=
    match (result I s.mem ((arg s 1).setWidth 64) ((arg s 2).setWidth 64)).1 with
    | some rs => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 1 ∧
      bytesAt s'.mem ((arg s 0).setWidth 64) (2 * I.ecdsa.curve.len) = encode I.ecdsa.curve rs
    | none => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 0 ∧
      bytesAt s'.mem ((arg s 0).setWidth 64) (2 * I.ecdsa.curve.len) = List.replicate (2 * I.ecdsa.curve.len) 0
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧
    arg s₁ 2 = arg s₂ 2 ∧ arg s₁ 3 = arg s₂ 3 ∧
    (result I s₁.mem ((arg s₁ 1).setWidth 64) ((arg s₁ 2).setWidth 64)).2 =
      (result I s₂.mem ((arg s₂ 1).setWidth 64) ((arg s₂ 2).setWidth 64)).2

end VG.Proof.Ecdsa.Rfc6979.X86
