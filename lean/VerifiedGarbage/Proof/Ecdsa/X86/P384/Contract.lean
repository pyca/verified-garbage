import VerifiedGarbage.Spec.Ecdsa.P384
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ECDSA over P-384 on x86 (32-bit): the contract the proof is written against

The facts of `Spec.Ecdsa.P384.inst.signContract` for x86, by name:
`vg_ecdsa_p384_sign(out, d, digest, k, scratch)`, whose arguments are on
the stack (cdecl), the result in `eax`.
-/

namespace VG.Proof.Ecdsa.X86.P384

open VG VG.X86 Spec.Weierstrass Spec.Ecdsa

/-- The signature of the arguments, as the specification computes it. -/
abbrev sig (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  signWith Spec.P384.curve (ofBytes (bytesAt m d 48)) (hashToInt Spec.P384.curve (bytesAt m digest 48))
    (ofBytes (bytesAt m k 48))

def signX86 : Contract X86.isa where
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 96⟩
    let d : Region := ⟨(arg s 1).setWidth 64, 48⟩
    let digest : Region := ⟨(arg s 2).setWidth 64, 48⟩
    let k : Region := ⟨(arg s 3).setWidth 64, 48⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [d, digest, k, args] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint k ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ k.Disjoint scratch ∧
      args.Disjoint out ∧ args.Disjoint scratch ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 96 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 48 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 48 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 48 ≤ 2 ^ 32 ∧ (arg s 4).toNat + 8192 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post s s' :=
    match sig s.mem ((arg s 1).setWidth 64) ((arg s 2).setWidth 64) ((arg s 3).setWidth 64) with
    | some rs => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 1 ∧
      bytesAt s'.mem ((arg s 0).setWidth 64) 96 = encode Spec.P384.curve rs
    | none => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 0 ∧
      bytesAt s'.mem ((arg s 0).setWidth 64) 96 = List.replicate 96 0
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧
    arg s₁ 2 = arg s₂ 2 ∧ arg s₁ 3 = arg s₂ 3 ∧ arg s₁ 4 = arg s₂ 4

end VG.Proof.Ecdsa.X86.P384
