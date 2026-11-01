module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Spec.Secp256k1
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Ecdsa.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# ECDSA over secp256k1 on x86 (32-bit): the contract the proof is written against

The facts of `Proof.Ecdsa.Instance.signContract Spec.Ecdsa.Secp256k1.inst` for x86, by name:
`vg_ecdsa_secp256k1_sign(out, d, digest, k, scratch)`, whose arguments are on
the stack (cdecl), the result in `eax`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86.Secp256k1

open VG VG.X86 Spec.Weierstrass Spec.Ecdsa

/-- The signature of the arguments, as the specification computes it. -/
abbrev sig (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  signWith Spec.Secp256k1.curve (ofBytes (bytesAt m d 32)) (hashToInt Spec.Secp256k1.curve (bytesAt m digest 32))
    (ofBytes (bytesAt m k 32))

def signX86 : Contract X86.isa where
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 64⟩
    let d : Region := ⟨(arg s 1).setWidth 64, 32⟩
    let digest : Region := ⟨(arg s 2).setWidth 64, 32⟩
    let k : Region := ⟨(arg s 3).setWidth 64, 32⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 28, 28⟩
    s.rd = [d, digest, k, args] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint k ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ k.Disjoint scratch ∧
      args.Disjoint out ∧ args.Disjoint scratch ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 4).toNat + 8192 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧
      28 ≤ (s.gpr .esp).toNat ∧ stack.Disjoint out ∧ stack.Disjoint scratch
  post s s' :=
    match sig s.mem ((arg s 1).setWidth 64) ((arg s 2).setWidth 64) ((arg s 3).setWidth 64) with
    | some rs => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 1 ∧
      bytesAt s'.mem ((arg s 0).setWidth 64) 64 = encode Spec.Secp256k1.curve rs
    | none => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 0 ∧
      bytesAt s'.mem ((arg s 0).setWidth 64) 64 = List.replicate 64 0
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧
    arg s₁ 2 = arg s₂ 2 ∧ arg s₁ 3 = arg s₂ 3 ∧ arg s₁ 4 = arg s₂ 4

end VG.Proof.Ecdsa.X86.Secp256k1
