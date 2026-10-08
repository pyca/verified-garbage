import VerifiedGarbage.Spec.EcKey.P384
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Contract

/-!
# P-384 public keys on x86 (32-bit): the contract the proof is written against

The facts of `Spec.EcKey.P384.inst.publicKeyContract` for x86, by name:
`vg_ec_p384_public_key(out, d, scratch)`, whose arguments are on the stack
(cdecl), the result in `eax`. Its arguments' slots are readable here; the
shared contract makes them writable (`Verified.narrowTo`).
-/

namespace VG.Proof.EcKey.X86.P384

open VG VG.X86 Spec.Weierstrass Spec.EcKey

/-- The public key of the private key at `d`, as the specification computes it. -/
abbrev pk (m : Mem) (d : Addr) : Option (Point Spec.P384.curve) :=
  publicKey Spec.P384.curve (ofBytes (bytesAt m d 48))

def pkX86 : Contract X86.isa where
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 97⟩
    let d : Region := ⟨(arg s 1).setWidth 64, 48⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 20, 20⟩
    s.rd = [d, args] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ out.Disjoint d ∧ d.Disjoint scratch ∧
      args.Disjoint out ∧ args.Disjoint scratch ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 97 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 48 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 8192 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 16 ≤ 2 ^ 32 ∧
      20 ≤ (s.gpr .esp).toNat ∧ stack.Disjoint out ∧ stack.Disjoint scratch
  post s s' :=
    match pk s.mem ((arg s 1).setWidth 64) with
    | some (.affine x y) => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 1 ∧
      bytesAt s'.mem ((arg s 0).setWidth 64) 97 = encodePoint (.affine x y)
    | _ => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 0 ∧
      bytesAt s'.mem ((arg s 0).setWidth 64) 97 = List.replicate 97 0
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧ arg s₁ 2 = arg s₂ 2

end VG.Proof.EcKey.X86.P384
