import VerifiedGarbage.Spec.Ecdsa.Verify.P192
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ECDSA verification over P-192 on x86 (32-bit): the contract the proof is written against

The facts of `Spec.Ecdsa.P192.inst.verifyContract` for x86, by name:
`vg_ecdsa_p192_verify(public, digest, sig, scratch)`, whose arguments are on
the stack (cdecl), the result in `eax`. Its arguments' slots are readable
here; the shared contract makes them writable (`Verified.narrowTo`). Only
the pointers are public here: the proof shows that nothing else affects
timing, although the contract would let the contents of the three buffers.
-/

namespace VG.Proof.Ecdsa.Verify.X86.P192

open VG VG.X86 Spec.Weierstrass Spec.Ecdsa

/-- Whether the signature at `sig` of the hash at `digest` is valid for the
public key at `pk`, as the specification says. -/
abbrev vf (m : Mem) (pk digest sig : Addr) : Bool :=
  verify Spec.P192.curve (bytesAt m pk 49) (hashToInt Spec.P192.curve (bytesAt m digest 24)) (bytesAt m sig 48)

def verifyX86 : Contract X86.isa where
  pre s :=
    let pk : Region := ⟨(arg s 0).setWidth 64, 49⟩
    let digest : Region := ⟨(arg s 1).setWidth 64, 24⟩
    let sig : Region := ⟨(arg s 2).setWidth 64, 48⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 20, 20⟩
    s.rd = [pk, digest, sig, args] ∧ s.wr = [scratch] ∧ pk.Disjoint scratch ∧ digest.Disjoint scratch ∧
      sig.Disjoint scratch ∧ args.Disjoint scratch ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 49 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 24 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 48 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 8192 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧
      20 ≤ (s.gpr .esp).toNat ∧ stack.Disjoint scratch
  post s s' := BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) =
    if vf s.mem ((arg s 0).setWidth 64) ((arg s 1).setWidth 64) ((arg s 2).setWidth 64) then 1 else 0
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧
    arg s₁ 2 = arg s₂ 2 ∧ arg s₁ 3 = arg s₂ 3

end VG.Proof.Ecdsa.Verify.X86.P192
