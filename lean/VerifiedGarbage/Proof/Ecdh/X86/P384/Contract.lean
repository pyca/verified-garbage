import VerifiedGarbage.Spec.Ecdh.P384
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ECDH over P-384 on x86 (32-bit): the contract the proof is written against

The facts of `Spec.Ecdh.P384.inst.exchangeContract` for x86, by name:
`vg_ecdh_p384(out, d, peer, scratch)`, whose arguments are on the stack
(cdecl), the result in `eax`. Its arguments' slots are readable here; the
shared contract makes them writable (`Verified.narrowTo`).
-/

namespace VG.Proof.Ecdh.X86.P384

open VG VG.X86 Spec.Weierstrass Spec.EcKey

/-- The shared secret of the private key at `d` and the public key at
`peer`, as the specification computes it. -/
abbrev ex (m : Mem) (d peer : Addr) : Option (List Byte) :=
  Spec.Ecdh.exchange Spec.P384.curve (ofBytes (bytesAt m d 48)) (bytesAt m peer 97)

def ecdhX86 : Contract X86.isa where
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 48⟩
    let d : Region := ⟨(arg s 1).setWidth 64, 48⟩
    let peer : Region := ⟨(arg s 2).setWidth 64, 97⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 20, 20⟩
    s.rd = [d, peer, args] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ out.Disjoint d ∧
      out.Disjoint peer ∧ d.Disjoint scratch ∧ peer.Disjoint scratch ∧
      args.Disjoint out ∧ args.Disjoint scratch ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 48 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 48 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 97 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 8192 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧
      20 ≤ (s.gpr .esp).toNat ∧ stack.Disjoint out ∧ stack.Disjoint scratch
  post s s' :=
    match ex s.mem ((arg s 1).setWidth 64) ((arg s 2).setWidth 64) with
    | some z => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 1 ∧
      bytesAt s'.mem ((arg s 0).setWidth 64) 48 = z
    | none => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 0 ∧
      bytesAt s'.mem ((arg s 0).setWidth 64) 48 = List.replicate 48 0
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧
    arg s₁ 2 = arg s₂ 2 ∧ arg s₁ 3 = arg s₂ 3

end VG.Proof.Ecdh.X86.P384
