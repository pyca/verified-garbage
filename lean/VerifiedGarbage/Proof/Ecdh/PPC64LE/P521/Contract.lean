module

public import VerifiedGarbage.Spec.EcKey.Generic
public import VerifiedGarbage.Spec.Ecdh
public import VerifiedGarbage.Spec.P521
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Proof.Framework.PowLit

/-!
# ECDH over P-521 on PPC64LE: the contract the proof is written against

The facts of `Spec.Ecdh.Instance.exchangeContract` for P-521 on PPC64LE, by
name: `vg_ecdh_p521(out, d, peer, scratch)`, with the arguments in `r3`–`r6`
and the result in `r3` (ELFv2).
-/

@[expose] public section

namespace VG.Proof.Ecdh.PPC64LE.P521

open VG VG.PPC64LE Spec.Weierstrass Spec.EcKey

/-- The shared secret of the private key at `d` and the public key at
`peer`, as the specification computes it. -/
abbrev ex (m : Mem) (d peer : Addr) : Option (List Byte) :=
  Spec.Ecdh.exchange Spec.P521.curve (ofBytes (bytesAt m d 66)) (bytesAt m peer 133)

def ecdhPPC : Contract PPC64LE.isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 66⟩
    let d : Region := ⟨s.gpr .r4, 66⟩
    let peer : Region := ⟨s.gpr .r5, 133⟩
    let scratch : Region := ⟨s.gpr .r6, 8192⟩
    s.rd = [d, peer] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ d.Disjoint scratch ∧
      peer.Disjoint scratch ∧ (s.gpr .r3).toNat + 66 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + 66 ≤ 2 ^ 64 ∧
      (s.gpr .r5).toNat + 133 ≤ 2 ^ 64 ∧ (s.gpr .r6).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match ex s.mem (s.gpr .r4) (s.gpr .r5) with
    | some z => s'.gpr .r3 = 1 ∧ bytesAt s'.mem (s.gpr .r3) 66 = z
    | none => s'.gpr .r3 = 0 ∧ bytesAt s'.mem (s.gpr .r3) 66 = List.replicate 66 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
    s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.gpr .r6 = s₂.gpr .r6

end VG.Proof.Ecdh.PPC64LE.P521
