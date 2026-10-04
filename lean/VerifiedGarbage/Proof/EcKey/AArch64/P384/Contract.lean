import VerifiedGarbage.Spec.EcKey.P384
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.Contract

/-!
# P-384 public keys on AArch64: the contract the proof is written against

The facts of `Spec.EcKey.P384.inst.publicKeyContract` for AArch64, by name:
`vg_ec_p384_public_key(out = x0, d = x1, scratch = x2)`, the result in `w0`.
-/

namespace VG.Proof.EcKey.AArch64.P384

open VG VG.AArch64 Spec.Weierstrass Spec.EcKey

/-- The public key of the private key at `d`, as the specification computes it. -/
abbrev pk (m : Mem) (d : Addr) : Option (Point Spec.P384.curve) :=
  publicKey Spec.P384.curve (ofBytes (bytesAt m d 48))

def pkAArch64 : Contract AArch64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 97⟩
    let d : Region := ⟨s.gpr .x1, 48⟩
    let scratch : Region := ⟨s.gpr .x2, 8192⟩
    s.rd = [d] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ out.Disjoint d ∧ d.Disjoint scratch ∧
      (s.gpr .x0).toNat + 97 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match pk s.mem (s.gpr .x1) with
    | some (.affine x y) => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x0) 97 = encodePoint (.affine x y)
    | _ => (s'.gpr .x0).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .x0) 97 = List.replicate 97 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.sp = s₂.sp

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x8000 | _ => 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, 48⟩]
  wr := [⟨0x1000, 97⟩, ⟨0x8000, 8192⟩]

theorem implies : pkAArch64.Implies (Spec.EcKey.P384.inst.publicKeyContract AArch64.abi) := by
  exact
    { pre := by
        sig_implies_pre [Spec.EcKey.P384.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P384.curve, Spec.EcKey.scratchWords, AArch64.abi,
          AArch64.argRegs, pkAArch64, pk]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.P384.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P384.curve, Spec.EcKey.scratchWords, AArch64.abi,
          AArch64.argRegs, pkAArch64, pk]
        simp only [pkAArch64, pk, Spec.P384.curve] at h
        revert h
        generalize publicKey _ _ = q
        rcases q with _ | _ | ⟨x, y⟩ <;> exact id
      pub := by
        sig_implies_pub [Spec.EcKey.P384.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P384.curve, Spec.EcKey.scratchWords, AArch64.abi,
          AArch64.argRegs, pkAArch64, pk]
      sat := by
        sig_implies_sat [Spec.EcKey.P384.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P384.curve, Spec.EcKey.scratchWords, AArch64.abi,
          AArch64.argRegs, satState] [satState] using satState }

end VG.Proof.EcKey.AArch64.P384
