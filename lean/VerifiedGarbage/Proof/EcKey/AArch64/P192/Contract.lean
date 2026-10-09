import VerifiedGarbage.Spec.EcKey.P192
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.Contract

/-!
# p192 public keys on AArch64: the contract the proof is written against

The facts of `Spec.EcKey.P192.inst.publicKeyContract` for AArch64, by name:
`vg_ec_p192_public_key(out = x0, d = x1, scratch = x2)`, the result in `w0`.
-/

namespace VG.Proof.EcKey.AArch64.P192

open VG VG.AArch64 Spec.Weierstrass Spec.EcKey

/-- The public key of the private key at `d`, as the specification computes it. -/
abbrev pk (m : Mem) (d : Addr) : Option (Point Spec.P192.curve) :=
  publicKey Spec.P192.curve (ofBytes (bytesAt m d 24))

def pkAArch64 : Contract AArch64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 49⟩
    let d : Region := ⟨s.gpr .x1, 24⟩
    let scratch : Region := ⟨s.gpr .x2, 8192⟩
    s.rd = [d] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ out.Disjoint d ∧ d.Disjoint scratch ∧
      (s.gpr .x0).toNat + 49 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match pk s.mem (s.gpr .x1) with
    | some (.affine x y) => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x0) 49 = encodePoint (.affine x y)
    | _ => (s'.gpr .x0).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .x0) 49 = List.replicate 49 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.sp = s₂.sp

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x8000 | _ => 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, 24⟩]
  wr := [⟨0x1000, 49⟩, ⟨0x8000, 8192⟩]

theorem implies : pkAArch64.Implies (Spec.EcKey.P192.inst.publicKeyContract AArch64.abi) := by
  exact
    { pre := by
        sig_implies_pre [Spec.EcKey.P192.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P192.curve, Spec.EcKey.scratchWords, AArch64.abi,
          AArch64.argRegs, pkAArch64, pk]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.P192.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P192.curve, Spec.EcKey.scratchWords, AArch64.abi,
          AArch64.argRegs, pkAArch64, pk]
        simp only [pkAArch64, pk, Spec.P192.curve] at h
        revert h
        generalize publicKey _ _ = q
        rcases q with _ | _ | ⟨x, y⟩ <;> exact id
      pub := by
        sig_implies_pub [Spec.EcKey.P192.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P192.curve, Spec.EcKey.scratchWords, AArch64.abi,
          AArch64.argRegs, pkAArch64, pk]
      sat := by
        sig_implies_sat [Spec.EcKey.P192.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P192.curve, Spec.EcKey.scratchWords, AArch64.abi,
          AArch64.argRegs, satState] [satState] using satState }

end VG.Proof.EcKey.AArch64.P192
