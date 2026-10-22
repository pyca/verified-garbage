module

public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem

/-! # Compression's signature obligations on AArch64 -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64

def compressContract (C : Spec.Weierstrass.Curve) : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, C.len + 1⟩
    let pk : Region := ⟨s.gpr .x1, 2 * C.len + 1⟩
    let ws : Region := ⟨s.gpr .x2, 8192⟩
    s.rd = [pk] ∧ s.wr = [out, ws] ∧
      pk.Disjoint out ∧ pk.Disjoint ws ∧ out.Disjoint ws ∧
      (s.gpr .x0).toNat + C.len + 1 ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match Spec.EcKey.compressPublicKey C (Spec.EcKey.bytesAt s.mem (s.gpr .x1) (2 * C.len + 1)) with
    | some bs => (s'.gpr .x0).setWidth 32 = 1 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .x0) (C.len + 1) = bs
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .x0) (C.len + 1) = List.replicate (C.len + 1) 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧
    s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2

theorem compress_implies (I : Spec.EcKey.Instance)
    (hsat : ∃ s, (I.compressPublicKeyContract abi 0).pre s) :
    (compressContract I.curve).Implies (I.compressPublicKeyContract abi 0) where
  pre := by
    sig_implies_pre [Spec.EcKey.Instance.compressPublicKeyContract,
      Spec.EcKey.Instance.compressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, compressContract]
  post := by
    intro s s' _ h
    sig_post [Spec.EcKey.Instance.compressPublicKeyContract,
      Spec.EcKey.Instance.compressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, compressContract]
    exact h
  pub := by
    sig_implies_pub [Spec.EcKey.Instance.compressPublicKeyContract,
      Spec.EcKey.Instance.compressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, compressContract]
  sat := hsat

def satState (len : Nat) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x8000 | _ => 0
  sp := 0x20000
  c := false
  mem _ := 0
  rd := [⟨0x2000, 2 * len + 1⟩]
  wr := [⟨0x1000, len + 1⟩, ⟨0x8000, 8192⟩]

end VG.Proof.EcKey.Compressed.AArch64
