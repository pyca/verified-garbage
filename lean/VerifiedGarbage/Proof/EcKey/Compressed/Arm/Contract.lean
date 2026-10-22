module

public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem

/-! # Compression's signature obligations on ARMv7 -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm

open VG VG.Arm

def compressContract (C : Spec.Weierstrass.Curve) : Contract isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), C.len + 1⟩
    let pk : Region := ⟨State.addr (s.gpr .r1), 2 * C.len + 1⟩
    let ws : Region := ⟨State.addr (s.gpr .r2), 8192⟩
    s.rd = [pk] ∧ s.wr = [out, ws] ∧
      pk.Disjoint out ∧ pk.Disjoint ws ∧ out.Disjoint ws ∧
      (s.gpr .r0).toNat + C.len + 1 ≤ 2 ^ 32 ∧
      (s.gpr .r1).toNat + 2 * C.len + 1 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 8192 ≤ 2 ^ 32
  post s s' :=
    match Spec.EcKey.compressPublicKey C (Spec.EcKey.bytesAt s.mem (State.addr (s.gpr .r1)) (2 * C.len + 1)) with
    | some bs => (s'.gpr .r1 ++ s'.gpr .r0).setWidth 32 = 1 ∧
        Spec.EcKey.bytesAt s'.mem (State.addr (s.gpr .r0)) (C.len + 1) = bs
    | none => (s'.gpr .r1 ++ s'.gpr .r0).setWidth 32 = 0 ∧
        Spec.EcKey.bytesAt s'.mem (State.addr (s.gpr .r0)) (C.len + 1) = List.replicate (C.len + 1) 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧
    s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2

theorem compress_implies (I : Spec.EcKey.Instance)
    (hsat : ∃ s, (I.compressPublicKeyContract abi 0).pre s) :
    (compressContract I.curve).Implies (I.compressPublicKeyContract abi 0) where
  pre := by
    sig_implies_pre [Spec.EcKey.Instance.compressPublicKeyContract,
      Spec.EcKey.Instance.compressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, reduceClassify, Loc.val, State.addr, compressContract]
  post := by
    intro s s' _ h
    sig_post [Spec.EcKey.Instance.compressPublicKeyContract,
      Spec.EcKey.Instance.compressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, reduceClassify, Loc.val, State.addr, compressContract]
    exact h
  pub := by
    sig_implies_pub [Spec.EcKey.Instance.compressPublicKeyContract,
      Spec.EcKey.Instance.compressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, reduceClassify, Loc.val, State.addr, compressContract]
  sat := hsat

def satState (len : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x8000 | _ => 0
  sp := 0x20000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 2 * len + 1⟩]
  wr := [⟨0x1000, len + 1⟩, ⟨0x8000, 8192⟩]

end VG.Proof.EcKey.Compressed.Arm
