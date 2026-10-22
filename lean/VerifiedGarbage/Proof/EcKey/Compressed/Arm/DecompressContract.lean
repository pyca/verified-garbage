module

public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.EcKey.Compressed.Decode
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Ecdh.Arm.Main
public import VerifiedGarbage.Impl.EcKey.Compressed
public import VerifiedGarbage.Proof.EcKey.Compressed.Root

/-! # Decompression's signature obligations on ARMv7 -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm

open VG VG.Arm

def decompressContract (C : Spec.Weierstrass.Curve)
    (root : Spec.Weierstrass.Fe C → Spec.Weierstrass.Fe C) : Contract isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 2 * C.len + 1⟩
    let pk : Region := ⟨State.addr (s.gpr .r1), C.len + 1⟩
    let ws : Region := ⟨State.addr (s.gpr .r2), 8192⟩
    s.rd = [pk] ∧ s.wr = [out, ws] ∧
      pk.Disjoint out ∧ pk.Disjoint ws ∧ out.Disjoint ws ∧
      (s.gpr .r0).toNat + 2 * C.len + 1 ≤ 2 ^ 32 ∧
      (s.gpr .r1).toNat + C.len + 1 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 8192 ≤ 2 ^ 32
  post s s' :=
    match Impl.EcKey.Compressed.decode C root (Spec.EcKey.bytesAt s.mem (State.addr (s.gpr .r1)) (C.len + 1)) with
    | some Q => (s'.gpr .r1 ++ s'.gpr .r0).setWidth 32 = 1 ∧
        Spec.EcKey.bytesAt s'.mem (State.addr (s.gpr .r0)) (2 * C.len + 1) = Spec.EcKey.encodePoint Q
    | none => (s'.gpr .r1 ++ s'.gpr .r0).setWidth 32 = 0 ∧
        Spec.EcKey.bytesAt s'.mem (State.addr (s.gpr .r0)) (2 * C.len + 1) = List.replicate (2 * C.len + 1) 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧
    s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2

theorem decompress_implies (I : Spec.EcKey.Instance)
    (root : Spec.Weierstrass.Fe I.curve → Spec.Weierstrass.Fe I.curve)
    (hf : RootFacts root)
    (hsat : ∃ s, (I.decompressPublicKeyContract abi 0).pre s) :
    (decompressContract I.curve root).Implies (I.decompressPublicKeyContract abi 0) where
  pre := by
    sig_implies_pre [Spec.EcKey.Instance.decompressPublicKeyContract,
      Spec.EcKey.Instance.decompressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, reduceClassify, Loc.val, State.addr, decompressContract]
  post := by
    intro s s' _ h
    sig_post [Spec.EcKey.Instance.decompressPublicKeyContract,
      Spec.EcKey.Instance.decompressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, reduceClassify, Loc.val, State.addr, decompressContract]
    cases he : Impl.EcKey.Compressed.decode I.curve root
        (Spec.EcKey.bytesAt s.mem (State.addr (s.gpr .r1)) (I.curve.len + 1)) with
    | none =>
      simp only [decompressContract, he] at h
      exact Or.inr ⟨h.1, (decode_none_iff hf _).mp he, h.2⟩
    | some Q =>
      simp only [decompressContract, he] at h
      exact Or.inl ⟨h.1, Q, decode_sound he, h.2⟩
  pub := by
    sig_implies_pub [Spec.EcKey.Instance.decompressPublicKeyContract,
      Spec.EcKey.Instance.decompressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, reduceClassify, Loc.val, State.addr, decompressContract]
  sat := hsat

def decompressSatState (len : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x8000 | _ => 0
  sp := 0x20000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, len + 1⟩]
  wr := [⟨0x1000, 2 * len + 1⟩, ⟨0x8000, 8192⟩]

end VG.Proof.EcKey.Compressed.Arm
