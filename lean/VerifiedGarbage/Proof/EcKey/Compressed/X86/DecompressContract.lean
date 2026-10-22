module

public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.Contract
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.EcKey.Compressed.Decode
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Ecdh.X86.Main
public import VerifiedGarbage.Impl.EcKey.Compressed
public import VerifiedGarbage.Proof.EcKey.Compressed.Root

/-! # Decompression's signature obligations on 32-bit x86 -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86

def decompressContract (C : Spec.Weierstrass.Curve)
    (root : Spec.Weierstrass.Fe C → Spec.Weierstrass.Fe C) (wide : Bool := false) : Contract isa where
  pre := codecPre (C.len + 1) (2 * C.len + 1) wide
  post s s' :=
    match Impl.EcKey.Compressed.decode C root (Spec.EcKey.bytesAt s.mem ((arg s 1).setWidth 64) (C.len + 1)) with
    | some Q => (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 = 1 ∧
        Spec.EcKey.bytesAt s'.mem ((arg s 0).setWidth 64) (2 * C.len + 1) = Spec.EcKey.encodePoint Q
    | none => (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 = 0 ∧
        Spec.EcKey.bytesAt s'.mem ((arg s 0).setWidth 64) (2 * C.len + 1) = List.replicate (2 * C.len + 1) 0
  pub s t := s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧ arg s 2 = arg t 2

theorem decompress_implies (I : Spec.EcKey.Instance)
    (root : Spec.Weierstrass.Fe I.curve → Spec.Weierstrass.Fe I.curve)
    (hf : RootFacts root)
    (hsat : ∃ s, (I.decompressPublicKeyContract abi 28).pre s) :
    (decompressContract I.curve root true).Implies (I.decompressPublicKeyContract abi 28) where
  pre := by
    sig_implies_pre [Spec.EcKey.Instance.decompressPublicKeyContract,
      Spec.EcKey.Instance.decompressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argSlots, argVal, argBytes, stackBelow, decompressContract, codecPre]
  post := by
    intro s s' _ h
    sig_post [Spec.EcKey.Instance.decompressPublicKeyContract,
      Spec.EcKey.Instance.decompressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argSlots, argVal, argBytes, stackBelow, decompressContract, codecPre]
    cases he : Impl.EcKey.Compressed.decode I.curve root
        (Spec.EcKey.bytesAt s.mem ((arg s 1).setWidth 64) (I.curve.len + 1)) with
    | none =>
      simp only [decompressContract, he] at h
      exact Or.inr ⟨h.1, (decode_none_iff hf _).mp he, h.2⟩
    | some Q =>
      simp only [decompressContract, he] at h
      exact Or.inl ⟨h.1, Q, decode_sound he, h.2⟩
  pub := by
    sig_implies_pub [Spec.EcKey.Instance.decompressPublicKeyContract,
      Spec.EcKey.Instance.decompressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argSlots, argVal, argBytes, stackBelow, decompressContract, codecPre]
  sat := hsat

def decompressSatState (len : Nat) : State := satState (len + 1) (2 * len + 1)

end VG.Proof.EcKey.Compressed.X86
