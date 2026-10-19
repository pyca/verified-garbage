module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptHashMemory
public import VerifiedGarbage.Spec.Hmac.Generic

/-! # Inner and outer SHA-256 representations for rejection-key HMACs -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

def macKey (key : List Byte) : List Byte := Spec.Hmac.blockKey Spec.Hmac.sha256 key

def MacRepr (g : Geometry) (key text : List Byte) (s : VG.X86.State) : Prop :=
  Spec.Sha256.Repr s.mem (g.scratch sSt 96).base (Spec.Hmac.xorPad (macKey key) Spec.Hmac.ipad ++ text) ∧
  Spec.Sha256.Repr s.mem (g.scratch sOuter 96).base (Spec.Hmac.xorPad (macKey key) Spec.Hmac.opad)

theorem macKey_length {key : List Byte} (bound : key.length ≤ 64) : (macKey key).length = 64 := by
  unfold macKey Spec.Hmac.blockKey
  rw [ite_eq_right (show ¬ Spec.Hmac.sha256.blockSize < key.length from Nat.not_lt.mpr bound)]
  simp only [List.length_append, List.length_replicate]
  change key.length + (64 - key.length) = 64
  omega

end VG.Proof.RsaPkcs1Enc.X86.Dec
