module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Subgroup
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.NativeSearch
import VerifiedGarbage.Proof.Framework.Omega

/-! # Hash implementations shared by the complete parameter-generation phases -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.Proof.Pbkdf2.Md.AArch64

structure GenerationHashes where
  sha1 : Impl.Pbkdf2.Md.AArch64.Hash
  sha256 : Impl.Pbkdf2.Md.AArch64.Hash
  h1 : Calls.StreamOK sha1.stream
  h256 : Calls.StreamOK sha256.stream
  hash1 : ∀ x, Spec.Mgf1.sha1.hash x = h1.SH.H.hash x
  hash256 : ∀ x, Spec.Mgf1.sha256.hash x = h256.SH.H.hash x
  size1 : ∀ x, (Spec.Mgf1.sha1.hash x).length = sha1.D
  size256 : ∀ x, (Spec.Mgf1.sha256.hash x).length = sha256.D
  width1 : sha1.D = 20
  width256 : sha256.D = 32

end VG.Proof.Dsa.AArch64.Generation
