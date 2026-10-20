module
public import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Hash
public import VerifiedGarbage.Spec.Dsa

/-! # Parameter generation is generic over the streaming SHA implementations -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.Impl.Pbkdf2.Stream.X86 VG.Proof.Pbkdf2.Stream.X86

structure GenerationHashes where
  sha1 : Hash
  sha256 : Hash
  h1 : HashOK sha1
  h256 : HashOK sha256
  width1 : sha1.D = 20
  width256 : sha256.D = 32
  final1 : sha1.F = 20
  final256 : sha256.F = 32
  hash1 : ∀ bs, h1.SH.H.hash bs = Spec.Dsa.seedHash 160 bs
  hash256 : ∀ bs, h256.SH.H.hash bs = Spec.Dsa.seedHash 256 bs
  size1 : ∀ bs, (Spec.Dsa.seedHash 160 bs).length = 20
  size256 : ∀ bs, (Spec.Dsa.seedHash 256 bs).length = 32
end VG.Proof.Dsa.X86.Generation
