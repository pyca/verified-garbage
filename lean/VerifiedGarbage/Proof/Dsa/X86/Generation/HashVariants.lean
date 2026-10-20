module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Hashes
public import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Sha1
public import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Sha256
import VerifiedGarbage.Proof.Sha1.Md

/-! # Parameter generation follows every SHA-1 and SHA-256 streaming backend -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.Proof.Pbkdf2.Stream.X86

def generationHashes (v1 : Sha1Stream) (v256 : Sha256Stream) : GenerationHashes where
  sha1 := sha1H v1
  sha256 := sha256H v256
  h1 := sha1OK v1
  h256 := sha256OK v256
  width1 := rfl
  width256 := rfl
  final1 := rfl
  final256 := rfl
  hash1 _ := rfl
  hash256 _ := rfl
  size1 bs := by
    change (Spec.Sha1.hash bs).length = 20
    rw [Proof.Sha1.hash_eq]
    exact Proof.Sha1.md.digest_length _
  size256 bs := by
    change (Spec.Sha256.hash bs).length = 32
    rw [Proof.Sha256.hash_eq]
    exact Proof.Sha256.md.digest_length _
end VG.Proof.Dsa.X86.Generation
