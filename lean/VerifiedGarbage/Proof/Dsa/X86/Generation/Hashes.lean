module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.SeedHashTiming
public import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Sha1
public import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Sha256
public import VerifiedGarbage.Spec.Mgf1
import VerifiedGarbage.Proof.Sha1.Md
import VerifiedGarbage.Proof.Sha256.Md

/-! # DSA generation inherits every SHA-1 and SHA-256 streaming variant -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

structure GenerationHashes where
  sha1 : Hash
  sha256 : Hash
  ok1 : HashOK sha1
  ok256 : HashOK sha256
  hash1 : ∀ x, Spec.Mgf1.sha1.hash x = ok1.SH.H.hash x
  hash256 : ∀ x, Spec.Mgf1.sha256.hash x = ok256.SH.H.hash x
  size1 : ∀ x, (Spec.Mgf1.sha1.hash x).length = sha1.D
  size256 : ∀ x, (Spec.Mgf1.sha256.hash x).length = sha256.D
  width1 : sha1.D = 20
  width256 : sha256.D = 32

def generation_hashes (v1 : Sha1Stream) (v256 : Sha256Stream) : GenerationHashes where
  sha1 := sha1H v1
  sha256 := sha256H v256
  ok1 := sha1OK v1
  ok256 := sha256OK v256
  hash1 _ := rfl
  hash256 _ := rfl
  size1 x := by
    change (Spec.Sha1.hash x).length = 20
    change (VG.Proof.Sha1.md.hash Spec.Sha1.H0 x).length = 20
    exact VG.Proof.Sha1.md.digest_length _
  size256 x := by
    change (Spec.Sha256.hash x).length = 32
    change (VG.Proof.Sha256.md.hash Spec.Sha256.H0 x).length = 32
    exact VG.Proof.Sha256.md.digest_length _
  width1 := rfl
  width256 := rfl

end VG.Proof.Dsa.X86.Generation
