module

public import VerifiedGarbage.Proof.Argon2.X86_64.Avx512.Compress
public import VerifiedGarbage.Proof.Argon2.X86_64.Avx2.Compress
public import VerifiedGarbage.Proof.Argon2.X86_64.Compress
import VerifiedGarbage.Proof.Argon2.X86_64.Avx2.Lit
import VerifiedGarbage.Proof.Argon2.X86_64.Avx512.Lit
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Argon2 compression on x86-64

Registration for the scalar compression primitive. The API and contract
come from the reviewed specification; the code and proof are untrusted.
-/

@[expose] public section

namespace VG.Artifacts.Argon2.X86_64

def artifacts : List Artifact := [
  Spec.Argon2.compressApi.artifact X86_64.target {
    code := Impl.Argon2.X86_64.compress
    stack := 0
    verified := Proof.Argon2.X86_64.compress_verified },
  Spec.Argon2.compressApi.artifact X86_64.target {
    suffix := "_avx2"
    code := Impl.Argon2.X86_64.Avx2.compress
    stack := 0
    verified := Proof.Argon2.X86_64.Avx2.compress_verified
    features := ["avx", "avx2"] },
  Spec.Argon2.compressApi.artifact X86_64.target {
    suffix := "_avx512"
    code := Impl.Argon2.X86_64.Avx512.compress
    stack := 0
    verified := Proof.Argon2.X86_64.Avx512.compress_verified
    features := ["avx", "avx512f"] }]

end VG.Artifacts.Argon2.X86_64
