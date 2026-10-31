module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha512

/-! # SHA-384 on x86-64 with AVX2 and BMI -/

@[expose] public section

namespace VG.Variants.MdHash.X86_64.Sha384Avx2

def variant : Proof.Pbkdf2.Md.X86_64.MdHash :=
  Proof.Pbkdf2.Md.X86_64.Sha512.sha384 .avx2 (Proof.Pbkdf2.Md.X86_64.Sha512.stream384 .avx2)

end VG.Variants.MdHash.X86_64.Sha384Avx2
