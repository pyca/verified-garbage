module

public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha256Avx2

/-! # SHA-256 on x86-64 with AVX2 and BMI -/

@[expose] public section

namespace VG.Variants.MdHash.X86_64.Sha256Avx2

open VG.Impl.Sha256.X86_64.Stream (Callee)

def variant : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha256Avx2.variant

end VG.Variants.MdHash.X86_64.Sha256Avx2
