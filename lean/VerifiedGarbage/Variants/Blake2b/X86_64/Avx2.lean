module

public import VerifiedGarbage.Proof.Variants.Blake2b.X86_64.Avx2

/-! # BLAKE2b on x86-64 with AVX2 -/

@[expose] public section

namespace VG.Variants.Blake2b.X86_64.Avx2

def variant : Proof.Blake2.X86_64.Backend := Proof.Variants.Blake2b.X86_64.Avx2.variant

end VG.Variants.Blake2b.X86_64.Avx2
