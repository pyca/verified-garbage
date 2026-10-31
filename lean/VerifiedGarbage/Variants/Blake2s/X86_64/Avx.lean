module

public import VerifiedGarbage.Proof.Variants.Blake2s.X86_64.Avx

/-! # BLAKE2s on x86-64 with AVX -/

@[expose] public section

namespace VG.Variants.Blake2s.X86_64.Avx

def variant : Proof.Blake2.X86_64.BackendS := Proof.Variants.Blake2s.X86_64.Avx.variant

end VG.Variants.Blake2s.X86_64.Avx
