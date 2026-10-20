module

public import VerifiedGarbage.Proof.Variants.Blake2s.X86_64.Avx

/-!
# BLAKE2s on x86-64 with AVX

A variant of `Blake2s` on x86-64 (see `TCB/Emit.lean`):
`vg_blake2s_compress_avx`, the work vector in four 128-bit registers, whose
`VEX.128` instructions need AVX alone; the streaming functions calling it
need it too.
-/

@[expose] public section

namespace VG.Variants.Blake2s.X86_64.Avx

def variant : Proof.Blake2.X86_64.BackendS := Proof.Variants.Blake2s.X86_64.Avx.variant

end VG.Variants.Blake2s.X86_64.Avx
