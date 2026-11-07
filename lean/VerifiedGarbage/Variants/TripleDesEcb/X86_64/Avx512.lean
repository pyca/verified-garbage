module

public import VerifiedGarbage.Proof.TripleDes.X86_64.Batch.Call

/-! # `vg_triple_des_ecb_encrypt` and `vg_triple_des_ecb_decrypt` on x86-64: AVX-512 -/

@[expose] public section

namespace VG.Variants.TripleDesEcb.X86_64.Avx512

def variant : Proof.TripleDes.X86_64.Batch.EcbImpl := Proof.TripleDes.X86_64.Batch.avx512

end VG.Variants.TripleDesEcb.X86_64.Avx512
