module

public import VerifiedGarbage.Proof.TripleDes.X86_64.Batch.Call

/-! # `vg_triple_des_ecb_encrypt` and `vg_triple_des_ecb_decrypt` on x86-64: AVX2 -/

@[expose] public section

namespace VG.Variants.TripleDesEcb.X86_64.Avx2

def variant : Proof.TripleDes.X86_64.Batch.EcbImpl := Proof.TripleDes.X86_64.Batch.avx2

end VG.Variants.TripleDesEcb.X86_64.Avx2
