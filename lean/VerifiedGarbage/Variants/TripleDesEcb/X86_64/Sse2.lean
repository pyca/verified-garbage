module

public import VerifiedGarbage.Proof.TripleDes.X86_64.Batch.Call

/-! # `vg_triple_des_ecb_encrypt` and `vg_triple_des_ecb_decrypt` on x86-64: in the baseline ISA -/

@[expose] public section

namespace VG.Variants.TripleDesEcb.X86_64.Sse2

def variant : Proof.TripleDes.X86_64.Batch.EcbImpl := Proof.TripleDes.X86_64.Batch.sse

end VG.Variants.TripleDesEcb.X86_64.Sse2
