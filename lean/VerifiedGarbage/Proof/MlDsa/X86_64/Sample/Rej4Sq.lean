module
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlKem.X86_64.S4Base
import VerifiedGarbage.Proof.MlKem.X86_64.S4SqT


/-!
# ML-DSA on x86-64: `vg_mldsa_rej_ntt_poly4_avx2`, squeezing

`vg_mldsa_rej_ntt_poly4_avx2` absorbs the seeds and squeezes three blocks of
each as `vg_mlkem_sample_ntt4_avx2` does (`Proof/MlKem/X86_64/S4*.lean`, whose
precondition, layout and invariants it shares), then three more to the same
buffers, as `vg_mlkem_sample_ntt4_avx2` squeezes two more when it needs them
(`SqT`, `S4SqT.lean`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Rej4

export VG.Proof.MlKem.X86_64.S4 (SqT sqT_of lowR permT_ok EXT extT_step extractT_ok sqT_ok sqTs_ok)

end VG.Proof.MlDsa.X86_64.Rej4
