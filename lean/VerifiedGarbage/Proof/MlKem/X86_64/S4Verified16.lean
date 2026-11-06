module
public import VerifiedGarbage.Proof.MlKem.X86_64.S4Base

import VerifiedGarbage.Proof.MlKem.X86_64.S4CT
import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
import VerifiedGarbage.Proof.MlKem.Bits
import VerifiedGarbage.Proof.MlKem.X86_64.FragCall

/-!
# ML-KEM on x86-64: `vg_mlkem16_sample_ntt4`, verified

The code of `vg_mlkem_sample_ntt4_avx2` and `_avx512` with 16-bit stores
(`w16 := true`), whose proofs are theirs for either width (`S4.correct`,
`S4.ct`); `sample4KW true` implies the shared contract of `Spec/`.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64

theorem pBytes_true : Impl.MlKem.X86_64.Sample4.pBytes true = 512 := rfl

end VG.Proof.MlKem.X86_64
