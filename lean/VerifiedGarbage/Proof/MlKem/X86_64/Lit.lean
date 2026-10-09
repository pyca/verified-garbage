import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.MlKem.X86_64.KpkeMul
import VerifiedGarbage.Impl.MlKem.X86_64.Frag

/-!
# ML-KEM's polynomial arithmetic on x86-64: the code as literals

Untrusted: everything here is checked by Lean. The kernel checks each literal
once; the checks of every instruction of `vg_mlkem*_decrypt_mul`,
`vg_mlkem*_encrypt_mul` (which inline the backends' `Bodies`) and of the
functions `ArithOk` is about read them (`lit_decide`) rather than building
the code again.
-/

namespace VG

materialize_code Impl.MlKem.X86_64.nttOB
materialize_code Impl.MlKem.X86_64.nttInvB
materialize_code Impl.MlKem.X86_64.mulB
materialize_code Impl.MlKem.X86_64.add
materialize_code Impl.MlKem.X86_64.nttOBY
materialize_code Impl.MlKem.X86_64.nttInvBY
materialize_code Impl.MlKem.X86_64.mulBY
materialize_code Impl.MlKem.X86_64.addAvx2
materialize_code Impl.MlKem.X86_64.multiplyNTTs
materialize_code Impl.MlKem.X86_64.ntt
materialize_code Impl.MlKem.X86_64.nttInv
materialize_code Impl.MlKem.X86_64.sub
materialize_code Impl.MlKem.X86_64.cbd2
materialize_code Impl.MlKem.X86_64.decode12
materialize_code Impl.MlKem.X86_64.multiplyNTTsAvx2
materialize_code Impl.MlKem.X86_64.nttAvx2
materialize_code Impl.MlKem.X86_64.nttInvAvx2
materialize_code Impl.MlKem.X86_64.subAvx2
materialize_code Impl.MlKem.X86_64.decode12Avx2

end VG
