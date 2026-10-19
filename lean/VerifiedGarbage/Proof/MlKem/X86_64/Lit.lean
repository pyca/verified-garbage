module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.MlKem.X86_64.KpkeMul
meta import VerifiedGarbage.Impl.MlKem.X86_64.KpkeMul
public import VerifiedGarbage.Impl.MlKem.X86_64.Frag
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Lit
meta import VerifiedGarbage.Impl.MlKem.X86_64.Frag

/-!
# ML-KEM's polynomial arithmetic on x86-64: the code as literals

Untrusted: everything here is checked by Lean. The kernel checks each literal
once; the checks of every instruction of `vg_mlkem*_decrypt_mul`,
`vg_mlkem*_encrypt_mul` (which inline the backends' `Bodies`) and of the
functions `ArithOk` is about read them (`lit_decide`) rather than building
the code again.
-/

@[expose] public section

namespace VG

materialize_code Impl.MlKem.X86_64.nttOB
materialize_code Impl.MlKem.X86_64.nttInvB
materialize_code Impl.MlKem.X86_64.mulB
materialize_code Impl.MlKem.X86_64.add
materialize_code Impl.MlKem.X86_64.zeroB
materialize_code Impl.MlKem.X86_64.nttOBY
materialize_code Impl.MlKem.X86_64.nttInvAccY
materialize_code Impl.MlKem.X86_64.KpkeMul.nttAccY
materialize_code Impl.MlKem.X86_64.mulAccY
materialize_code Impl.MlKem.X86_64.mulSetY
materialize_code Impl.MlKem.X86_64.zeroAccY
materialize_code Impl.MlKem.X86_64.addAvx2
materialize_code Impl.MlKem.X86_64.multiplyNTTs
materialize_code Impl.MlKem.X86_64.ntt
materialize_code Impl.MlKem.X86_64.nttInv
materialize_code Impl.MlKem.X86_64.sub
materialize_code Impl.MlKem.X86_64.cbd2
materialize_code Impl.MlKem.X86_64.decode12
materialize_code Impl.MlKem.X86_64.subAvx2
materialize_code Impl.MlKem.X86_64.decode12Avx2
materialize_code Impl.MlKem.X86_64.encode12
materialize_code Impl.MlKem.X86_64.encode12Avx2

end VG
