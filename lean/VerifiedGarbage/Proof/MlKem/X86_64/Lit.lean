import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.MlKem.X86_64.KpkeMul

/-!
# ML-KEM on x86-64: the polynomial arithmetic's code as literals

The bodies of `NTT`, `NTT⁻¹` and the products of NTTs, for each backend, are
built by functions (their layers and loops), and every function of the
encryption and the decryption contains them: their literals
(`materialize_code`) spare the kernel building their instructions in every
check that evaluates them (`writesOnly`, `ctlOk`, `NoSp`, the stack's use,
constant time, `spSafe`).
-/

namespace VG.Impl.MlKem.X86_64

materialize_code nttOB
materialize_code nttInvB
materialize_code mulB
materialize_code nttOBY
materialize_code nttInvBY
materialize_code mulBY

end VG.Impl.MlKem.X86_64
