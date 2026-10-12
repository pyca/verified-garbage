import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Ecdsa.Secp256k1.X86_64

/-!
# `vg_secp256k1_mul` on x86-64: the code, as literals

The function's code (`Cfg.mulFn`) and its body, as literals
(`materialize_code`), which `lit_decide` and `taint_decide` read rather than
building the code again.
-/

namespace VG.Proof.Ecdsa.X86_64.Secp256k1.Mul

open VG.Impl.Ecdsa.X86_64

/-- `vg_secp256k1_mul`. -/
def mulCode : Prog VG.X86_64.isa := secp256k1.mulFn

/-- Its body, which writes no vector register. -/
def bodyCode : Prog VG.X86_64.isa := secp256k1.mulBody

materialize_code bodyCode
materialize_code mulCode

end VG.Proof.Ecdsa.X86_64.Secp256k1.Mul
