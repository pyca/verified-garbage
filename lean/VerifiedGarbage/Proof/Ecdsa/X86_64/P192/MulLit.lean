import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Ecdsa.P192.X86_64

/-!
# `vg_p192_mul` on x86-64: the code, as literals

The function's code (`Cfg.mulFn`) and its body, as literals
(`materialize_code`), which `lit_decide` and `taint_decide` read rather than
building the code again.
-/

namespace VG.Proof.Ecdsa.X86_64.P192.Mul

open VG.Impl.Ecdsa.X86_64

/-- `vg_p192_mul`. -/
def mulCode : Prog VG.X86_64.isa := p192.mulFn

/-- Its body, which writes no vector register. -/
def bodyCode : Prog VG.X86_64.isa := p192.mulBody

materialize_code bodyCode
materialize_code mulCode

end VG.Proof.Ecdsa.X86_64.P192.Mul
