module

public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.X86_64
meta import VerifiedGarbage.Impl.Ecdsa.Secp256k1.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
public import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.Syms
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.X86_64.Inline
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.Syms

/-!
# `vg_secp256k1_mul` on x86-64: the code, as literals

The function's code (`Cfg.mulFn`) and its body, as literals
(`materialize_code`), which `lit_decide` and `taint_decide` read rather than
building the code again.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64.Secp256k1.Mul

open VG.Impl.Ecdsa.X86_64

/-- `vg_secp256k1_mul`. -/
def mulCode : Prog VG.X86_64.isa := secp256k1.mulFn

/-- Its body, which writes no vector register. -/
def bodyCode : Prog VG.X86_64.isa := secp256k1.mulBody

materialize_code bodyCode
materialize_code mulCode

/-! The function without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check (`mul_ct`) analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/

def mulCodeErased : Prog VG.X86_64.isa := VG.X86_64.Code.erase mulCode
materialize_shared mulCodeErased

end VG.Proof.Ecdsa.X86_64.Secp256k1.Mul
