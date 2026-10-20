module

public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.X86_64
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.Ecdsa.Secp256k1.X86_64
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.TCB.X86_64.Target

/-!
# `vg_secp256k1_inv_mod_p` and `_n` on x86-64: the code, as literals

The functions' code (`Cfg.invFn` of the divsteps), as literals (`materialize_code`), which `lit_decide` and `taint_decide`
read rather than building the code again.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64.Secp256k1.Inverse

open VG.Impl.Ecdsa.X86_64

/-- `vg_secp256k1_inv_mod_p`. -/
def invP : Prog VG.X86_64.isa := secp256k1.invFn secp256k1.pPowI
/-- `vg_secp256k1_inv_mod_n`. -/
def invN : Prog VG.X86_64.isa := secp256k1.invFn secp256k1.nPowI

/-- The bodies, which write no vector register. -/
def bodyP : Prog VG.X86_64.isa := secp256k1.pPowI
def bodyN : Prog VG.X86_64.isa := secp256k1.nPowI

materialize_code bodyP
materialize_code bodyN
materialize_code invP
materialize_code invN

end VG.Proof.Ecdsa.X86_64.Secp256k1.Inverse
