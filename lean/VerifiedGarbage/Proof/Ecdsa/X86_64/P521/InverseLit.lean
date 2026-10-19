module

public import VerifiedGarbage.Impl.Ecdsa.P521.X86_64
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.Ecdsa.P521.X86_64
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
# `vg_p521_inv_mod_p` and `_n` on x86-64: the code, as literals

The functions' code (`Cfg.invFn` of the divsteps), with and without BMI2 and
ADX, as literals (`materialize_code`), which `lit_decide` and `taint_decide`
read rather than building the code again.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64.P521.Inverse

open VG.Impl.Ecdsa.X86_64

/-- `vg_p521_inv_mod_p`. -/
def invP : Prog VG.X86_64.isa := p521.invFn p521.pPowI
/-- `vg_p521_inv_mod_p_adx`. -/
def invPAdx : Prog VG.X86_64.isa := p521x.invFn p521x.pPowI
/-- `vg_p521_inv_mod_n`. -/
def invN : Prog VG.X86_64.isa := p521.invFn p521.nPowI
/-- `vg_p521_inv_mod_n_adx`. -/
def invNAdx : Prog VG.X86_64.isa := p521x.invFn p521x.nPowI

materialize_code invP
materialize_code invPAdx
materialize_code invN
materialize_code invNAdx

end VG.Proof.Ecdsa.X86_64.P521.Inverse
