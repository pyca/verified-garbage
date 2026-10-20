module

public import VerifiedGarbage.Impl.Ecdsa.P384.X86_64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Ecdsa.P384.X86_64
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# `vg_p384_inv_mod_p` and `_n` on x86-64: the code, as literals

The functions' code (`Cfg.invFn` of the divsteps), with and without BMI2 and
ADX, as literals (`materialize_code`), which `lit_decide` and `taint_decide`
read rather than building the code again.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64.P384.Inverse

open VG.Impl.Ecdsa.X86_64

/-- `vg_p384_inv_mod_p`. -/
def invP : Prog VG.X86_64.isa := p384.invFn p384.pPowI
/-- `vg_p384_inv_mod_p_adx`. -/
def invPAdx : Prog VG.X86_64.isa := p384x.invFn p384x.pPowI
/-- `vg_p384_inv_mod_n`. -/
def invN : Prog VG.X86_64.isa := p384.invFn p384.nPowI
/-- `vg_p384_inv_mod_n_adx`. -/
def invNAdx : Prog VG.X86_64.isa := p384x.invFn p384x.nPowI

materialize_code invP
materialize_code invPAdx
materialize_code invN
materialize_code invNAdx

end VG.Proof.Ecdsa.X86_64.P384.Inverse
