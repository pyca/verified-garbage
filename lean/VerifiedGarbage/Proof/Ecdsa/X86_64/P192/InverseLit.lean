module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.Ecdsa.P192.X86_64
meta import VerifiedGarbage.Impl.Ecdsa.P192.X86_64
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# `vg_p192_inv_mod_p` and `_n` on x86-64: the code, as literals

The functions' code (`Cfg.invFn` of the divsteps), as literals (`materialize_code`), which `lit_decide` and `taint_decide`
read rather than building the code again.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64.P192.Inverse

open VG.Impl.Ecdsa.X86_64

/-- `vg_p192_inv_mod_p`. -/
def invP : Prog VG.X86_64.isa := p192.invFn p192.pPowI
/-- `vg_p192_inv_mod_n`. -/
def invN : Prog VG.X86_64.isa := p192.invFn p192.nPowI

/-- The bodies, which write no vector register. -/
def bodyP : Prog VG.X86_64.isa := p192.pPowI
def bodyN : Prog VG.X86_64.isa := p192.nPowI

materialize_code bodyP
materialize_code bodyN
materialize_code invP
materialize_code invN

end VG.Proof.Ecdsa.X86_64.P192.Inverse
