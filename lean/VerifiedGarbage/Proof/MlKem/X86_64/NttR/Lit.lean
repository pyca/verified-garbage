module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.MlKem.X86_64.NttRegs
meta import VerifiedGarbage.Impl.MlKem.X86_64.NttRegs
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# ML-KEM on x86-64: the NTT on registers, its passes as literals

The kernel evaluates the passes of `nttR` in `check` (`Run.lean`), in the
constant-time analysis, and in the checks of every instruction of the
functions that contain them; these read the literals rather than running the
register allocation again.
-/

@[expose] public section

namespace VG

namespace Impl.MlKem.X86_64.NttR

/-- The halves of pass B, each with a literal of its own, for the runs of
the machine on them (`Run.lean`). -/
def passBRdi0 : List VG.X86_64.Instr := passB .rdi 0
def passBRdi1 : List VG.X86_64.Instr := passB .rdi 1
def passBR100 : List VG.X86_64.Instr := passB .r10 0
def passBR101 : List VG.X86_64.Instr := passB .r10 1

end Impl.MlKem.X86_64.NttR

materialize_value Impl.MlKem.X86_64.NttR.passA
materialize_value Impl.MlKem.X86_64.NttR.passBsRdi
materialize_value Impl.MlKem.X86_64.NttR.passBsR10
materialize_value Impl.MlKem.X86_64.NttR.passBRdi0
materialize_value Impl.MlKem.X86_64.NttR.passBRdi1
materialize_value Impl.MlKem.X86_64.NttR.passBR100
materialize_value Impl.MlKem.X86_64.NttR.passBR101
