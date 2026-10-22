module

public import VerifiedGarbage.Impl.MlKem.X86_64.NttRegs
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.MlKem.X86_64.NttRegs
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# ML-KEM on x86-64: the NTT on registers, its passes as literals

The kernel evaluates the passes of `nttR` in `check` (`Run.lean`), in the
constant-time analysis, and in the checks of every instruction of the
functions that contain them; these read the literals rather than running the
register allocation again.

Name each half's
underlying generator application explicitly, so the combined passes reuse
its checked literal instead of evaluating the allocator a second time.
-/

@[expose] public section

namespace VG

namespace Impl.MlKem.X86_64.NttR

/-- The halves of pass B, each with a literal of its own, for the runs of
the machine on them (`Run.lean`). -/
def passBR100 : List VG.X86_64.Instr := passB .r10 0
def passBR101 : List VG.X86_64.Instr := passB .r10 1
def passBAccR100 : List VG.X86_64.Instr := passBAcc .r10 0
def passBAccR101 : List VG.X86_64.Instr := passBAcc .r10 1
def passIBAcc0 : List VG.X86_64.Instr := passIB .acc 0
def passIBAcc1 : List VG.X86_64.Instr := passIB .acc 1

end Impl.MlKem.X86_64.NttR

materialize_value Impl.MlKem.X86_64.NttR.passA
materialize_value Impl.MlKem.X86_64.NttR.passBR100 :=
  Impl.MlKem.X86_64.NttR.passB .r10 0
materialize_value Impl.MlKem.X86_64.NttR.passBR101 :=
  Impl.MlKem.X86_64.NttR.passB .r10 1
materialize_value Impl.MlKem.X86_64.NttR.passBsR10
materialize_value Impl.MlKem.X86_64.NttR.passBAccR100 :=
  Impl.MlKem.X86_64.NttR.passBAcc .r10 0
materialize_value Impl.MlKem.X86_64.NttR.passBAccR101 :=
  Impl.MlKem.X86_64.NttR.passBAcc .r10 1
materialize_value Impl.MlKem.X86_64.NttR.passBsAccR10
materialize_value Impl.MlKem.X86_64.NttR.passIA
materialize_value Impl.MlKem.X86_64.NttR.passIBAcc0 :=
  Impl.MlKem.X86_64.NttR.passIB .acc 0
materialize_value Impl.MlKem.X86_64.NttR.passIBAcc1 :=
  Impl.MlKem.X86_64.NttR.passIB .acc 1
materialize_value Impl.MlKem.X86_64.NttR.passIBsAcc
