import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.LitAdx
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.LitErase
import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
import VerifiedGarbage.Proof.Framework.LitShare

/-!
# ECDSA verification over P-256 on x86-64 with BMI2 and ADX: the checked code without its displacements

From a taint that knows no region bases, the analysis does not read
displacements and immediates (`Proof/Framework/X86_64/TaintErase.lean`), so
the constant-time checks of the code before and after the comb, and of the
comb's tail, analyse it with them erased. Its field arithmetic is then the
same few blocks again and again: with each a constant (`materialize_shared`),
the kernel analyses each once from the same taint.
-/

namespace VG.Proof.Ecdsa.Verify.X86_64

open VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdsa.Verify.X86_64 VG.Proof.Weierstrass.X86_64

/-- The code before the comb, without its displacements. -/
def beforeErasedAdx : Prog VG.X86_64.isa := VG.X86_64.Code.erase (verifyPrefix p256x)

/-- The code after the comb, without its displacements. -/
def afterErasedAdx : Prog VG.X86_64.isa := VG.X86_64.Code.erase (verifySuffix p256x).inline

/-- The comb's tail, without its displacements. -/
def tailErasedAdx : Prog VG.X86_64.isa :=
  VG.X86_64.Code.erase (Code.seq (.block (publicLoads (p256x.combCfg p256Table)))
    (publicRest (p256x.combCfg p256Table))).inline

materialize_shared beforeErasedAdx
materialize_shared afterErasedAdx
materialize_shared tailErasedAdx

end VG.Proof.Ecdsa.Verify.X86_64
