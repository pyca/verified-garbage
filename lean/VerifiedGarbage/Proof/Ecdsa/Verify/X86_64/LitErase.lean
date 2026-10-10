import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Timing
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Lit
import VerifiedGarbage.Impl.P256.CombTable7
import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
import VerifiedGarbage.Proof.Framework.LitShare

/-!
# ECDSA verification over P-256 on x86-64: the checked code without its displacements

From a taint that knows no region bases, the analysis does not read
displacements and immediates (`Proof/Framework/X86_64/TaintErase.lean`), so
the constant-time checks of the code before and after the comb, and of the
comb's tail, analyse it with them erased. Its field arithmetic is then the
same few blocks again and again: with each a constant (`materialize_shared`),
the kernel analyses each once from the same taint.
-/

namespace VG.Proof.Ecdsa.Verify.X86_64

open VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdsa.Verify.X86_64 VG.Proof.Weierstrass.X86_64

/-- P-256's comb table. -/
def p256Table : CombData := ⟨7,Impl.P256.p256Comb7,Impl.P256.p256Comb7Start,"VG_P256_COMB",true⟩

/-- The code before the comb, without its displacements. -/
def beforeErased : Prog VG.X86_64.isa := VG.X86_64.Code.erase (verifyPrefix p256)

/-- The code after the comb, without its displacements. -/
def afterErased : Prog VG.X86_64.isa := VG.X86_64.Code.erase (verifySuffix p256).inline

/-- The comb's tail, without its displacements. -/
def tailErased : Prog VG.X86_64.isa :=
  VG.X86_64.Code.erase (Code.seq (.block (publicLoads (p256.combCfg p256Table)))
    (publicRest (p256.combCfg p256Table))).inline

materialize_shared beforeErased
materialize_shared afterErased
materialize_shared tailErased

end VG.Proof.Ecdsa.Verify.X86_64
