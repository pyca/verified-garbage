module

public import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP384r1.X86_64
public import VerifiedGarbage.Proof.Weierstrass.X86_64.BrainpoolP384r1Literals
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP384r1.X86_64
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.BrainpoolP384r1Literals
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64.BrainpoolP384r1

open VG.Impl.Ecdsa.Verify.X86_64

/-- The literals of `BrainpoolP384r1Literals`, under the terms the verification's code
has: its configuration is `brainpoolp384r1S`, `brainpoolp384r1` with the comb's tables, and
`materialize_code` finds a literal by its term. These pieces do not read the
tables: the two terms are equal by unfolding the configurations. -/
private noncomputable abbrev nPowS.lit := Weierstrass.X86_64.BrainpoolP384r1Literals.nPow.lit
private theorem nPowS.lit_eq : Impl.Ecdsa.X86_64.brainpoolp384r1S.nPow = nPowS.lit :=
  Weierstrass.X86_64.BrainpoolP384r1Literals.nPow.lit_eq
private noncomputable abbrev pPowS.lit := Weierstrass.X86_64.BrainpoolP384r1Literals.pPow.lit
private theorem pPowS.lit_eq : Impl.Ecdsa.X86_64.brainpoolp384r1S.pPow = pPowS.lit :=
  Weierstrass.X86_64.BrainpoolP384r1Literals.pPow.lit_eq
private noncomputable abbrev checkS.lit := Weierstrass.X86_64.BrainpoolP384r1Literals.check.lit
private theorem checkS.lit_eq :
    Impl.Ecdh.X86_64.Cfg.check Impl.Ecdsa.X86_64.brainpoolp384r1S = checkS.lit :=
  Weierstrass.X86_64.BrainpoolP384r1Literals.check.lit_eq

materialize_code verifyBrainpoolP384r1

end VG.Proof.Ecdsa.Verify.X86_64.BrainpoolP384r1
