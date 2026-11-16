module

public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Allocated
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticCachedHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticJacTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticMixedHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticMixedTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticRR
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticTableHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticTableTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds

/-! # The forwarded field programs of P-256 verification on AArch64, as its code spells them

The verifications inline their forwarded field programs
(`VerifyArithmetic.program`, `VerifyDouble.double`), so the kernel, checking a
verification's literal, would run the forwarding pass (`Forward.optimize`) on
each of them again: most of that check. Their literals exist
(`Forward/Arithmetic*.lean`, `Forward/P256Bounds.lean`, checked with the
pass's twin for the kernel), but for the programs as the proofs name them
(`Arithmetic.optimized k`), which the code does not mention. Here each has a
literal under the term the verification's code unfolds to, which
`materialize_code` then finds in it and reads (`Lit.unfoldToLits`): the two
terms are equal by unfolding definitions, without evaluating the pass. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64.ForwardLit
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Weierstrass.AArch64.Forward (optimize)
open VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Weierstrass.AArch64.Forward

noncomputable abbrev tableHead.lit := ArithmeticTableHead.rightCode.lit
theorem tableHead.lit_eq :
    optimize (fprog P256Joint.cfg.K.M
      (jacHead P256Joint.cfg.K.S P256Joint.cfg.K.R (Naf.twice P256Joint.cfg.K))) = tableHead.lit :=
  ArithmeticTableHead.rightCode.lit_eq

noncomputable abbrev tableTail.lit := ArithmeticTableTail.rightCode.lit
theorem tableTail.lit_eq :
    optimize (fprog P256Joint.cfg.K.M
      (jacTail P256Joint.cfg.K.S P256Joint.cfg.K.R (Naf.twice P256Joint.cfg.K) P256Joint.cfg.K.D)) =
      tableTail.lit :=
  ArithmeticTableTail.rightCode.lit_eq

noncomputable abbrev cachedHead.lit := ArithmeticCachedHead.rightCode.lit
theorem cachedHead.lit_eq :
    optimize (fprog P256Joint.cfg.K.M
      (Impl.Weierstrass.CachedJac.head P256Joint.cfg.K.S P256Joint.cfg.K.R P256Joint.cfg.K.E)) =
      cachedHead.lit :=
  ArithmeticCachedHead.rightCode.lit_eq

noncomputable abbrev jacTail.lit := ArithmeticJacTail.rightCode.lit
theorem jacTail.lit_eq :
    optimize (fprog P256Joint.cfg.K.M
      (Impl.Weierstrass.jacTail P256Joint.cfg.K.S P256Joint.cfg.K.R P256Joint.cfg.K.E
        P256Joint.cfg.K.D)) = jacTail.lit :=
  ArithmeticJacTail.rightCode.lit_eq

noncomputable abbrev mixedHead.lit := ArithmeticMixedHead.rightCode.lit
theorem mixedHead.lit_eq :
    optimize (fprog P256Joint.cfg.K.M
      (jacMixedHead P256Joint.cfg.K.S P256Joint.cfg.K.R P256Joint.cfg.K.E)) = mixedHead.lit :=
  ArithmeticMixedHead.rightCode.lit_eq

noncomputable abbrev mixedTail.lit := ArithmeticMixedTail.rightCode.lit
theorem mixedTail.lit_eq :
    optimize (fprog P256Joint.cfg.K.M
      (jacMixedTail P256Joint.cfg.K.S P256Joint.cfg.K.R P256Joint.cfg.K.E P256Joint.cfg.K.D)) =
      mixedTail.lit :=
  ArithmeticMixedTail.rightCode.lit_eq

noncomputable abbrev doubleRR.lit := ArithmeticRR.rightCode.lit
theorem doubleRR.lit_eq :
    optimize (fprog P256Joint.cfg.K.M
      (dblJMul P256Joint.cfg.K.S P256Joint.cfg.K.R P256Joint.cfg.K.R)) = doubleRR.lit :=
  ArithmeticRR.rightCode.lit_eq

noncomputable abbrev doubleRD.lit := P256Bounds.rightRD.lit
theorem doubleRD.lit_eq :
    optimize (fprog P256Joint.cfg.K.M
      (dblJMul P256Joint.cfg.K.S P256Joint.cfg.K.R P256Joint.cfg.K.D)) = doubleRD.lit :=
  P256Bounds.rightRD.lit_eq

/-- `doubleRD`, as the verification with allocated registers spells it. -/
noncomputable abbrev allocatedDoubleRD.lit := P256Bounds.rightRD.lit
theorem allocatedDoubleRD.lit_eq :
    optimize (fprog P256Allocated.K.M
      (dblJMul P256Allocated.K.S P256Allocated.K.R P256Allocated.K.D)) = allocatedDoubleRD.lit :=
  P256Bounds.rightRD.lit_eq

end VG.Proof.Ecdsa.Verify.AArch64.ForwardLit
