module

public import VerifiedGarbage.Impl.Ecdsa.P521.ArmComb
import VerifiedGarbage.Proof.P521.Arm.CombLit
meta import VerifiedGarbage.Impl.Ecdsa.P521.ArmComb
meta import VerifiedGarbage.Proof.P521.Arm.CombLit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-! Materialize P-521's signing, public-key and verification pipelines with the
comb for checked taint evaluation.

The six pipelines call the same functions modulo `p` and `n`, and each of the three of a
multiplier contains the same comb: the kernel built each function's body, and the comb, again
in every pipeline's literal. Each is a literal of its own first, stated of the term the
pipelines have it as (the configuration `p521With u`'s fields, and `mulGeneratorP521With u`:
`materialize_code` finds a literal only by the term it was stated for), so that the
pipelines' literals evaluate only what is their own. -/

@[expose] public section
namespace VG

namespace Proof.Ecdsa.Arm.P521.CombLit
open Impl.Ecdsa.Arm Impl.Weierstrass.Arm

materialize_code mulP := Mont.mulFnWith (p521With false).umaal (p521With false).SP.k (p521With false).SP.m
materialize_code addP := Mont.addFnWith (p521With false).umaal (p521With false).SP.k (p521With false).SP.m
materialize_code subP := Mont.subFnWith (p521With false).umaal (p521With false).SP.k (p521With false).SP.m
materialize_code mulN := Mont.mulFnWith (p521With false).umaal (p521With false).SN.k (p521With false).SN.m
materialize_code addN := Mont.addFnWith (p521With false).umaal (p521With false).SN.k (p521With false).SN.m
materialize_code subN := Mont.subFnWith (p521With false).umaal (p521With false).SN.k (p521With false).SN.m
materialize_code mulPU := Mont.mulFnWith (p521With true).umaal (p521With true).SP.k (p521With true).SP.m
materialize_code addPU := Mont.addFnWith (p521With true).umaal (p521With true).SP.k (p521With true).SP.m
materialize_code subPU := Mont.subFnWith (p521With true).umaal (p521With true).SP.k (p521With true).SP.m
materialize_code mulNU := Mont.mulFnWith (p521With true).umaal (p521With true).SN.k (p521With true).SN.m
materialize_code addNU := Mont.addFnWith (p521With true).umaal (p521With true).SN.k (p521With true).SN.m
materialize_code subNU := Mont.subFnWith (p521With true).umaal (p521With true).SN.k (p521With true).SN.m
materialize_code comb := mulGeneratorP521With false
materialize_code combU := mulGeneratorP521With true

end Proof.Ecdsa.Arm.P521.CombLit

materialize_code Impl.Ecdsa.Arm.signP521Comb
materialize_code Impl.Ecdsa.Arm.publicKeyP521Comb
materialize_code Impl.Ecdsa.Arm.verifyP521Comb
materialize_code Impl.Ecdsa.Arm.signP521CombU
materialize_code Impl.Ecdsa.Arm.publicKeyP521CombU
materialize_code Impl.Ecdsa.Arm.verifyP521CombU
end VG
