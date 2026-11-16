module

public import VerifiedGarbage.Impl.Ecdsa.P384.ArmComb
import VerifiedGarbage.Proof.P384.Arm.CombLit
meta import VerifiedGarbage.Impl.Ecdsa.P384.ArmComb
meta import VerifiedGarbage.Proof.P384.Arm.CombLit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-! Materialize P-384's signing, public-key and verification pipelines with the
comb for checked taint evaluation.

The six pipelines call the same functions modulo `p` and `n`, and each of the three of a
multiplier contains the same comb: the kernel built each function's body, and the comb, again
in every pipeline's literal. Each is a literal of its own first, stated of the term the
pipelines have it as (the configuration `p384With u`'s fields, and `mulGeneratorP384With u`:
`materialize_code` finds a literal only by the term it was stated for), so that the
pipelines' literals evaluate only what is their own. -/

@[expose] public section
namespace VG

namespace Proof.Ecdsa.Arm.P384.CombLit
open Impl.Ecdsa.Arm Impl.Weierstrass.Arm

materialize_code mulP := Mont.mulFnWith (p384With false).umaal (p384With false).SP.k (p384With false).SP.m
materialize_code addP := Mont.addFn (p384With false).SP.k (p384With false).SP.m
materialize_code subP := Mont.subFn (p384With false).SP.k (p384With false).SP.m
materialize_code mulN := Mont.mulFnWith (p384With false).umaal (p384With false).SN.k (p384With false).SN.m
materialize_code addN := Mont.addFn (p384With false).SN.k (p384With false).SN.m
materialize_code subN := Mont.subFn (p384With false).SN.k (p384With false).SN.m
materialize_code mulPU := Mont.mulFnWith (p384With true).umaal (p384With true).SP.k (p384With true).SP.m
materialize_code addPU := Mont.addFn (p384With true).SP.k (p384With true).SP.m
materialize_code subPU := Mont.subFn (p384With true).SP.k (p384With true).SP.m
materialize_code mulNU := Mont.mulFnWith (p384With true).umaal (p384With true).SN.k (p384With true).SN.m
materialize_code addNU := Mont.addFn (p384With true).SN.k (p384With true).SN.m
materialize_code subNU := Mont.subFn (p384With true).SN.k (p384With true).SN.m
materialize_code comb := mulGeneratorP384With false
materialize_code combU := mulGeneratorP384With true

end Proof.Ecdsa.Arm.P384.CombLit

materialize_code Impl.Ecdsa.Arm.signP384Comb
materialize_code Impl.Ecdsa.Arm.publicKeyP384Comb
materialize_code Impl.Ecdsa.Arm.verifyP384Comb
materialize_code Impl.Ecdsa.Arm.signP384CombU
materialize_code Impl.Ecdsa.Arm.publicKeyP384CombU
materialize_code Impl.Ecdsa.Arm.verifyP384CombU
end VG
