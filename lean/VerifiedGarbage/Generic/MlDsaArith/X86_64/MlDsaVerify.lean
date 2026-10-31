module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Prims
import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Instrs
import Mathlib.Tactic.Conv
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Instrs
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.MlDsa.Pack.Arith
public import VerifiedGarbage.Proof.MlDsa.Pack.Stream
public import VerifiedGarbage.Proof.MlDsa.Verify.Bounds
public import VerifiedGarbage.Proof.MlDsa.Verify.Mem
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Same
public import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.HintPack
public import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.HintUnpack
public import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.SimpleBitPack
public import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.Unpack
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.BallCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CTCompute
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CTSample
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CTStages
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Control
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Correct
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Verified
public import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
public import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompress
import VerifiedGarbage.Proof.MlDsa.Pack.Arith
import VerifiedGarbage.Proof.MlDsa.Pack.Stream
import VerifiedGarbage.Proof.MlDsa.Verify.Bounds
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Same
import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.HintPack
import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.HintUnpack
import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.SimpleBitPack
import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.Unpack
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.BallCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CTCompute
import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CTSample
import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CTStages
import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Control
import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Correct
import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Verified
import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompress

/-! # ML-DSA (FIPS 204) on x86-64: verification -/

@[expose] public section

namespace VG.Generic.MlDsaArith.X86_64.MlDsaVerify

open VG
open VG.Proof.MlDsa.X86_64 (ArithImpl)
open VG.Proof.MlDsa.X86_64.Verify (primsWith prims_okWith verify_prims verify_spSafe)

def artifacts (v : ArithImpl) : List Artifact := [
  Spec.MlDsa.verify44Api.artifact X86_64.target {
    suffix := v.code.sfx
    features := v.features
    code := Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) Spec.MlDsa.mlDsa44
    stack := 32
    verified := verify_prims v (List.mem_cons_self ..)
    spSafe := verify_spSafe (prims_okWith v) (List.mem_cons_self ..) },
  Spec.MlDsa.verify65Api.artifact X86_64.target {
    suffix := v.code.sfx
    features := v.features
    code := Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) Spec.MlDsa.mlDsa65
    stack := 32
    verified := verify_prims v (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    spSafe := verify_spSafe (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_self ..)) },
  Spec.MlDsa.verify87Api.artifact X86_64.target {
    suffix := v.code.sfx
    features := v.features
    code := Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) Spec.MlDsa.mlDsa87
    stack := 32
    verified := verify_prims v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    spSafe := verify_spSafe (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) }]

end VG.Generic.MlDsaArith.X86_64.MlDsaVerify
