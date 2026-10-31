module

import VerifiedGarbage.Proof.MlDsa.X86_64.Message.VerifyFn
import Mathlib.Tactic.Conv
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.MlDsa.X86_64.Message
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Prims
import VerifiedGarbage.Proof.MlDsa.X86_64.Message.VerifyVerified
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.VerifyFn
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.VerifyVerified
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Spec.MlDsa.CachedVerify
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CallPack

/-! # ML-DSA (FIPS 204) on x86-64: verifying messages -/

@[expose] public section

namespace VG.Generic.MlDsaArith.X86_64.MlDsaVerifyMessageCached

open VG
open VG.Proof.MlDsa.X86_64 (ArithImpl)
open VG.Proof.MlDsa.X86_64.Verify (primsWith prims_okWith verify_spSafe)
open VG.Proof.MlDsa.X86_64.Message (verifyFn verifyMessage_verified verifyMessage_spSafe)

def artifacts (v : ArithImpl) : List Artifact := [
  (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact X86_64.target {
    suffix := v.code.sfx
    features := v.features
    code := Impl.MlDsa.X86_64.Message.verifyMessageCached (Spec.MlDsa.verify44Api.name ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) Spec.MlDsa.mlDsa44) Spec.MlDsa.mlDsa44
    stack := 112
    verified := verifyMessage_verified (verifyFn v (List.mem_cons_self ..)) (List.mem_cons_self ..)
    spSafe := verifyMessage_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_self ..)) },
  (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact X86_64.target {
    suffix := v.code.sfx
    features := v.features
    code := Impl.MlDsa.X86_64.Message.verifyMessageCached (Spec.MlDsa.verify65Api.name ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) Spec.MlDsa.mlDsa65) Spec.MlDsa.mlDsa65
    stack := 112
    verified := verifyMessage_verified (verifyFn v (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    spSafe := verifyMessage_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_self ..))) },
  (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact X86_64.target {
    suffix := v.code.sfx
    features := v.features
    code := Impl.MlDsa.X86_64.Message.verifyMessageCached (Spec.MlDsa.verify87Api.name ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) Spec.MlDsa.mlDsa87) Spec.MlDsa.mlDsa87
    stack := 112
    verified := verifyMessage_verified (verifyFn v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..)))) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    spSafe := verifyMessage_spSafe (verify_spSafe (prims_okWith v)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) }]

end VG.Generic.MlDsaArith.X86_64.MlDsaVerifyMessageCached
