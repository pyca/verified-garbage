module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Prims
public import VerifiedGarbage.Proof.MlDsa.X86_64.PreparedKey.Prepare
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! # ML-DSA (FIPS 204) on x86-64: preparing keys -/

@[expose] public section

namespace VG.Generic.MlDsaArith.X86_64.MlDsaPreparedKey

open VG
open VG.Proof.MlDsa.X86_64 (ArithImpl)
open VG.Proof.MlDsa.X86_64.Verify (primsWith prims_okWith)
open VG.Proof.MlDsa.X86_64.Verify.Prepare (preparePublic_verified prepareSecret_verified preparePublic_spSafe
  prepareSecret_spSafe)

def artifacts (v : ArithImpl) : List Artifact :=
  if v.samplersOnly then [] else [
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact X86_64.target {
    suffix := v.code.sfx
    features := v.features
    code := Impl.MlDsa.X86_64.PreparedKey.preparePublic (primsWith v.code) Spec.MlDsa.mlDsa44
    stack := 32
    verified := preparePublic_verified (prims_okWith v) (List.mem_cons_self ..)
    spSafe := preparePublic_spSafe (prims_okWith v) (List.mem_cons_self ..) },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact X86_64.target {
    suffix := v.code.sfx
    features := v.features
    code := Impl.MlDsa.X86_64.PreparedKey.prepareSecret (primsWith v.code) Spec.MlDsa.mlDsa44
    stack := 32
    verified := prepareSecret_verified (prims_okWith v) (List.mem_cons_self ..)
    spSafe := prepareSecret_spSafe (prims_okWith v) (List.mem_cons_self ..) },
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact X86_64.target {
    suffix := v.code.sfx
    features := v.features
    code := Impl.MlDsa.X86_64.PreparedKey.preparePublic (primsWith v.code) Spec.MlDsa.mlDsa65
    stack := 32
    verified := preparePublic_verified (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    spSafe := preparePublic_spSafe (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_self ..)) },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact X86_64.target {
    suffix := v.code.sfx
    features := v.features
    code := Impl.MlDsa.X86_64.PreparedKey.prepareSecret (primsWith v.code) Spec.MlDsa.mlDsa65
    stack := 32
    verified := prepareSecret_verified (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    spSafe := prepareSecret_spSafe (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_self ..)) },
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact X86_64.target {
    suffix := v.code.sfx
    features := v.features
    code := Impl.MlDsa.X86_64.PreparedKey.preparePublic (primsWith v.code) Spec.MlDsa.mlDsa87
    stack := 32
    verified := preparePublic_verified (prims_okWith v)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    spSafe := preparePublic_spSafe (prims_okWith v)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact X86_64.target {
    suffix := v.code.sfx
    features := v.features
    code := Impl.MlDsa.X86_64.PreparedKey.prepareSecret (primsWith v.code) Spec.MlDsa.mlDsa87
    stack := 32
    verified := prepareSecret_verified (prims_okWith v)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    spSafe := prepareSecret_spSafe (prims_okWith v)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) }]

end VG.Generic.MlDsaArith.X86_64.MlDsaPreparedKey
