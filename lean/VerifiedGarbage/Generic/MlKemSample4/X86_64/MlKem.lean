module

public import VerifiedGarbage.Proof.MlKem.X86_64.Top768
public import VerifiedGarbage.Proof.MlKem1024.X86_64.Top
public import VerifiedGarbage.Proof.MlKem1024.X86_64.Written
public import VerifiedGarbage.Proof.MlKem.X86_64.Instances
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-KEM-768 and ML-KEM-1024 (FIPS 203) on x86-64: key generation, encapsulation (hashing the key, or with `H(ek)` given) and decapsulation -/

@[expose] public section

namespace VG.Generic.MlKemSample4.X86_64.MlKem

open VG.Proof.MlKem.X86_64 (Sample4Impl)

def artifacts (v : Sample4Impl) : List Artifact := [
  Spec.MlKem.keyGenApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.MlKem.X86_64.keyGen v.callee
    stack := 32
    verified := Proof.MlKem.X86_64.keyGen_verified v
    spSafe := Proof.MlKem.X86_64.keyGen_spSafe v
    features := v.features },
  Spec.MlKem.encapsHApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.MlKem.X86_64.encapsH v.callee
    stack := 32
    verified := Proof.MlKem.X86_64.encapsH_verified v
    spSafe := Proof.MlKem.X86_64.encapsH_spSafe v
    features := v.features },
  Spec.MlKem.encapsApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.MlKem.X86_64.encaps v.callee
    stack := 32
    verified := Proof.MlKem.X86_64.encaps_verified v
    spSafe := Proof.MlKem.X86_64.encaps_spSafe v
    features := v.features },
  Spec.MlKem.decapsApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.MlKem.X86_64.decaps v.callee
    stack := 32
    verified := Proof.MlKem.X86_64.decaps_verified v
    spSafe := Proof.MlKem.X86_64.decaps_spSafe v
    features := v.features },
  Spec.MlKem1024.keyGenApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.MlKem1024.X86_64.keyGen1024 v.callee
    stack := 32
    verified := Proof.MlKem1024.X86_64.keyGen1024_verified v
    spSafe := Proof.MlKem.X86_64.keyGen1024_spSafe v
    written := Proof.MlKem1024.X86_64.written v
    writtenOk := Proof.MlKem1024.X86_64.keyGen1024_written v
    features := v.features },
  Spec.MlKem1024.encapsHApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.MlKem1024.X86_64.encapsH1024 v.callee
    stack := 32
    verified := Proof.MlKem1024.X86_64.encapsH1024_verified v
    spSafe := Proof.MlKem.X86_64.encapsH1024_spSafe v
    written := Proof.MlKem1024.X86_64.written v
    writtenOk := Proof.MlKem1024.X86_64.encapsH1024_written v
    features := v.features },
  Spec.MlKem1024.encapsApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.MlKem1024.X86_64.encaps1024 v.callee
    stack := 32
    verified := Proof.MlKem1024.X86_64.encaps1024_verified v
    spSafe := Proof.MlKem.X86_64.encaps1024_spSafe v
    written := Proof.MlKem1024.X86_64.writtenEnc v
    writtenOk := Proof.MlKem1024.X86_64.encaps1024_written v
    features := v.features },
  Spec.MlKem1024.decapsApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.MlKem1024.X86_64.decaps1024 v.callee
    stack := 32
    verified := Proof.MlKem1024.X86_64.decaps1024_verified v
    spSafe := Proof.MlKem.X86_64.decaps1024_spSafe v
    written := Proof.MlKem1024.X86_64.writtenEnc v
    writtenOk := Proof.MlKem1024.X86_64.decaps1024_written v
    features := v.features }]

end VG.Generic.MlKemSample4.X86_64.MlKem
