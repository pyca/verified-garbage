module

public import VerifiedGarbage.Proof.MlKem.X86_64.CallWipe
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # ML-KEM-768 and ML-KEM-1024 (FIPS 203) on x86-64: key generation, encapsulation (hashing the key, or with `H(ek)` given) and decapsulation -/

@[expose] public section

namespace VG.Generic.MlKemSample4.Zeroize.X86_64.MlKem

open VG.Proof.MlKem.X86_64 (Sample4Impl)
open VG.Proof.Zeroize.X86_64 (ZeroizeImpl)

def artifacts (v : Sample4Impl) (z : ZeroizeImpl) : List Artifact :=
  if Proof.MlKem.X86_64.Wipe.skip v z then [] else [
  Spec.MlKem.keyGenApi.artifact X86_64.target {
    suffix := Proof.MlKem.X86_64.Wipe.suffix v z
    code := Impl.MlKem.X86_64.keyGenW v.callee v.suffix z.name z.code
    stack := 56
    verified := Proof.MlKem.X86_64.keyGenW_verified v z
    spSafe := Proof.MlKem.X86_64.keyGenW_spSafe v z
    features := Proof.MlKem.X86_64.Wipe.features v z },
  Spec.MlKem.encapsHApi.artifact X86_64.target {
    suffix := Proof.MlKem.X86_64.Wipe.suffix v z
    code := Impl.MlKem.X86_64.encapsHW v.callee v.suffix z.name z.code
    stack := 56
    verified := Proof.MlKem.X86_64.encapsHW_verified v z
    spSafe := Proof.MlKem.X86_64.encapsHW_spSafe v z
    features := Proof.MlKem.X86_64.Wipe.features v z },
  Spec.MlKem.encapsApi.artifact X86_64.target {
    suffix := Proof.MlKem.X86_64.Wipe.suffix v z
    code := Impl.MlKem.X86_64.encapsW v.callee v.suffix z.name z.code
    stack := 56
    verified := Proof.MlKem.X86_64.encapsW_verified v z
    spSafe := Proof.MlKem.X86_64.encapsW_spSafe v z
    features := Proof.MlKem.X86_64.Wipe.features v z },
  Spec.MlKem.decapsApi.artifact X86_64.target {
    suffix := Proof.MlKem.X86_64.Wipe.suffix v z
    code := Impl.MlKem.X86_64.decapsW v.callee v.suffix z.name z.code
    stack := 56
    verified := Proof.MlKem.X86_64.decapsW_verified v z
    spSafe := Proof.MlKem.X86_64.decapsW_spSafe v z
    features := Proof.MlKem.X86_64.Wipe.features v z },
  Spec.MlKem1024.keyGenApi.artifact X86_64.target {
    suffix := Proof.MlKem.X86_64.Wipe.suffix v z
    code := Impl.MlKem.X86_64.keyGen1024W v.callee v.suffix z.name z.code
    stack := 56
    verified := Proof.MlKem.X86_64.keyGen1024W_verified v z
    spSafe := Proof.MlKem.X86_64.keyGen1024W_spSafe v z
    features := Proof.MlKem.X86_64.Wipe.features v z },
  Spec.MlKem1024.encapsHApi.artifact X86_64.target {
    suffix := Proof.MlKem.X86_64.Wipe.suffix v z
    code := Impl.MlKem.X86_64.encapsH1024W v.callee v.suffix z.name z.code
    stack := 56
    verified := Proof.MlKem.X86_64.encapsH1024W_verified v z
    spSafe := Proof.MlKem.X86_64.encapsH1024W_spSafe v z
    features := Proof.MlKem.X86_64.Wipe.features v z },
  Spec.MlKem1024.encapsApi.artifact X86_64.target {
    suffix := Proof.MlKem.X86_64.Wipe.suffix v z
    code := Impl.MlKem.X86_64.encaps1024W v.callee v.suffix z.name z.code
    stack := 56
    verified := Proof.MlKem.X86_64.encaps1024W_verified v z
    spSafe := Proof.MlKem.X86_64.encaps1024W_spSafe v z
    features := Proof.MlKem.X86_64.Wipe.features v z },
  Spec.MlKem1024.decapsApi.artifact X86_64.target {
    suffix := Proof.MlKem.X86_64.Wipe.suffix v z
    code := Impl.MlKem.X86_64.decaps1024W v.callee v.suffix z.name z.code
    stack := 56
    verified := Proof.MlKem.X86_64.decaps1024W_verified v z
    spSafe := Proof.MlKem.X86_64.decaps1024W_spSafe v z
    features := Proof.MlKem.X86_64.Wipe.features v z }]

end VG.Generic.MlKemSample4.Zeroize.X86_64.MlKem
