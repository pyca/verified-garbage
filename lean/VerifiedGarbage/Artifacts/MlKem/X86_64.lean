module

public import VerifiedGarbage.Impl.MlKem.X86_64.Fn
public import VerifiedGarbage.Proof.MlKem.X86_64.CheckEkScrub
public import VerifiedGarbage.Proof.MlKem.X86_64.KemScrub
public import VerifiedGarbage.Proof.Variants.MlKemSample4.X86_64
public import VerifiedGarbage.Proof.Variants.Zeroize.X86_64
public import VerifiedGarbage.TCB.X86_64.Print

/-! # ML-KEM (FIPS 203) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.MlKem.X86_64

def direct : List Artifact := [
  Spec.MlKem.checkEkApi.artifact X86_64.target { code := Impl.MlKem.X86_64.Fn.checkEk, verified := .scrubbed Proof.MlKem.X86_64.Scrub.checkEk_scrubbed, spSafe := Proof.MlKem.X86_64.Scrub.checkEk_spSafe },
  Spec.MlKem.checkEkApi.artifact X86_64.target { suffix := "_avx2", code := Impl.MlKem.X86_64.Fn.checkEkAvx2, verified := .scrubbed Proof.MlKem.X86_64.Scrub.checkEkAvx2_scrubbed, spSafe := Proof.MlKem.X86_64.Scrub.checkEkAvx2_spSafe }]

end VG.Artifacts.MlKem.X86_64

-- ML-KEM-768 and ML-KEM-1024 (FIPS 203) on x86-64: key generation, encapsulation (hashing the key, or with `H(ek)` given) and decapsulation
namespace VG.Artifacts.MlKem.X86_64.MlKemSample4Zeroize

open VG.Proof.MlKem.X86_64 (Sample4Impl)
open VG.Proof.Zeroize.X86_64 (ZeroizeImpl)


/-- The functions over `v`, wiping with `z`: none where `Wipe.skip` (an
implementation of `vg_mlkem_sample_ntt4` that needs CPU features is emitted
only with an implementation of `vg_zeroize` that needs some of them). -/
def artifacts (v : Sample4Impl) (z : ZeroizeImpl) : List Artifact :=
  if Proof.MlKem.X86_64.Wipe.skip v z then [] else [
  Spec.MlKem.keyGenApi.artifact X86_64.target {
    suffix := Proof.MlKem.X86_64.Wipe.suffix v z
    code := Impl.MlKem.X86_64.Fn.keyGen (Proof.MlKem.X86_64.KemScrub.level v z) v.callee v.suffix z.name z.code
    verified := .scrubbed (Proof.MlKem.X86_64.KemScrub.keyGen_scrubbed v z)
    spSafe := Proof.MlKem.X86_64.KemScrub.keyGen_spSafe v z },
  Spec.MlKem.encapsHApi.artifact X86_64.target {
    suffix := Proof.MlKem.X86_64.Wipe.suffix v z
    code := Impl.MlKem.X86_64.Fn.encapsH (Proof.MlKem.X86_64.KemScrub.level v z) v.callee v.suffix z.name z.code
    verified := .scrubbed (Proof.MlKem.X86_64.KemScrub.encapsH_scrubbed v z)
    spSafe := Proof.MlKem.X86_64.KemScrub.encapsH_spSafe v z },
  Spec.MlKem.encapsApi.artifact X86_64.target {
    suffix := Proof.MlKem.X86_64.Wipe.suffix v z
    code := Impl.MlKem.X86_64.Fn.encaps (Proof.MlKem.X86_64.KemScrub.level v z) v.callee v.suffix z.name z.code
    verified := .scrubbed (Proof.MlKem.X86_64.KemScrub.encaps_scrubbed v z)
    spSafe := Proof.MlKem.X86_64.KemScrub.encaps_spSafe v z },
  Spec.MlKem.decapsApi.artifact X86_64.target {
    suffix := Proof.MlKem.X86_64.Wipe.suffix v z
    code := Impl.MlKem.X86_64.Fn.decaps (Proof.MlKem.X86_64.KemScrub.level v z) v.callee v.suffix z.name z.code
    verified := .scrubbed (Proof.MlKem.X86_64.KemScrub.decaps_scrubbed v z)
    spSafe := Proof.MlKem.X86_64.KemScrub.decaps_spSafe v z },
  Spec.MlKem1024.keyGenApi.artifact X86_64.target {
    suffix := Proof.MlKem.X86_64.Wipe.suffix v z
    code := Impl.MlKem.X86_64.Fn.keyGen1024 (Proof.MlKem.X86_64.KemScrub.level v z) v.callee v.suffix z.name z.code
    verified := .scrubbed (Proof.MlKem.X86_64.KemScrub.keyGen1024_scrubbed v z)
    spSafe := Proof.MlKem.X86_64.KemScrub.keyGen1024_spSafe v z },
  Spec.MlKem1024.encapsHApi.artifact X86_64.target {
    suffix := Proof.MlKem.X86_64.Wipe.suffix v z
    code := Impl.MlKem.X86_64.Fn.encapsH1024 (Proof.MlKem.X86_64.KemScrub.level v z) v.callee v.suffix z.name z.code
    verified := .scrubbed (Proof.MlKem.X86_64.KemScrub.encapsH1024_scrubbed v z)
    spSafe := Proof.MlKem.X86_64.KemScrub.encapsH1024_spSafe v z },
  Spec.MlKem1024.encapsApi.artifact X86_64.target {
    suffix := Proof.MlKem.X86_64.Wipe.suffix v z
    code := Impl.MlKem.X86_64.Fn.encaps1024 (Proof.MlKem.X86_64.KemScrub.level v z) v.callee v.suffix z.name z.code
    verified := .scrubbed (Proof.MlKem.X86_64.KemScrub.encaps1024_scrubbed v z)
    spSafe := Proof.MlKem.X86_64.KemScrub.encaps1024_spSafe v z },
  Spec.MlKem1024.decapsApi.artifact X86_64.target {
    suffix := Proof.MlKem.X86_64.Wipe.suffix v z
    code := Impl.MlKem.X86_64.Fn.decaps1024 (Proof.MlKem.X86_64.KemScrub.level v z) v.callee v.suffix z.name z.code
    verified := .scrubbed (Proof.MlKem.X86_64.KemScrub.decaps1024_scrubbed v z)
    spSafe := Proof.MlKem.X86_64.KemScrub.decaps1024_spSafe v z }]

end VG.Artifacts.MlKem.X86_64.MlKemSample4Zeroize

namespace VG.Artifacts.MlKem.X86_64

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.MlKemSample4.X86_64.variants.flatMap fun v => VG.Proof.Variants.Zeroize.X86_64.variants.flatMap fun v2 => MlKemSample4Zeroize.artifacts v v2) ++
  [
    Spec.MlKem1024.checkEkApi.artifact X86_64.target { code := Impl.MlKem.X86_64.Fn.checkEk1024, verified := .scrubbed Proof.MlKem.X86_64.Scrub.checkEk1024_scrubbed, spSafe := Proof.MlKem.X86_64.Scrub.checkEk1024_spSafe },
    Spec.MlKem1024.checkEkApi.artifact X86_64.target { suffix := "_avx2", code := Impl.MlKem.X86_64.Fn.checkEk1024Avx2, verified := .scrubbed Proof.MlKem.X86_64.Scrub.checkEk1024Avx2_scrubbed, spSafe := Proof.MlKem.X86_64.Scrub.checkEk1024Avx2_spSafe }]

end VG.Artifacts.MlKem.X86_64
