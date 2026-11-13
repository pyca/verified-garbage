module

import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Lit
public import VerifiedGarbage.Proof.MlKem.X86_64.CheckEkScrub
public import VerifiedGarbage.Proof.MlKem.X86_64.CheckEk
public import VerifiedGarbage.Proof.MlKem.X86_64.CheckEkAvx2
public import VerifiedGarbage.Proof.MlKem.X86_64.KgMulV
public import VerifiedGarbage.Proof.MlKem.X86_64.DecMulV
public import VerifiedGarbage.Proof.MlKem.X86_64.EncMulV
public import VerifiedGarbage.Proof.MlKem.X86_64.Encode12
public import VerifiedGarbage.Proof.MlKem.X86_64.KpkeEncV
public import VerifiedGarbage.Proof.MlKem.X86_64.KpkeDecV
public import VerifiedGarbage.Proof.MlKem.X86_64.S4Verified16
public import VerifiedGarbage.Proof.MlKem.X86_64.Cbd16Avx2
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.MlKem.X86_64.Lit
public import VerifiedGarbage.Proof.MlKem.X86_64.CallWipe
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Variants.MlKemSample4.X86_64
public import VerifiedGarbage.Proof.Variants.Zeroize.X86_64
public import VerifiedGarbage.Proof.MlKem1024.X86_64.DecodeDecompress
public import VerifiedGarbage.Proof.MlKem1024.X86_64.CheckEk
public import VerifiedGarbage.Proof.MlKem1024.X86_64.CheckEkAvx2
public import VerifiedGarbage.Proof.MlKem1024.X86_64.CompressEncode
public import VerifiedGarbage.Proof.MlKem1024.X86_64.KpkeKgV
public import VerifiedGarbage.Proof.MlKem1024.X86_64.KpkeEncV
public import VerifiedGarbage.Proof.MlKem1024.X86_64.KpkeDecV

/-! # ML-KEM (FIPS 203) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.MlKem.X86_64

def direct : List Artifact := [
  Spec.MlKem.checkEkApi.artifact X86_64.target Proof.MlKem.X86_64.Scrub.checkEkReg,
  Spec.MlKem.checkEkApi.artifact X86_64.target Proof.MlKem.X86_64.Scrub.checkEkAvx2Reg]

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
  Spec.MlKem.keyGenApi.artifact X86_64.target (X86_64.Scrub.withScrubAll {
    suffix := Proof.MlKem.X86_64.Wipe.suffix v z
    code := Impl.MlKem.X86_64.keyGenW v.callee v.suffix z.name z.code
    stack := 56
    verified := Proof.MlKem.X86_64.keyGenW_verified v z
    spSafe := Proof.MlKem.X86_64.keyGenW_spSafe v z }
    (Proof.MlKem.X86_64.keyGenOut _)),
  Spec.MlKem.encapsHApi.artifact X86_64.target (X86_64.Scrub.withScrubAll {
    suffix := Proof.MlKem.X86_64.Wipe.suffix v z
    code := Impl.MlKem.X86_64.encapsHW v.callee v.suffix z.name z.code
    stack := 56
    verified := Proof.MlKem.X86_64.encapsHW_verified v z
    spSafe := Proof.MlKem.X86_64.encapsHW_spSafe v z }
    (Proof.MlKem.X86_64.encapsHOut _)),
  Spec.MlKem.encapsApi.artifact X86_64.target (X86_64.Scrub.withScrubAll {
    suffix := Proof.MlKem.X86_64.Wipe.suffix v z
    code := Impl.MlKem.X86_64.encapsW v.callee v.suffix z.name z.code
    stack := 56
    verified := Proof.MlKem.X86_64.encapsW_verified v z
    spSafe := Proof.MlKem.X86_64.encapsW_spSafe v z }
    (Proof.MlKem.X86_64.encapsOut _)),
  Spec.MlKem.decapsApi.artifact X86_64.target (X86_64.Scrub.withScrubAll {
    suffix := Proof.MlKem.X86_64.Wipe.suffix v z
    code := Impl.MlKem.X86_64.decapsW v.callee v.suffix z.name z.code
    stack := 56
    verified := Proof.MlKem.X86_64.decapsW_verified v z
    spSafe := Proof.MlKem.X86_64.decapsW_spSafe v z }
    (Proof.MlKem.X86_64.decapsOut _)),
  Spec.MlKem1024.keyGenApi.artifact X86_64.target (X86_64.Scrub.withScrubAll {
    suffix := Proof.MlKem.X86_64.Wipe.suffix v z
    code := Impl.MlKem.X86_64.keyGen1024W v.callee v.suffix z.name z.code
    stack := 56
    verified := Proof.MlKem.X86_64.keyGen1024W_verified v z
    spSafe := Proof.MlKem.X86_64.keyGen1024W_spSafe v z }
    (Proof.MlKem.X86_64.keyGen1024Out _)),
  Spec.MlKem1024.encapsHApi.artifact X86_64.target (X86_64.Scrub.withScrubAll {
    suffix := Proof.MlKem.X86_64.Wipe.suffix v z
    code := Impl.MlKem.X86_64.encapsH1024W v.callee v.suffix z.name z.code
    stack := 56
    verified := Proof.MlKem.X86_64.encapsH1024W_verified v z
    spSafe := Proof.MlKem.X86_64.encapsH1024W_spSafe v z }
    (Proof.MlKem.X86_64.encapsH1024Out _)),
  Spec.MlKem1024.encapsApi.artifact X86_64.target (X86_64.Scrub.withScrubAll {
    suffix := Proof.MlKem.X86_64.Wipe.suffix v z
    code := Impl.MlKem.X86_64.encaps1024W v.callee v.suffix z.name z.code
    stack := 56
    verified := Proof.MlKem.X86_64.encaps1024W_verified v z
    spSafe := Proof.MlKem.X86_64.encaps1024W_spSafe v z }
    (Proof.MlKem.X86_64.encaps1024Out _)),
  Spec.MlKem1024.decapsApi.artifact X86_64.target (X86_64.Scrub.withScrubAll {
    suffix := Proof.MlKem.X86_64.Wipe.suffix v z
    code := Impl.MlKem.X86_64.decaps1024W v.callee v.suffix z.name z.code
    stack := 56
    verified := Proof.MlKem.X86_64.decaps1024W_verified v z
    spSafe := Proof.MlKem.X86_64.decaps1024W_spSafe v z }
    (Proof.MlKem.X86_64.decaps1024Out _))]

end VG.Artifacts.MlKem.X86_64.MlKemSample4Zeroize

namespace VG.Artifacts.MlKem.X86_64

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.MlKemSample4.X86_64.variants.flatMap fun v => VG.Proof.Variants.Zeroize.X86_64.variants.flatMap fun v2 => MlKemSample4Zeroize.artifacts v v2) ++
  [
    Spec.MlKem1024.checkEkApi.artifact X86_64.target Proof.MlKem.X86_64.Scrub.checkEk1024Reg,
    Spec.MlKem1024.checkEkApi.artifact X86_64.target Proof.MlKem.X86_64.Scrub.checkEk1024Avx2Reg]

end VG.Artifacts.MlKem.X86_64
