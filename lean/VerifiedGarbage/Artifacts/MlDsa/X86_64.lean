module

public import VerifiedGarbage.Impl.MlDsa.X86_64.Fn
public import VerifiedGarbage.Proof.MlDsa.X86_64.FnScrub
public import VerifiedGarbage.Proof.MlDsa.X86_64.SignScrub
public import VerifiedGarbage.Proof.MlDsa.X86_64.VerifyScrub
public import VerifiedGarbage.Proof.MlDsa.X86_64.PreparedKey.Scrub
public import VerifiedGarbage.Proof.Variants.MlDsaArith.X86_64
public import VerifiedGarbage.TCB.X86_64.Print

/-! # ML-DSA (FIPS 204) on x86-64 -/

@[expose] public section

-- ML-DSA (FIPS 204) on x86-64: key generation
namespace VG.Artifacts.MlDsa.X86_64.KeyGen

open VG
open VG.Proof.MlDsa.X86_64 (ArithImpl)

def artifactsFor (v : ArithImpl) : List Artifact := [
  Spec.MlDsa.keyGen44Api.artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Fn.keyGen v.level v.code Spec.MlDsa.mlDsa44
    verified := Proof.MlDsa.X86_64.FnScrub.keyGen44_scrubbed v
    spSafe := Proof.MlDsa.X86_64.FnScrub.keyGen44_spSafe v },
  Spec.MlDsa.keyGen65Api.artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Fn.keyGen v.level v.code Spec.MlDsa.mlDsa65
    verified := Proof.MlDsa.X86_64.FnScrub.keyGen65_scrubbed v
    spSafe := Proof.MlDsa.X86_64.FnScrub.keyGen65_spSafe v },
  Spec.MlDsa.keyGen87Api.artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Fn.keyGen v.level v.code Spec.MlDsa.mlDsa87
    verified := Proof.MlDsa.X86_64.FnScrub.keyGen87_scrubbed v
    spSafe := Proof.MlDsa.X86_64.FnScrub.keyGen87_spSafe v }]

def artifacts : List Artifact :=
  VG.Proof.Variants.MlDsaArith.X86_64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.MlDsa.X86_64.KeyGen

-- ML-DSA (FIPS 204) on x86-64: preparing keys
namespace VG.Artifacts.MlDsa.X86_64.PreparedKey

open VG
open VG.Proof.MlDsa.X86_64 (ArithImpl)

def artifactsFor (v : Proof.MlDsa.X86_64.PreparedKey.Scrub.PrepImpl) : List Artifact := [
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact X86_64.target {
    suffix := v.arith.code.sfx
    code := Impl.MlDsa.X86_64.Fn.preparePublic v.arith.level (Proof.MlDsa.X86_64.Verify.primsWith v.arith.code) Spec.MlDsa.mlDsa44
    verified := Proof.MlDsa.X86_64.FnScrub.preparePublic44_scrubbed v.arith
    spSafe := Proof.MlDsa.X86_64.FnScrub.preparePublic44_spSafe v.arith },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact X86_64.target {
    suffix := v.arith.code.sfx
    code := Impl.MlDsa.X86_64.Fn.prepareSecret v.arith.level (Proof.MlDsa.X86_64.Verify.primsWith v.arith.code) Spec.MlDsa.mlDsa44
    verified := Proof.MlDsa.X86_64.FnScrub.prepareSecret44_scrubbed v.arith
    spSafe := Proof.MlDsa.X86_64.FnScrub.prepareSecret44_spSafe v.arith },
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact X86_64.target {
    suffix := v.arith.code.sfx
    code := Impl.MlDsa.X86_64.Fn.preparePublic v.arith.level (Proof.MlDsa.X86_64.Verify.primsWith v.arith.code) Spec.MlDsa.mlDsa65
    verified := Proof.MlDsa.X86_64.FnScrub.preparePublic65_scrubbed v.arith
    spSafe := Proof.MlDsa.X86_64.FnScrub.preparePublic65_spSafe v.arith },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact X86_64.target {
    suffix := v.arith.code.sfx
    code := Impl.MlDsa.X86_64.Fn.prepareSecret v.arith.level (Proof.MlDsa.X86_64.Verify.primsWith v.arith.code) Spec.MlDsa.mlDsa65
    verified := Proof.MlDsa.X86_64.FnScrub.prepareSecret65_scrubbed v.arith
    spSafe := Proof.MlDsa.X86_64.FnScrub.prepareSecret65_spSafe v.arith },
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact X86_64.target {
    suffix := v.arith.code.sfx
    code := Impl.MlDsa.X86_64.Fn.preparePublic v.arith.level (Proof.MlDsa.X86_64.Verify.primsWith v.arith.code) Spec.MlDsa.mlDsa87
    verified := Proof.MlDsa.X86_64.FnScrub.preparePublic87_scrubbed v.arith
    spSafe := Proof.MlDsa.X86_64.FnScrub.preparePublic87_spSafe v.arith },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact X86_64.target {
    suffix := v.arith.code.sfx
    code := Impl.MlDsa.X86_64.Fn.prepareSecret v.arith.level (Proof.MlDsa.X86_64.Verify.primsWith v.arith.code) Spec.MlDsa.mlDsa87
    verified := Proof.MlDsa.X86_64.FnScrub.prepareSecret87_scrubbed v.arith
    spSafe := Proof.MlDsa.X86_64.FnScrub.prepareSecret87_spSafe v.arith }]

def artifacts : List Artifact :=
  VG.Proof.Variants.MlDsaArith.X86_64.samplerFreeVariants.flatMap fun v => artifactsFor v

end VG.Artifacts.MlDsa.X86_64.PreparedKey

-- ML-DSA (FIPS 204) on x86-64: signing
namespace VG.Artifacts.MlDsa.X86_64.Sign

open VG
open VG.Proof.MlDsa.X86_64 (ArithImpl)

def artifactsFor (v : ArithImpl) : List Artifact := [
  Spec.MlDsa.sign44Api.artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Fn.signEntry v.level (Proof.MlDsa.signWithCacheName "mldsa44" ++ v.code.sfx) (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa44 0
    verified := Proof.MlDsa.X86_64.SignScrub.sign44_scrubbed v
    spSafe := Proof.MlDsa.X86_64.SignScrub.sign44_spSafe v },
  Spec.MlDsa.sign65Api.artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Fn.signEntry v.level (Proof.MlDsa.signWithCacheName "mldsa65" ++ v.code.sfx) (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa65 0
    verified := Proof.MlDsa.X86_64.SignScrub.sign65_scrubbed v
    spSafe := Proof.MlDsa.X86_64.SignScrub.sign65_spSafe v },
  Spec.MlDsa.sign87Api.artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Fn.signEntry v.level (Proof.MlDsa.signWithCacheName "mldsa87" ++ v.code.sfx) (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa87 0
    verified := Proof.MlDsa.X86_64.SignScrub.sign87_scrubbed v
    spSafe := Proof.MlDsa.X86_64.SignScrub.sign87_spSafe v },
  (Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Fn.signEntry v.level (Proof.MlDsa.signWithCacheName "mldsa44" ++ v.code.sfx) (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa44 1
    verified := Proof.MlDsa.X86_64.SignScrub.preparedSign44_scrubbed v
    spSafe := Proof.MlDsa.X86_64.SignScrub.preparedSign44_spSafe v },
  (Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Fn.signEntry v.level (Proof.MlDsa.signWithCacheName "mldsa65" ++ v.code.sfx) (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa65 1
    verified := Proof.MlDsa.X86_64.SignScrub.preparedSign65_scrubbed v
    spSafe := Proof.MlDsa.X86_64.SignScrub.preparedSign65_spSafe v },
  (Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Fn.signEntry v.level (Proof.MlDsa.signWithCacheName "mldsa87" ++ v.code.sfx) (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa87 1
    verified := Proof.MlDsa.X86_64.SignScrub.preparedSign87_scrubbed v
    spSafe := Proof.MlDsa.X86_64.SignScrub.preparedSign87_spSafe v }]

def artifacts : List Artifact :=
  VG.Proof.Variants.MlDsaArith.X86_64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.MlDsa.X86_64.Sign

-- ML-DSA (FIPS 204) on x86-64: signing messages
namespace VG.Artifacts.MlDsa.X86_64.SignMessage

open VG
open VG.Proof.MlDsa.X86_64 (ArithImpl)

def artifactsFor (v : ArithImpl) : List Artifact := [
  Spec.MlDsa.signMessage44Api.artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Fn.signMessage v.level (Proof.MlDsa.signWithCacheName "mldsa44" ++ v.code.sfx) (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa44 0
    verified := Proof.MlDsa.X86_64.SignScrub.signMessage44_scrubbed v
    spSafe := Proof.MlDsa.X86_64.SignScrub.signMessage44_spSafe v },
  Spec.MlDsa.signMessage65Api.artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Fn.signMessage v.level (Proof.MlDsa.signWithCacheName "mldsa65" ++ v.code.sfx) (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa65 0
    verified := Proof.MlDsa.X86_64.SignScrub.signMessage65_scrubbed v
    spSafe := Proof.MlDsa.X86_64.SignScrub.signMessage65_spSafe v },
  Spec.MlDsa.signMessage87Api.artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Fn.signMessage v.level (Proof.MlDsa.signWithCacheName "mldsa87" ++ v.code.sfx) (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa87 0
    verified := Proof.MlDsa.X86_64.SignScrub.signMessage87_scrubbed v
    spSafe := Proof.MlDsa.X86_64.SignScrub.signMessage87_spSafe v },
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Fn.signMessage v.level (Proof.MlDsa.signWithCacheName "mldsa44" ++ v.code.sfx) (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa44 1
    verified := Proof.MlDsa.X86_64.SignScrub.preparedSignMessage44_scrubbed v
    spSafe := Proof.MlDsa.X86_64.SignScrub.preparedSignMessage44_spSafe v },
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Fn.signMessage v.level (Proof.MlDsa.signWithCacheName "mldsa65" ++ v.code.sfx) (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa65 1
    verified := Proof.MlDsa.X86_64.SignScrub.preparedSignMessage65_scrubbed v
    spSafe := Proof.MlDsa.X86_64.SignScrub.preparedSignMessage65_spSafe v },
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Fn.signMessage v.level (Proof.MlDsa.signWithCacheName "mldsa87" ++ v.code.sfx) (Proof.MlDsa.X86_64.Sign.primsWith v.code) Spec.MlDsa.mlDsa87 1
    verified := Proof.MlDsa.X86_64.SignScrub.preparedSignMessage87_scrubbed v
    spSafe := Proof.MlDsa.X86_64.SignScrub.preparedSignMessage87_spSafe v }]

def artifacts : List Artifact :=
  VG.Proof.Variants.MlDsaArith.X86_64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.MlDsa.X86_64.SignMessage

-- ML-DSA (FIPS 204) on x86-64: verification
namespace VG.Artifacts.MlDsa.X86_64.Verify

open VG
open VG.Proof.MlDsa.X86_64 (ArithImpl)

def artifactsFor (v : ArithImpl) : List Artifact := [
  Spec.MlDsa.verify44Api.artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Fn.verifyEntry v.level (Proof.MlDsa.verifyWithCacheName "mldsa44" ++ v.code.sfx) (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa44 0
    verified := Proof.MlDsa.X86_64.VerifyScrub.verify44_scrubbed v
    spSafe := Proof.MlDsa.X86_64.VerifyScrub.verify44_spSafe v },
  Spec.MlDsa.verify65Api.artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Fn.verifyEntry v.level (Proof.MlDsa.verifyWithCacheName "mldsa65" ++ v.code.sfx) (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa65 0
    verified := Proof.MlDsa.X86_64.VerifyScrub.verify65_scrubbed v
    spSafe := Proof.MlDsa.X86_64.VerifyScrub.verify65_spSafe v },
  Spec.MlDsa.verify87Api.artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Fn.verifyEntry v.level (Proof.MlDsa.verifyWithCacheName "mldsa87" ++ v.code.sfx) (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa87 0
    verified := Proof.MlDsa.X86_64.VerifyScrub.verify87_scrubbed v
    spSafe := Proof.MlDsa.X86_64.VerifyScrub.verify87_spSafe v },
  (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Fn.verifyEntry v.level (Proof.MlDsa.verifyWithCacheName "mldsa44" ++ v.code.sfx) (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa44 1
    verified := Proof.MlDsa.X86_64.VerifyScrub.preparedVerify44_scrubbed v
    spSafe := Proof.MlDsa.X86_64.VerifyScrub.preparedVerify44_spSafe v },
  (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Fn.verifyEntry v.level (Proof.MlDsa.verifyWithCacheName "mldsa65" ++ v.code.sfx) (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa65 1
    verified := Proof.MlDsa.X86_64.VerifyScrub.preparedVerify65_scrubbed v
    spSafe := Proof.MlDsa.X86_64.VerifyScrub.preparedVerify65_spSafe v },
  (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Fn.verifyEntry v.level (Proof.MlDsa.verifyWithCacheName "mldsa87" ++ v.code.sfx) (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa87 1
    verified := Proof.MlDsa.X86_64.VerifyScrub.preparedVerify87_scrubbed v
    spSafe := Proof.MlDsa.X86_64.VerifyScrub.preparedVerify87_spSafe v }]

def artifacts : List Artifact :=
  VG.Proof.Variants.MlDsaArith.X86_64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.MlDsa.X86_64.Verify

-- ML-DSA (FIPS 204) on x86-64: verifying messages
namespace VG.Artifacts.MlDsa.X86_64.VerifyMessageCached

open VG
open VG.Proof.MlDsa.X86_64 (ArithImpl)

def artifactsFor (v : ArithImpl) : List Artifact := [
  (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Fn.verifyMessage v.level (Proof.MlDsa.verifyWithCacheName "mldsa44" ++ v.code.sfx) (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa44 0
    verified := Proof.MlDsa.X86_64.VerifyScrub.verifyMessage44_scrubbed v
    spSafe := Proof.MlDsa.X86_64.VerifyScrub.verifyMessage44_spSafe v },
  (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Fn.verifyMessage v.level (Proof.MlDsa.verifyWithCacheName "mldsa65" ++ v.code.sfx) (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa65 0
    verified := Proof.MlDsa.X86_64.VerifyScrub.verifyMessage65_scrubbed v
    spSafe := Proof.MlDsa.X86_64.VerifyScrub.verifyMessage65_spSafe v },
  (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Fn.verifyMessage v.level (Proof.MlDsa.verifyWithCacheName "mldsa87" ++ v.code.sfx) (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa87 0
    verified := Proof.MlDsa.X86_64.VerifyScrub.verifyMessage87_scrubbed v
    spSafe := Proof.MlDsa.X86_64.VerifyScrub.verifyMessage87_spSafe v },
  (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Fn.verifyMessage v.level (Proof.MlDsa.verifyWithCacheName "mldsa44" ++ v.code.sfx) (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa44 1
    verified := Proof.MlDsa.X86_64.VerifyScrub.preparedVerifyMessage44_scrubbed v
    spSafe := Proof.MlDsa.X86_64.VerifyScrub.preparedVerifyMessage44_spSafe v },
  (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Fn.verifyMessage v.level (Proof.MlDsa.verifyWithCacheName "mldsa65" ++ v.code.sfx) (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa65 1
    verified := Proof.MlDsa.X86_64.VerifyScrub.preparedVerifyMessage65_scrubbed v
    spSafe := Proof.MlDsa.X86_64.VerifyScrub.preparedVerifyMessage65_spSafe v },
  (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Fn.verifyMessage v.level (Proof.MlDsa.verifyWithCacheName "mldsa87" ++ v.code.sfx) (Proof.MlDsa.X86_64.Verify.primsWith v.code) Spec.MlDsa.mlDsa87 1
    verified := Proof.MlDsa.X86_64.VerifyScrub.preparedVerifyMessage87_scrubbed v
    spSafe := Proof.MlDsa.X86_64.VerifyScrub.preparedVerifyMessage87_spSafe v }]

def artifacts : List Artifact :=
  VG.Proof.Variants.MlDsaArith.X86_64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.MlDsa.X86_64.VerifyMessageCached

namespace VG.Artifacts.MlDsa.X86_64

def artifacts : List Artifact :=
  KeyGen.artifacts ++
  [
    Spec.MlDsa.pkTr44Api.artifact X86_64.target { code := Impl.MlDsa.X86_64.Fn.pkTr Spec.MlDsa.mlDsa44, verified := Proof.MlDsa.X86_64.FnScrub.pkTr44_scrubbed, spSafe := Proof.MlDsa.X86_64.FnScrub.pkTr44_spSafe },
    Spec.MlDsa.pkTr65Api.artifact X86_64.target { code := Impl.MlDsa.X86_64.Fn.pkTr Spec.MlDsa.mlDsa65, verified := Proof.MlDsa.X86_64.FnScrub.pkTr65_scrubbed, spSafe := Proof.MlDsa.X86_64.FnScrub.pkTr65_spSafe },
    Spec.MlDsa.pkTr87Api.artifact X86_64.target { code := Impl.MlDsa.X86_64.Fn.pkTr Spec.MlDsa.mlDsa87, verified := Proof.MlDsa.X86_64.FnScrub.pkTr87_scrubbed, spSafe := Proof.MlDsa.X86_64.FnScrub.pkTr87_spSafe }] ++
  PreparedKey.artifacts ++
  Sign.artifacts ++
  SignMessage.artifacts ++
  Verify.artifacts ++
  VerifyMessageCached.artifacts

end VG.Artifacts.MlDsa.X86_64
