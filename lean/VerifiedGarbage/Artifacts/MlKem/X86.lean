module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.MlKem.Contract
public import VerifiedGarbage.Spec.MlKem.EncapsH
public import VerifiedGarbage.Spec.MlKem.Contract1024
import VerifiedGarbage.Proof.MlKem.X86.Scrub
import VerifiedGarbage.Impl.MlKem.X86.Wipe
import VerifiedGarbage.Proof.Sha3.X86.Lit
import VerifiedGarbage.Proof.MlKem.X86.AddSub
import VerifiedGarbage.Proof.MlKem.X86.Cbd
import VerifiedGarbage.Proof.MlKem.X86.CompressEncode
import VerifiedGarbage.Proof.MlKem.X86.Decode12
import VerifiedGarbage.Proof.MlKem.X86.DecodeDecompress
import VerifiedGarbage.Proof.MlKem.X86.Encode12
import VerifiedGarbage.Proof.MlKem.X86.Mul
import VerifiedGarbage.Proof.MlKem.X86.NttInv
import VerifiedGarbage.Proof.MlKem.X86.Sample
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.MlKem1024.X86.CompressEncode
import VerifiedGarbage.Proof.MlKem1024.X86.DecodeDecompress
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ML-KEM (FIPS 203) on x86 -/

namespace VG.Artifacts.MlKem.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.MlKem.checkEkApi.artifact X86.target {
    code := Impl.MlKem.X86.Fn.checkEk
    verified := Proof.MlKem.X86.Scrub.checkEk_scrubbed },
  Spec.MlKem.keyGenApi.artifact X86.target {
    code := Impl.MlKem.X86.Fn.keyGen
    verified := Proof.MlKem.X86.Scrub.keyGen_scrubbed
    publicOutOk := Proof.MlKem.X86.Scrub.keyGen_public },
  Spec.MlKem.encapsApi.artifact X86.target {
    code := Impl.MlKem.X86.Fn.encaps
    verified := Proof.MlKem.X86.Scrub.encaps_scrubbed
    publicOutOk := Proof.MlKem.X86.Scrub.encaps_public },
  Spec.MlKem.encapsHApi.artifact X86.target {
    code := Impl.MlKem.X86.Fn.encapsH
    verified := Proof.MlKem.X86.Scrub.encapsH_scrubbed
    publicOutOk := Proof.MlKem.X86.Scrub.encapsH_public },
  Spec.MlKem.decapsApi.artifact X86.target {
    code := Impl.MlKem.X86.Fn.decaps
    verified := Proof.MlKem.X86.Scrub.decaps_scrubbed
    publicOutOk := Proof.MlKem.X86.Scrub.decaps_public },
  Spec.MlKem1024.checkEkApi.artifact X86.target {
    code := Impl.MlKem.X86.Fn.checkEk1024
    verified := Proof.MlKem.X86.Scrub.checkEk1024_scrubbed },
  Spec.MlKem1024.keyGenApi.artifact X86.target {
    code := Impl.MlKem.X86.Fn.keyGen1024
    verified := Proof.MlKem.X86.Scrub.keyGen1024_scrubbed
    publicOutOk := Proof.MlKem.X86.Scrub.keyGen1024_public },
  Spec.MlKem1024.encapsApi.artifact X86.target {
    code := Impl.MlKem.X86.Fn.encaps1024
    verified := Proof.MlKem.X86.Scrub.encaps1024_scrubbed
    publicOutOk := Proof.MlKem.X86.Scrub.encaps1024_public },
  Spec.MlKem1024.encapsHApi.artifact X86.target {
    code := Impl.MlKem.X86.Fn.encapsH1024
    verified := Proof.MlKem.X86.Scrub.encapsH1024_scrubbed
    publicOutOk := Proof.MlKem.X86.Scrub.encapsH1024_public },
  Spec.MlKem1024.decapsApi.artifact X86.target {
    code := Impl.MlKem.X86.Fn.decaps1024
    verified := Proof.MlKem.X86.Scrub.decaps1024_scrubbed
    publicOutOk := Proof.MlKem.X86.Scrub.decaps1024_public }]

spec_apis artifacts

end VG.Artifacts.MlKem.X86
