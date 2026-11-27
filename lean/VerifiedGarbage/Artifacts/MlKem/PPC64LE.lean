module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.MlKem.Contract
public import VerifiedGarbage.Spec.MlKem.EncapsH
public import VerifiedGarbage.Spec.MlKem.Contract1024
import VerifiedGarbage.Proof.MlKem.PPC64LE.Scrub
import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
import VerifiedGarbage.Proof.MlKem.PPC64LE.Add
import VerifiedGarbage.Proof.MlKem.PPC64LE.Ntt
import VerifiedGarbage.Proof.MlKem.PPC64LE.NttInv
import VerifiedGarbage.Proof.MlKem.PPC64LE.Mul
import VerifiedGarbage.Proof.MlKem.PPC64LE.Cbd2
import VerifiedGarbage.Proof.MlKem.PPC64LE.Encode12
import VerifiedGarbage.Proof.MlKem.PPC64LE.Decode12
import VerifiedGarbage.Proof.MlKem.PPC64LE.CheckEk
import VerifiedGarbage.Proof.MlKem.PPC64LE.CompressEncode
import VerifiedGarbage.Proof.MlKem.PPC64LE.DecodeDecompress
import VerifiedGarbage.Proof.MlKem.PPC64LE.CallWipe
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.MlKem1024.PPC64LE.CheckEk
import VerifiedGarbage.Proof.MlKem1024.PPC64LE.CompressEncode
import VerifiedGarbage.Proof.MlKem1024.PPC64LE.Decompress
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ML-KEM (FIPS 203) on PPC64LE -/

namespace VG.Artifacts.MlKem.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.MlKem.keyGenApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.Fn.keyGen
    verified := Proof.MlKem.PPC64LE.Scrub.keyGen_scrubbed
    publicOutOk := Proof.MlKem.PPC64LE.Scrub.keyGen_public },
  Spec.MlKem.encapsApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.Fn.encaps
    verified := Proof.MlKem.PPC64LE.Scrub.encaps_scrubbed
    publicOutOk := Proof.MlKem.PPC64LE.Scrub.encaps_public },
  Spec.MlKem.encapsHApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.Fn.encapsH
    verified := Proof.MlKem.PPC64LE.Scrub.encapsH_scrubbed
    publicOutOk := Proof.MlKem.PPC64LE.Scrub.encapsH_public },
  Spec.MlKem.decapsApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.Fn.decaps
    verified := Proof.MlKem.PPC64LE.Scrub.decaps_scrubbed
    publicOutOk := Proof.MlKem.PPC64LE.Scrub.decaps_public },
  Spec.MlKem.checkEkApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.Fn.checkEk
    verified := Proof.MlKem.PPC64LE.Scrub.checkEk_scrubbed },
  Spec.MlKem1024.checkEkApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.Fn.checkEk1024
    verified := Proof.MlKem.PPC64LE.Scrub.checkEk1024_scrubbed },
  Spec.MlKem1024.keyGenApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.Fn.keyGen1024
    verified := Proof.MlKem.PPC64LE.Scrub.keyGen1024_scrubbed
    publicOutOk := Proof.MlKem.PPC64LE.Scrub.keyGen1024_public },
  Spec.MlKem1024.encapsApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.Fn.encaps1024
    verified := Proof.MlKem.PPC64LE.Scrub.encaps1024_scrubbed
    publicOutOk := Proof.MlKem.PPC64LE.Scrub.encaps1024_public },
  Spec.MlKem1024.encapsHApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.Fn.encapsH1024
    verified := Proof.MlKem.PPC64LE.Scrub.encapsH1024_scrubbed
    publicOutOk := Proof.MlKem.PPC64LE.Scrub.encapsH1024_public },
  Spec.MlKem1024.decapsApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.Fn.decaps1024
    verified := Proof.MlKem.PPC64LE.Scrub.decaps1024_scrubbed
    publicOutOk := Proof.MlKem.PPC64LE.Scrub.decaps1024_public }]

spec_apis artifacts

end VG.Artifacts.MlKem.PPC64LE
