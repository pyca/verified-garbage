module

public import VerifiedGarbage.Proof.MlKem.PPC64LE.Scrub
public import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
public import VerifiedGarbage.Proof.MlKem.PPC64LE.Add
public import VerifiedGarbage.Proof.MlKem.PPC64LE.Ntt
public import VerifiedGarbage.Proof.MlKem.PPC64LE.NttInv
public import VerifiedGarbage.Proof.MlKem.PPC64LE.Mul
public import VerifiedGarbage.Proof.MlKem.PPC64LE.Cbd2
public import VerifiedGarbage.Proof.MlKem.PPC64LE.Encode12
public import VerifiedGarbage.Proof.MlKem.PPC64LE.Decode12
public import VerifiedGarbage.Proof.MlKem.PPC64LE.CheckEk
public import VerifiedGarbage.Proof.MlKem.PPC64LE.CompressEncode
public import VerifiedGarbage.Proof.MlKem.PPC64LE.DecodeDecompress
public import VerifiedGarbage.Proof.MlKem.PPC64LE.CallWipe
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.MlKem1024.PPC64LE.CheckEk
public import VerifiedGarbage.Proof.MlKem1024.PPC64LE.CompressEncode
public import VerifiedGarbage.Proof.MlKem1024.PPC64LE.Decompress

/-! # ML-KEM (FIPS 203) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.MlKem.PPC64LE

def artifacts : List Artifact := [
  Spec.MlKem.keyGenApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.Fn.keyGen
    verified := .scrubbed Proof.MlKem.PPC64LE.Scrub.keyGen_scrubbed },
  Spec.MlKem.encapsApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.Fn.encaps
    verified := .scrubbed Proof.MlKem.PPC64LE.Scrub.encaps_scrubbed },
  Spec.MlKem.encapsHApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.Fn.encapsH
    verified := .scrubbed Proof.MlKem.PPC64LE.Scrub.encapsH_scrubbed },
  Spec.MlKem.decapsApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.Fn.decaps
    verified := .scrubbed Proof.MlKem.PPC64LE.Scrub.decaps_scrubbed },
  Spec.MlKem.checkEkApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.Fn.checkEk
    verified := .scrubbed Proof.MlKem.PPC64LE.Scrub.checkEk_scrubbed },
  Spec.MlKem1024.checkEkApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.Fn.checkEk1024
    verified := .scrubbed Proof.MlKem.PPC64LE.Scrub.checkEk1024_scrubbed },
  Spec.MlKem1024.keyGenApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.Fn.keyGen1024
    verified := .scrubbed Proof.MlKem.PPC64LE.Scrub.keyGen1024_scrubbed },
  Spec.MlKem1024.encapsApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.Fn.encaps1024
    verified := .scrubbed Proof.MlKem.PPC64LE.Scrub.encaps1024_scrubbed },
  Spec.MlKem1024.encapsHApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.Fn.encapsH1024
    verified := .scrubbed Proof.MlKem.PPC64LE.Scrub.encapsH1024_scrubbed },
  Spec.MlKem1024.decapsApi.artifact PPC64LE.target {
    code := Impl.MlKem.PPC64LE.Fn.decaps1024
    verified := .scrubbed Proof.MlKem.PPC64LE.Scrub.decaps1024_scrubbed }]

end VG.Artifacts.MlKem.PPC64LE
