module

public import VerifiedGarbage.Proof.MlKem.X86.Scrub
public import VerifiedGarbage.Impl.MlKem.X86.Wipe
import VerifiedGarbage.Proof.Sha3.X86.Lit
public import VerifiedGarbage.Proof.MlKem.X86.AddSub
public import VerifiedGarbage.Proof.MlKem.X86.Cbd
public import VerifiedGarbage.Proof.MlKem.X86.CompressEncode
public import VerifiedGarbage.Proof.MlKem.X86.Decode12
public import VerifiedGarbage.Proof.MlKem.X86.DecodeDecompress
public import VerifiedGarbage.Proof.MlKem.X86.Encode12
public import VerifiedGarbage.Proof.MlKem.X86.Mul
public import VerifiedGarbage.Proof.MlKem.X86.NttInv
public import VerifiedGarbage.Proof.MlKem.X86.Sample
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.MlKem1024.X86.CompressEncode
public import VerifiedGarbage.Proof.MlKem1024.X86.DecodeDecompress

/-! # ML-KEM (FIPS 203) on x86 -/

@[expose] public section

namespace VG.Artifacts.MlKem.X86

def artifacts : List (Artifact X86.target) := [
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

end VG.Artifacts.MlKem.X86
