module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.SlhDsa.Contract
import VerifiedGarbage.Impl.SlhDsa.X86_64.Fn
import VerifiedGarbage.Proof.SlhDsa.X86_64.ScrubKeyGen
import VerifiedGarbage.Proof.SlhDsa.X86_64.ScrubSign
import VerifiedGarbage.Proof.SlhDsa.X86_64.ScrubVerify
import VerifiedGarbage.Proof.Variants.SlhDsaThash4.X86_64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SLH-DSA (FIPS 205) with SHAKE on x86-64 -/

namespace VG.Artifacts.SlhDsaShake.X86_64

open VG
open VG.Proof.SlhDsa.X86_64 (Thash4Impl)

def artifacts16 (T : Thash4Impl 16) : List (Artifact X86_64.target) := [
  Spec.SlhDsa.keyGenShake_128sApi.artifact X86_64.target {
    suffix := T.sfx
    code := Impl.SlhDsa.X86_64.Fn.keyGen T.level Spec.SlhDsa.shake_128s (Proof.SlhDsa.X86_64.KeyGen.fnsOf Spec.SlhDsa.shake_128s T "128s")
    verified := Proof.SlhDsa.X86_64.KeyGen.keyGen128s_scrubbed T
    spSafe := Proof.SlhDsa.X86_64.KeyGen.keyGen128s_spSafe T },
  Spec.SlhDsa.signShake_128sApi.artifact X86_64.target {
    suffix := T.sfx
    code := Impl.SlhDsa.X86_64.Fn.sign T.level Spec.SlhDsa.shake_128s (Proof.SlhDsa.X86_64.KeyGen.fnsOf Spec.SlhDsa.shake_128s T "128s")
    verified := Proof.SlhDsa.X86_64.SignTop.sign128s_scrubbed T
    spSafe := Proof.SlhDsa.X86_64.SignTop.sign128s_spSafe T },
  Spec.SlhDsa.verifyShake_128sApi.artifact X86_64.target {
    suffix := T.sfx
    code := Impl.SlhDsa.X86_64.Fn.verify T.level Spec.SlhDsa.shake_128s (Proof.SlhDsa.X86_64.KeyGen.fnsOf Spec.SlhDsa.shake_128s T "128s") (Proof.SlhDsa.X86_64.VerifyTop.vfnsOf T "128s")
    verified := Proof.SlhDsa.X86_64.VerifyTop.verify128s_scrubbed T
    spSafe := Proof.SlhDsa.X86_64.VerifyTop.verify128s_spSafe T },
  Spec.SlhDsa.keyGenShake_128fApi.artifact X86_64.target {
    suffix := T.sfx
    code := Impl.SlhDsa.X86_64.Fn.keyGen T.level Spec.SlhDsa.shake_128f (Proof.SlhDsa.X86_64.KeyGen.fnsOf Spec.SlhDsa.shake_128f T "128f")
    verified := Proof.SlhDsa.X86_64.KeyGen.keyGen128f_scrubbed T
    spSafe := Proof.SlhDsa.X86_64.KeyGen.keyGen128f_spSafe T },
  Spec.SlhDsa.signShake_128fApi.artifact X86_64.target {
    suffix := T.sfx
    code := Impl.SlhDsa.X86_64.Fn.sign T.level Spec.SlhDsa.shake_128f (Proof.SlhDsa.X86_64.KeyGen.fnsOf Spec.SlhDsa.shake_128f T "128f")
    verified := Proof.SlhDsa.X86_64.SignTop.sign128f_scrubbed T
    spSafe := Proof.SlhDsa.X86_64.SignTop.sign128f_spSafe T },
  Spec.SlhDsa.verifyShake_128fApi.artifact X86_64.target {
    suffix := T.sfx
    code := Impl.SlhDsa.X86_64.Fn.verify T.level Spec.SlhDsa.shake_128f (Proof.SlhDsa.X86_64.KeyGen.fnsOf Spec.SlhDsa.shake_128f T "128f") (Proof.SlhDsa.X86_64.VerifyTop.vfnsOf T "128f")
    verified := Proof.SlhDsa.X86_64.VerifyTop.verify128f_scrubbed T
    spSafe := Proof.SlhDsa.X86_64.VerifyTop.verify128f_spSafe T }]

def artifacts24 (T : Thash4Impl 24) : List (Artifact X86_64.target) := [
  Spec.SlhDsa.keyGenShake_192sApi.artifact X86_64.target {
    suffix := T.sfx
    code := Impl.SlhDsa.X86_64.Fn.keyGen T.level Spec.SlhDsa.shake_192s (Proof.SlhDsa.X86_64.KeyGen.fnsOf Spec.SlhDsa.shake_192s T "192s")
    verified := Proof.SlhDsa.X86_64.KeyGen.keyGen192s_scrubbed T
    spSafe := Proof.SlhDsa.X86_64.KeyGen.keyGen192s_spSafe T },
  Spec.SlhDsa.signShake_192sApi.artifact X86_64.target {
    suffix := T.sfx
    code := Impl.SlhDsa.X86_64.Fn.sign T.level Spec.SlhDsa.shake_192s (Proof.SlhDsa.X86_64.KeyGen.fnsOf Spec.SlhDsa.shake_192s T "192s")
    verified := Proof.SlhDsa.X86_64.SignTop.sign192s_scrubbed T
    spSafe := Proof.SlhDsa.X86_64.SignTop.sign192s_spSafe T },
  Spec.SlhDsa.verifyShake_192sApi.artifact X86_64.target {
    suffix := T.sfx
    code := Impl.SlhDsa.X86_64.Fn.verify T.level Spec.SlhDsa.shake_192s (Proof.SlhDsa.X86_64.KeyGen.fnsOf Spec.SlhDsa.shake_192s T "192s") (Proof.SlhDsa.X86_64.VerifyTop.vfnsOf T "192s")
    verified := Proof.SlhDsa.X86_64.VerifyTop.verify192s_scrubbed T
    spSafe := Proof.SlhDsa.X86_64.VerifyTop.verify192s_spSafe T },
  Spec.SlhDsa.keyGenShake_192fApi.artifact X86_64.target {
    suffix := T.sfx
    code := Impl.SlhDsa.X86_64.Fn.keyGen T.level Spec.SlhDsa.shake_192f (Proof.SlhDsa.X86_64.KeyGen.fnsOf Spec.SlhDsa.shake_192f T "192f")
    verified := Proof.SlhDsa.X86_64.KeyGen.keyGen192f_scrubbed T
    spSafe := Proof.SlhDsa.X86_64.KeyGen.keyGen192f_spSafe T },
  Spec.SlhDsa.signShake_192fApi.artifact X86_64.target {
    suffix := T.sfx
    code := Impl.SlhDsa.X86_64.Fn.sign T.level Spec.SlhDsa.shake_192f (Proof.SlhDsa.X86_64.KeyGen.fnsOf Spec.SlhDsa.shake_192f T "192f")
    verified := Proof.SlhDsa.X86_64.SignTop.sign192f_scrubbed T
    spSafe := Proof.SlhDsa.X86_64.SignTop.sign192f_spSafe T },
  Spec.SlhDsa.verifyShake_192fApi.artifact X86_64.target {
    suffix := T.sfx
    code := Impl.SlhDsa.X86_64.Fn.verify T.level Spec.SlhDsa.shake_192f (Proof.SlhDsa.X86_64.KeyGen.fnsOf Spec.SlhDsa.shake_192f T "192f") (Proof.SlhDsa.X86_64.VerifyTop.vfnsOf T "192f")
    verified := Proof.SlhDsa.X86_64.VerifyTop.verify192f_scrubbed T
    spSafe := Proof.SlhDsa.X86_64.VerifyTop.verify192f_spSafe T }]

def artifacts32 (T : Thash4Impl 32) : List (Artifact X86_64.target) := [
  Spec.SlhDsa.keyGenShake_256sApi.artifact X86_64.target {
    suffix := T.sfx
    code := Impl.SlhDsa.X86_64.Fn.keyGen T.level Spec.SlhDsa.shake_256s (Proof.SlhDsa.X86_64.KeyGen.fnsOf Spec.SlhDsa.shake_256s T "256s")
    verified := Proof.SlhDsa.X86_64.KeyGen.keyGen256s_scrubbed T
    spSafe := Proof.SlhDsa.X86_64.KeyGen.keyGen256s_spSafe T },
  Spec.SlhDsa.signShake_256sApi.artifact X86_64.target {
    suffix := T.sfx
    code := Impl.SlhDsa.X86_64.Fn.sign T.level Spec.SlhDsa.shake_256s (Proof.SlhDsa.X86_64.KeyGen.fnsOf Spec.SlhDsa.shake_256s T "256s")
    verified := Proof.SlhDsa.X86_64.SignTop.sign256s_scrubbed T
    spSafe := Proof.SlhDsa.X86_64.SignTop.sign256s_spSafe T },
  Spec.SlhDsa.verifyShake_256sApi.artifact X86_64.target {
    suffix := T.sfx
    code := Impl.SlhDsa.X86_64.Fn.verify T.level Spec.SlhDsa.shake_256s (Proof.SlhDsa.X86_64.KeyGen.fnsOf Spec.SlhDsa.shake_256s T "256s") (Proof.SlhDsa.X86_64.VerifyTop.vfnsOf T "256s")
    verified := Proof.SlhDsa.X86_64.VerifyTop.verify256s_scrubbed T
    spSafe := Proof.SlhDsa.X86_64.VerifyTop.verify256s_spSafe T },
  Spec.SlhDsa.keyGenShake_256fApi.artifact X86_64.target {
    suffix := T.sfx
    code := Impl.SlhDsa.X86_64.Fn.keyGen T.level Spec.SlhDsa.shake_256f (Proof.SlhDsa.X86_64.KeyGen.fnsOf Spec.SlhDsa.shake_256f T "256f")
    verified := Proof.SlhDsa.X86_64.KeyGen.keyGen256f_scrubbed T
    spSafe := Proof.SlhDsa.X86_64.KeyGen.keyGen256f_spSafe T },
  Spec.SlhDsa.signShake_256fApi.artifact X86_64.target {
    suffix := T.sfx
    code := Impl.SlhDsa.X86_64.Fn.sign T.level Spec.SlhDsa.shake_256f (Proof.SlhDsa.X86_64.KeyGen.fnsOf Spec.SlhDsa.shake_256f T "256f")
    verified := Proof.SlhDsa.X86_64.SignTop.sign256f_scrubbed T
    spSafe := Proof.SlhDsa.X86_64.SignTop.sign256f_spSafe T },
  Spec.SlhDsa.verifyShake_256fApi.artifact X86_64.target {
    suffix := T.sfx
    code := Impl.SlhDsa.X86_64.Fn.verify T.level Spec.SlhDsa.shake_256f (Proof.SlhDsa.X86_64.KeyGen.fnsOf Spec.SlhDsa.shake_256f T "256f") (Proof.SlhDsa.X86_64.VerifyTop.vfnsOf T "256f")
    verified := Proof.SlhDsa.X86_64.VerifyTop.verify256f_scrubbed T
    spSafe := Proof.SlhDsa.X86_64.VerifyTop.verify256f_spSafe T }]

public def artifacts : List (Artifact X86_64.target) :=
  Proof.Variants.SlhDsaThash4.X86_64.variants16.flatMap artifacts16 ++
  Proof.Variants.SlhDsaThash4.X86_64.variants24.flatMap artifacts24 ++
  Proof.Variants.SlhDsaThash4.X86_64.variants32.flatMap artifacts32

spec_apis artifacts

end VG.Artifacts.SlhDsaShake.X86_64
