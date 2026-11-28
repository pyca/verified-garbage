module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.SlhDsa.Contract
import VerifiedGarbage.Impl.SlhDsa.AArch64.Fn
import VerifiedGarbage.Proof.SlhDsa.AArch64.ScrubKeyGen
import VerifiedGarbage.Proof.SlhDsa.AArch64.ScrubSign
import VerifiedGarbage.Proof.SlhDsa.AArch64.ScrubVerify
import VerifiedGarbage.Proof.Variants.SlhDsaThash4.AArch64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SLH-DSA (FIPS 205) with SHAKE on AArch64 -/

namespace VG.Artifacts.SlhDsaShake.AArch64

open VG
open VG.Proof.SlhDsa.AArch64 (Thash4Impl)

def artifacts16 (T : Thash4Impl 16) : List (Artifact AArch64.target) := [
  Spec.SlhDsa.keyGenShake_128sApi.artifact AArch64.target {
    suffix := T.sfx
    code := Impl.SlhDsa.AArch64.Fn.keyGen Spec.SlhDsa.shake_128s (Proof.SlhDsa.AArch64.KeyGen.fnsOf Spec.SlhDsa.shake_128s T "128s")
    verified := Proof.SlhDsa.AArch64.KeyGen.keyGen128s_scrubbed T
    spSafe := Proof.SlhDsa.AArch64.KeyGen.keyGen128s_spSafe T },
  Spec.SlhDsa.signShake_128sApi.artifact AArch64.target {
    suffix := T.sfx
    code := Impl.SlhDsa.AArch64.Fn.sign Spec.SlhDsa.shake_128s (Proof.SlhDsa.AArch64.KeyGen.fnsOf Spec.SlhDsa.shake_128s T "128s")
    verified := Proof.SlhDsa.AArch64.Sign.sign128s_scrubbed T
    spSafe := Proof.SlhDsa.AArch64.Sign.sign128s_spSafe T },
  Spec.SlhDsa.verifyShake_128sApi.artifact AArch64.target {
    suffix := T.sfx
    code := Impl.SlhDsa.AArch64.Fn.verify Spec.SlhDsa.shake_128s (Proof.SlhDsa.AArch64.KeyGen.fnsOf Spec.SlhDsa.shake_128s T "128s") (Proof.SlhDsa.AArch64.VerifyTop.vfnsOf T "128s")
    verified := Proof.SlhDsa.AArch64.VerifyTop.verify128s_scrubbed T
    spSafe := Proof.SlhDsa.AArch64.VerifyTop.verify128s_spSafe T },
  Spec.SlhDsa.keyGenShake_128fApi.artifact AArch64.target {
    suffix := T.sfx
    code := Impl.SlhDsa.AArch64.Fn.keyGen Spec.SlhDsa.shake_128f (Proof.SlhDsa.AArch64.KeyGen.fnsOf Spec.SlhDsa.shake_128f T "128f")
    verified := Proof.SlhDsa.AArch64.KeyGen.keyGen128f_scrubbed T
    spSafe := Proof.SlhDsa.AArch64.KeyGen.keyGen128f_spSafe T },
  Spec.SlhDsa.signShake_128fApi.artifact AArch64.target {
    suffix := T.sfx
    code := Impl.SlhDsa.AArch64.Fn.sign Spec.SlhDsa.shake_128f (Proof.SlhDsa.AArch64.KeyGen.fnsOf Spec.SlhDsa.shake_128f T "128f")
    verified := Proof.SlhDsa.AArch64.Sign.sign128f_scrubbed T
    spSafe := Proof.SlhDsa.AArch64.Sign.sign128f_spSafe T },
  Spec.SlhDsa.verifyShake_128fApi.artifact AArch64.target {
    suffix := T.sfx
    code := Impl.SlhDsa.AArch64.Fn.verify Spec.SlhDsa.shake_128f (Proof.SlhDsa.AArch64.KeyGen.fnsOf Spec.SlhDsa.shake_128f T "128f") (Proof.SlhDsa.AArch64.VerifyTop.vfnsOf T "128f")
    verified := Proof.SlhDsa.AArch64.VerifyTop.verify128f_scrubbed T
    spSafe := Proof.SlhDsa.AArch64.VerifyTop.verify128f_spSafe T }]

def artifacts24 (T : Thash4Impl 24) : List (Artifact AArch64.target) := [
  Spec.SlhDsa.keyGenShake_192sApi.artifact AArch64.target {
    suffix := T.sfx
    code := Impl.SlhDsa.AArch64.Fn.keyGen Spec.SlhDsa.shake_192s (Proof.SlhDsa.AArch64.KeyGen.fnsOf Spec.SlhDsa.shake_192s T "192s")
    verified := Proof.SlhDsa.AArch64.KeyGen.keyGen192s_scrubbed T
    spSafe := Proof.SlhDsa.AArch64.KeyGen.keyGen192s_spSafe T },
  Spec.SlhDsa.signShake_192sApi.artifact AArch64.target {
    suffix := T.sfx
    code := Impl.SlhDsa.AArch64.Fn.sign Spec.SlhDsa.shake_192s (Proof.SlhDsa.AArch64.KeyGen.fnsOf Spec.SlhDsa.shake_192s T "192s")
    verified := Proof.SlhDsa.AArch64.Sign.sign192s_scrubbed T
    spSafe := Proof.SlhDsa.AArch64.Sign.sign192s_spSafe T },
  Spec.SlhDsa.verifyShake_192sApi.artifact AArch64.target {
    suffix := T.sfx
    code := Impl.SlhDsa.AArch64.Fn.verify Spec.SlhDsa.shake_192s (Proof.SlhDsa.AArch64.KeyGen.fnsOf Spec.SlhDsa.shake_192s T "192s") (Proof.SlhDsa.AArch64.VerifyTop.vfnsOf T "192s")
    verified := Proof.SlhDsa.AArch64.VerifyTop.verify192s_scrubbed T
    spSafe := Proof.SlhDsa.AArch64.VerifyTop.verify192s_spSafe T },
  Spec.SlhDsa.keyGenShake_192fApi.artifact AArch64.target {
    suffix := T.sfx
    code := Impl.SlhDsa.AArch64.Fn.keyGen Spec.SlhDsa.shake_192f (Proof.SlhDsa.AArch64.KeyGen.fnsOf Spec.SlhDsa.shake_192f T "192f")
    verified := Proof.SlhDsa.AArch64.KeyGen.keyGen192f_scrubbed T
    spSafe := Proof.SlhDsa.AArch64.KeyGen.keyGen192f_spSafe T },
  Spec.SlhDsa.signShake_192fApi.artifact AArch64.target {
    suffix := T.sfx
    code := Impl.SlhDsa.AArch64.Fn.sign Spec.SlhDsa.shake_192f (Proof.SlhDsa.AArch64.KeyGen.fnsOf Spec.SlhDsa.shake_192f T "192f")
    verified := Proof.SlhDsa.AArch64.Sign.sign192f_scrubbed T
    spSafe := Proof.SlhDsa.AArch64.Sign.sign192f_spSafe T },
  Spec.SlhDsa.verifyShake_192fApi.artifact AArch64.target {
    suffix := T.sfx
    code := Impl.SlhDsa.AArch64.Fn.verify Spec.SlhDsa.shake_192f (Proof.SlhDsa.AArch64.KeyGen.fnsOf Spec.SlhDsa.shake_192f T "192f") (Proof.SlhDsa.AArch64.VerifyTop.vfnsOf T "192f")
    verified := Proof.SlhDsa.AArch64.VerifyTop.verify192f_scrubbed T
    spSafe := Proof.SlhDsa.AArch64.VerifyTop.verify192f_spSafe T }]

def artifacts32 (T : Thash4Impl 32) : List (Artifact AArch64.target) := [
  Spec.SlhDsa.keyGenShake_256sApi.artifact AArch64.target {
    suffix := T.sfx
    code := Impl.SlhDsa.AArch64.Fn.keyGen Spec.SlhDsa.shake_256s (Proof.SlhDsa.AArch64.KeyGen.fnsOf Spec.SlhDsa.shake_256s T "256s")
    verified := Proof.SlhDsa.AArch64.KeyGen.keyGen256s_scrubbed T
    spSafe := Proof.SlhDsa.AArch64.KeyGen.keyGen256s_spSafe T },
  Spec.SlhDsa.signShake_256sApi.artifact AArch64.target {
    suffix := T.sfx
    code := Impl.SlhDsa.AArch64.Fn.sign Spec.SlhDsa.shake_256s (Proof.SlhDsa.AArch64.KeyGen.fnsOf Spec.SlhDsa.shake_256s T "256s")
    verified := Proof.SlhDsa.AArch64.Sign.sign256s_scrubbed T
    spSafe := Proof.SlhDsa.AArch64.Sign.sign256s_spSafe T },
  Spec.SlhDsa.verifyShake_256sApi.artifact AArch64.target {
    suffix := T.sfx
    code := Impl.SlhDsa.AArch64.Fn.verify Spec.SlhDsa.shake_256s (Proof.SlhDsa.AArch64.KeyGen.fnsOf Spec.SlhDsa.shake_256s T "256s") (Proof.SlhDsa.AArch64.VerifyTop.vfnsOf T "256s")
    verified := Proof.SlhDsa.AArch64.VerifyTop.verify256s_scrubbed T
    spSafe := Proof.SlhDsa.AArch64.VerifyTop.verify256s_spSafe T },
  Spec.SlhDsa.keyGenShake_256fApi.artifact AArch64.target {
    suffix := T.sfx
    code := Impl.SlhDsa.AArch64.Fn.keyGen Spec.SlhDsa.shake_256f (Proof.SlhDsa.AArch64.KeyGen.fnsOf Spec.SlhDsa.shake_256f T "256f")
    verified := Proof.SlhDsa.AArch64.KeyGen.keyGen256f_scrubbed T
    spSafe := Proof.SlhDsa.AArch64.KeyGen.keyGen256f_spSafe T },
  Spec.SlhDsa.signShake_256fApi.artifact AArch64.target {
    suffix := T.sfx
    code := Impl.SlhDsa.AArch64.Fn.sign Spec.SlhDsa.shake_256f (Proof.SlhDsa.AArch64.KeyGen.fnsOf Spec.SlhDsa.shake_256f T "256f")
    verified := Proof.SlhDsa.AArch64.Sign.sign256f_scrubbed T
    spSafe := Proof.SlhDsa.AArch64.Sign.sign256f_spSafe T },
  Spec.SlhDsa.verifyShake_256fApi.artifact AArch64.target {
    suffix := T.sfx
    code := Impl.SlhDsa.AArch64.Fn.verify Spec.SlhDsa.shake_256f (Proof.SlhDsa.AArch64.KeyGen.fnsOf Spec.SlhDsa.shake_256f T "256f") (Proof.SlhDsa.AArch64.VerifyTop.vfnsOf T "256f")
    verified := Proof.SlhDsa.AArch64.VerifyTop.verify256f_scrubbed T
    spSafe := Proof.SlhDsa.AArch64.VerifyTop.verify256f_spSafe T }]

public def artifacts : List (Artifact AArch64.target) :=
  Proof.Variants.SlhDsaThash4.AArch64.variants16.flatMap artifacts16 ++
  Proof.Variants.SlhDsaThash4.AArch64.variants24.flatMap artifacts24 ++
  Proof.Variants.SlhDsaThash4.AArch64.variants32.flatMap artifacts32

spec_apis artifacts

end VG.Artifacts.SlhDsaShake.AArch64
