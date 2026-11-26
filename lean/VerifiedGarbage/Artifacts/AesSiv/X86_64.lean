module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Siv.Contract
import VerifiedGarbage.Proof.AesSiv.X86_64.Frame
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.X86_64.Registration
import VerifiedGarbage.Impl.AesCcm.X86_64
import VerifiedGarbage.Impl.Gcm.X86_64
import VerifiedGarbage.Impl.Gcm.X86_64.Pclmul
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
import VerifiedGarbage.Proof.AesCcm.Mac
import VerifiedGarbage.Proof.AesCcm.X86_64.Contract
import VerifiedGarbage.Proof.AesSiv.Ctr32
import VerifiedGarbage.Proof.AesSiv.X86_64.CmacOf
import VerifiedGarbage.Proof.AesSiv.X86_64.Init
import VerifiedGarbage.Proof.AesSiv.X86_64.Open
import VerifiedGarbage.Proof.AesSiv.X86_64.XorBytes
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.CmacAes.X86_64.Dbl
import VerifiedGarbage.Proof.CmacAes.X86_64.UpdateCorrect
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Gcm.X86_64.Bits
import VerifiedGarbage.Spec.Ccm.Contract
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Variants.AesCtr32.X86_64
import VerifiedGarbage.Proof.Variants.CmacAesUpdate.X86_64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-SIV (RFC 5297) on x86-64 -/

namespace VG.Artifacts.AesSiv.X86_64

open VG.Proof.AesSiv.X86_64

public def artifacts : List (Artifact X86_64.target) :=
  (VG.Proof.Variants.AesCtr32.X86_64.variants.flatMap fun (v : Proof.Aes.X86_64.Ctr32Impl) => [
    Spec.Siv.initApi.artifact X86_64.target
      (match v.free with
      | some f => {
          suffix := v.suffix
          code := Impl.AesSiv.X86_64.Fn.initF v.level v.callee v.suffix
          verified := Proof.AesSiv.X86_64.initF_scrubbed v f
          spSafe := Proof.AesSiv.X86_64.initF_spSafeFn v }
      | none =>
        match v.small with
        | some g => {
          suffix := v.suffix
          code := Impl.AesSiv.X86_64.Fn.initS v.level v.expand v.callee v.suffix
          verified := Proof.AesSiv.X86_64.initS_scrubbed v g
          spSafe := Proof.AesSiv.X86_64.initS_spSafeFn v }
        | none => {
          suffix := v.suffix
          code := Impl.AesSiv.X86_64.Fn.init v.level v.expand v.callee v.suffix
          verified := Proof.AesSiv.X86_64.init_scrubbed v
          spSafe := Proof.AesSiv.X86_64.init_spSafeFn v })]) ++
  (VG.Proof.Variants.CmacAesUpdate.X86_64.variants.flatMap fun (v : Proof.CmacAes.X86_64.UpdateImpl) => [
    Spec.Siv.encryptApi.artifact X86_64.target
      (match v.free, v.ctr.free with
      | some f, some fc => {
          suffix := v.suffix
          code := Impl.AesSiv.X86_64.Fn.encryptF (v.level.join v.ctr.level) v.callee v.ctr.callee v.ctr.suffix
          verified := Proof.AesSiv.X86_64.encryptF_scrubbed v f fc
          spSafe := Proof.AesSiv.X86_64.encryptF_spSafeFn v }
      | none, some _ => {
          suffix := v.suffix
          code := Impl.AesSiv.X86_64.Fn.encrypt (v.level.join v.ctr.level) v.callee v.ctr.callee v.ctr.suffix
          verified := Proof.AesSiv.X86_64.encrypt_scrubbed v
          spSafe := Proof.AesSiv.X86_64.encrypt_spSafeFn v }
      | _, none =>
        match v.small, v.ctr.small with
        | some f, some fc => {
          suffix := v.suffix
          code := Impl.AesSiv.X86_64.Fn.encryptS (v.level.join v.ctr.level) v.callee v.ctr.callee v.ctr.suffix
          verified := Proof.AesSiv.X86_64.encryptS_scrubbed v f fc
          spSafe := Proof.AesSiv.X86_64.encryptS_spSafeFn v }
        | _, _ => {
          suffix := v.suffix
          code := Impl.AesSiv.X86_64.Fn.encrypt (v.level.join v.ctr.level) v.callee v.ctr.callee v.ctr.suffix
          verified := Proof.AesSiv.X86_64.encrypt_scrubbed v
          spSafe := Proof.AesSiv.X86_64.encrypt_spSafeFn v }),
    Spec.Siv.decryptApi.artifact X86_64.target
      (match v.free, v.ctr.free with
      | some f, some fc => {
          suffix := v.suffix
          code := Impl.AesSiv.X86_64.Fn.decryptF (v.level.join v.ctr.level) v.callee v.ctr.callee v.ctr.suffix
          verified := Proof.AesSiv.X86_64.decryptF_scrubbed v f fc
          spSafe := Proof.AesSiv.X86_64.decryptF_spSafeFn v }
      | none, some _ => {
          suffix := v.suffix
          code := Impl.AesSiv.X86_64.Fn.decrypt (v.level.join v.ctr.level) v.callee v.ctr.callee v.ctr.suffix
          verified := Proof.AesSiv.X86_64.decrypt_scrubbed v
          spSafe := Proof.AesSiv.X86_64.decrypt_spSafeFn v }
      | _, none =>
        match v.small, v.ctr.small with
        | some f, some fc => {
          suffix := v.suffix
          code := Impl.AesSiv.X86_64.Fn.decryptS (v.level.join v.ctr.level) v.callee v.ctr.callee v.ctr.suffix
          verified := Proof.AesSiv.X86_64.decryptS_scrubbed v f fc
          spSafe := Proof.AesSiv.X86_64.decryptS_spSafeFn v }
        | _, _ => {
          suffix := v.suffix
          code := Impl.AesSiv.X86_64.Fn.decrypt (v.level.join v.ctr.level) v.callee v.ctr.callee v.ctr.suffix
          verified := Proof.AesSiv.X86_64.decrypt_scrubbed v
          spSafe := Proof.AesSiv.X86_64.decrypt_spSafeFn v })])

spec_apis artifacts

end VG.Artifacts.AesSiv.X86_64
