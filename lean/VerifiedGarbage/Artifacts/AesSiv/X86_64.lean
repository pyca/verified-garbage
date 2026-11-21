module

public import VerifiedGarbage.Proof.AesSiv.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Impl.AesCcm.X86_64
public import VerifiedGarbage.Impl.Gcm.X86_64
public import VerifiedGarbage.Impl.Gcm.X86_64.Pclmul
public import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
public import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
public import VerifiedGarbage.Proof.AesCcm.Mac
public import VerifiedGarbage.Proof.AesCcm.X86_64.Contract
public import VerifiedGarbage.Proof.AesSiv.Ctr32
public import VerifiedGarbage.Proof.AesSiv.X86_64.CmacOf
public import VerifiedGarbage.Proof.AesSiv.X86_64.Init
public import VerifiedGarbage.Proof.AesSiv.X86_64.Open
public import VerifiedGarbage.Proof.AesSiv.X86_64.XorBytes
public import VerifiedGarbage.Proof.Cmac.Dbl32
public import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.CmacAes.X86_64.Dbl
public import VerifiedGarbage.Proof.CmacAes.X86_64.UpdateCorrect
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegSetOrder
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86_64.Avx
public import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Sse
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Proof.Gcm.Spec
public import VerifiedGarbage.Proof.Gcm.Stream
public import VerifiedGarbage.Proof.Gcm.X86_64.Bits
public import VerifiedGarbage.Spec.Ccm.Contract
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Variants.AesCtr32.X86_64
public import VerifiedGarbage.Proof.Variants.CmacAesUpdate.X86_64

/-! # AES-SIV (RFC 5297) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.AesSiv.X86_64

open VG.Proof.AesSiv.X86_64

def artifacts : List Artifact :=
  (VG.Proof.Variants.AesCtr32.X86_64.variants.flatMap fun (v : Proof.Aes.X86_64.Ctr32Impl) => [
    Spec.Siv.initApi.artifact X86_64.target
      (match v.free with
      | some f => {
          suffix := v.suffix
          code := Impl.AesSiv.X86_64.Fn.initF v.level v.callee v.suffix
          verified := .scrubbed (Proof.AesSiv.X86_64.initF_scrubbed v f)
          spSafe := Proof.AesSiv.X86_64.initF_spSafeFn v }
      | none =>
        match v.small with
        | some g => {
          suffix := v.suffix
          code := Impl.AesSiv.X86_64.Fn.initS v.level v.expand v.callee v.suffix
          verified := .scrubbed (Proof.AesSiv.X86_64.initS_scrubbed v g)
          spSafe := Proof.AesSiv.X86_64.initS_spSafeFn v }
        | none => {
          suffix := v.suffix
          code := Impl.AesSiv.X86_64.Fn.init v.level v.expand v.callee v.suffix
          verified := .scrubbed (Proof.AesSiv.X86_64.init_scrubbed v)
          spSafe := Proof.AesSiv.X86_64.init_spSafeFn v })]) ++
  (VG.Proof.Variants.CmacAesUpdate.X86_64.variants.flatMap fun (v : Proof.CmacAes.X86_64.UpdateImpl) => [
    Spec.Siv.encryptApi.artifact X86_64.target
      (match v.free, v.ctr.free with
      | some f, some fc => {
          suffix := v.suffix
          code := Impl.AesSiv.X86_64.Fn.encryptF (v.level.join v.ctr.level) v.callee v.ctr.callee v.ctr.suffix
          verified := .scrubbed (Proof.AesSiv.X86_64.encryptF_scrubbed v f fc)
          spSafe := Proof.AesSiv.X86_64.encryptF_spSafeFn v }
      | none, some _ => {
          suffix := v.suffix
          code := Impl.AesSiv.X86_64.Fn.encrypt (v.level.join v.ctr.level) v.callee v.ctr.callee v.ctr.suffix
          verified := .scrubbed (Proof.AesSiv.X86_64.encrypt_scrubbed v)
          spSafe := Proof.AesSiv.X86_64.encrypt_spSafeFn v }
      | _, none =>
        match v.small, v.ctr.small with
        | some f, some fc => {
          suffix := v.suffix
          code := Impl.AesSiv.X86_64.Fn.encryptS (v.level.join v.ctr.level) v.callee v.ctr.callee v.ctr.suffix
          verified := .scrubbed (Proof.AesSiv.X86_64.encryptS_scrubbed v f fc)
          spSafe := Proof.AesSiv.X86_64.encryptS_spSafeFn v }
        | _, _ => {
          suffix := v.suffix
          code := Impl.AesSiv.X86_64.Fn.encrypt (v.level.join v.ctr.level) v.callee v.ctr.callee v.ctr.suffix
          verified := .scrubbed (Proof.AesSiv.X86_64.encrypt_scrubbed v)
          spSafe := Proof.AesSiv.X86_64.encrypt_spSafeFn v }),
    Spec.Siv.decryptApi.artifact X86_64.target
      (match v.free, v.ctr.free with
      | some f, some fc => {
          suffix := v.suffix
          code := Impl.AesSiv.X86_64.Fn.decryptF (v.level.join v.ctr.level) v.callee v.ctr.callee v.ctr.suffix
          verified := .scrubbed (Proof.AesSiv.X86_64.decryptF_scrubbed v f fc)
          spSafe := Proof.AesSiv.X86_64.decryptF_spSafeFn v }
      | none, some _ => {
          suffix := v.suffix
          code := Impl.AesSiv.X86_64.Fn.decrypt (v.level.join v.ctr.level) v.callee v.ctr.callee v.ctr.suffix
          verified := .scrubbed (Proof.AesSiv.X86_64.decrypt_scrubbed v)
          spSafe := Proof.AesSiv.X86_64.decrypt_spSafeFn v }
      | _, none =>
        match v.small, v.ctr.small with
        | some f, some fc => {
          suffix := v.suffix
          code := Impl.AesSiv.X86_64.Fn.decryptS (v.level.join v.ctr.level) v.callee v.ctr.callee v.ctr.suffix
          verified := .scrubbed (Proof.AesSiv.X86_64.decryptS_scrubbed v f fc)
          spSafe := Proof.AesSiv.X86_64.decryptS_spSafeFn v }
        | _, _ => {
          suffix := v.suffix
          code := Impl.AesSiv.X86_64.Fn.decrypt (v.level.join v.ctr.level) v.callee v.ctr.callee v.ctr.suffix
          verified := .scrubbed (Proof.AesSiv.X86_64.decrypt_scrubbed v)
          spSafe := Proof.AesSiv.X86_64.decrypt_spSafeFn v })])

end VG.Artifacts.AesSiv.X86_64
