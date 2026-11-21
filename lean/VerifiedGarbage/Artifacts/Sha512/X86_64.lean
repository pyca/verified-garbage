module

public import VerifiedGarbage.Impl.Sha512.X86_64.Fn
public import VerifiedGarbage.Proof.Sha512.X86_64.Shared
public import VerifiedGarbage.Proof.Sha512.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
public import VerifiedGarbage.Proof.Blake2.X86_64.Backend
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Proof.Blake2.Spec
public import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Init
public import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Verified
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegSetOrder
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Sha256.Stream
public import VerifiedGarbage.Proof.Variants.Blake2b.X86_64
public import VerifiedGarbage.Proof.Blake2.X86_64.BackendS
public import VerifiedGarbage.Proof.Variants.Blake2s.X86_64
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64

/-! # SHA-384, SHA-512, SHA-512/224 and SHA-512/256 (FIPS 180-4) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Sha512.X86_64

def artifacts : List Artifact := [
  Spec.Sha512.init384Api.artifact X86_64.target { code := Impl.Sha512.X86_64.Fn.init384, verified := Proof.Sha512.X86_64.init384_scrubbed, spSafe := Proof.Sha512.X86_64.init384_spSafe },
  Spec.Sha512.init512Api.artifact X86_64.target { code := Impl.Sha512.X86_64.Fn.init512, verified := Proof.Sha512.X86_64.init512_scrubbed, spSafe := Proof.Sha512.X86_64.init512_spSafe },
  Spec.Sha512.init512_224Api.artifact X86_64.target { code := Impl.Sha512.X86_64.Fn.init512_224, verified := Proof.Sha512.X86_64.init512_224_scrubbed, spSafe := Proof.Sha512.X86_64.init512_224_spSafe },
  Spec.Sha512.init512_256Api.artifact X86_64.target { code := Impl.Sha512.X86_64.Fn.init512_256, verified := Proof.Sha512.X86_64.init512_256_scrubbed, spSafe := Proof.Sha512.X86_64.init512_256_spSafe }] ++
  (VG.Proof.Variants.MdHash.X86_64.sha384Streams.flatMap
      fun (s : Proof.Pbkdf2.Md.X86_64.StreamFns2 Spec.Sha512.finalize384Api Spec.Sha512.digest384Api) => [
      Spec.Sha512.finalize384Api.artifact X86_64.target {
        suffix := s.suffix
        code := Impl.Scrub.X86_64.scrubSel s.finalize.sel.level s.finalize.f.retBits s.finalize.f.stack s.finalize.sel.runs
          s.finalize.f.code
        verified := Proof.Pbkdf2.Md.X86_64.StreamFnS.scrubbed s.finalize
        spSafe := Proof.Pbkdf2.Md.X86_64.StreamFnS.spSafeFn s.finalize },
      Spec.Sha512.digest384Api.artifact X86_64.target {
        suffix := s.suffix
        code := Impl.Scrub.X86_64.scrubSel s.digest.sel.level s.digest.f.retBits s.digest.f.stack s.digest.sel.runs
          s.digest.f.code
        verified := Proof.Pbkdf2.Md.X86_64.StreamFnS.scrubbed s.digest
        spSafe := Proof.Pbkdf2.Md.X86_64.StreamFnS.spSafeFn s.digest }]) ++
  (VG.Proof.Variants.MdHash.X86_64.sha512Streams.flatMap
      fun (s : Proof.Pbkdf2.Md.X86_64.StreamFns Spec.Sha512.updateApi Spec.Sha512.finalizeApi Spec.Sha512.digest512Api) => [
      Spec.Sha512.updateApi.artifact X86_64.target {
        suffix := s.suffix
        code := Impl.Scrub.X86_64.scrubSel s.update.sel.level s.update.f.retBits s.update.f.stack s.update.sel.runs
          s.update.f.code
        verified := Proof.Pbkdf2.Md.X86_64.StreamFnS.scrubbed s.update
        spSafe := Proof.Pbkdf2.Md.X86_64.StreamFnS.spSafeFn s.update },
      Spec.Sha512.finalizeApi.artifact X86_64.target {
        suffix := s.suffix
        code := Impl.Scrub.X86_64.scrubSel s.finalize.sel.level s.finalize.f.retBits s.finalize.f.stack s.finalize.sel.runs
          s.finalize.f.code
        verified := Proof.Pbkdf2.Md.X86_64.StreamFnS.scrubbed s.finalize
        spSafe := Proof.Pbkdf2.Md.X86_64.StreamFnS.spSafeFn s.finalize },
      Spec.Sha512.digest512Api.artifact X86_64.target {
        suffix := s.suffix
        code := Impl.Scrub.X86_64.scrubSel s.digest.sel.level s.digest.f.retBits s.digest.f.stack s.digest.sel.runs
          s.digest.f.code
        verified := Proof.Pbkdf2.Md.X86_64.StreamFnS.scrubbed s.digest
        spSafe := Proof.Pbkdf2.Md.X86_64.StreamFnS.spSafeFn s.digest }]) ++
  (VG.Proof.Variants.MdHash.X86_64.sha512_224Streams.flatMap
      fun (s : Proof.Pbkdf2.Md.X86_64.StreamFns2 Spec.Sha512.finalize512_224Api Spec.Sha512.digest512_224Api) => [
      Spec.Sha512.finalize512_224Api.artifact X86_64.target {
        suffix := s.suffix
        code := Impl.Scrub.X86_64.scrubSel s.finalize.sel.level s.finalize.f.retBits s.finalize.f.stack s.finalize.sel.runs
          s.finalize.f.code
        verified := Proof.Pbkdf2.Md.X86_64.StreamFnS.scrubbed s.finalize
        spSafe := Proof.Pbkdf2.Md.X86_64.StreamFnS.spSafeFn s.finalize },
      Spec.Sha512.digest512_224Api.artifact X86_64.target {
        suffix := s.suffix
        code := Impl.Scrub.X86_64.scrubSel s.digest.sel.level s.digest.f.retBits s.digest.f.stack s.digest.sel.runs
          s.digest.f.code
        verified := Proof.Pbkdf2.Md.X86_64.StreamFnS.scrubbed s.digest
        spSafe := Proof.Pbkdf2.Md.X86_64.StreamFnS.spSafeFn s.digest }]) ++
  (VG.Proof.Variants.MdHash.X86_64.sha512_256Streams.flatMap
      fun (s : Proof.Pbkdf2.Md.X86_64.StreamFns2 Spec.Sha512.finalize512_256Api Spec.Sha512.digest512_256Api) => [
      Spec.Sha512.finalize512_256Api.artifact X86_64.target {
        suffix := s.suffix
        code := Impl.Scrub.X86_64.scrubSel s.finalize.sel.level s.finalize.f.retBits s.finalize.f.stack s.finalize.sel.runs
          s.finalize.f.code
        verified := Proof.Pbkdf2.Md.X86_64.StreamFnS.scrubbed s.finalize
        spSafe := Proof.Pbkdf2.Md.X86_64.StreamFnS.spSafeFn s.finalize },
      Spec.Sha512.digest512_256Api.artifact X86_64.target {
        suffix := s.suffix
        code := Impl.Scrub.X86_64.scrubSel s.digest.sel.level s.digest.f.retBits s.digest.f.stack s.digest.sel.runs
          s.digest.f.code
        verified := Proof.Pbkdf2.Md.X86_64.StreamFnS.scrubbed s.digest
        spSafe := Proof.Pbkdf2.Md.X86_64.StreamFnS.spSafeFn s.digest }])

end VG.Artifacts.Sha512.X86_64
