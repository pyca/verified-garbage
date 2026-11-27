module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sha256.Contract
import VerifiedGarbage.Impl.Sha256.X86_64.Fn
import VerifiedGarbage.Proof.Sha256.X86_64.Shared
import VerifiedGarbage.Proof.Sha256.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sha256.X86_64.Avx2.Lit
import VerifiedGarbage.Proof.Sha256.X86_64.Lit
import VerifiedGarbage.Proof.Blake2.X86_64.Backend
import VerifiedGarbage.Proof.Framework.X86_64.Registration
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Blake2.Spec
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Init
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Verified
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Variants.Blake2b.X86_64
import VerifiedGarbage.Proof.Blake2.X86_64.BackendS
import VerifiedGarbage.Proof.Variants.Blake2s.X86_64
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
import VerifiedGarbage.Proof.Variants.MdHash.X86_64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SHA-256 (FIPS 180-4) on x86-64 -/

namespace VG.Artifacts.Sha256.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Sha256.init224Api.artifact X86_64.target { code := Impl.Sha256.X86_64.Fn.init224, verified := Proof.Sha256.X86_64.init224_scrubbed, spSafe := Proof.Sha256.X86_64.init224_spSafe },
  Spec.Sha256.initApi.artifact X86_64.target { code := Impl.Sha256.X86_64.Fn.init, verified := Proof.Sha256.X86_64.init_scrubbed, spSafe := Proof.Sha256.X86_64.init_spSafe }] ++
  (VG.Proof.Variants.MdHash.X86_64.sha224Streams.flatMap
      fun (s : Proof.Pbkdf2.Md.X86_64.StreamFns2 Spec.Sha256.finalize224Api Spec.Sha256.digest224Api) => [
      Spec.Sha256.finalize224Api.artifact X86_64.target {
        suffix := s.suffix
        code := Impl.Scrub.X86_64.scrubSel s.finalize.sel.level s.finalize.f.retBits s.finalize.f.stack s.finalize.sel.runs
          s.finalize.f.code
        verified := Proof.Pbkdf2.Md.X86_64.StreamFnS.scrubbed s.finalize
        spSafe := Proof.Pbkdf2.Md.X86_64.StreamFnS.spSafeFn s.finalize },
      Spec.Sha256.digest224Api.artifact X86_64.target {
        suffix := s.suffix
        code := Impl.Scrub.X86_64.scrubSel s.digest.sel.level s.digest.f.retBits s.digest.f.stack s.digest.sel.runs
          s.digest.f.code
        verified := Proof.Pbkdf2.Md.X86_64.StreamFnS.scrubbed s.digest
        spSafe := Proof.Pbkdf2.Md.X86_64.StreamFnS.spSafeFn s.digest }]) ++
  (VG.Proof.Variants.MdHash.X86_64.sha256Streams.flatMap
      fun (s : Proof.Pbkdf2.Md.X86_64.StreamFns Spec.Sha256.updateApi Spec.Sha256.finalizeApi Spec.Sha256.digest256Api) => [
      Spec.Sha256.updateApi.artifact X86_64.target {
        suffix := s.suffix
        code := Impl.Scrub.X86_64.scrubSel s.update.sel.level s.update.f.retBits s.update.f.stack s.update.sel.runs
          s.update.f.code
        verified := Proof.Pbkdf2.Md.X86_64.StreamFnS.scrubbed s.update
        spSafe := Proof.Pbkdf2.Md.X86_64.StreamFnS.spSafeFn s.update },
      Spec.Sha256.finalizeApi.artifact X86_64.target {
        suffix := s.suffix
        code := Impl.Scrub.X86_64.scrubSel s.finalize.sel.level s.finalize.f.retBits s.finalize.f.stack s.finalize.sel.runs
          s.finalize.f.code
        verified := Proof.Pbkdf2.Md.X86_64.StreamFnS.scrubbed s.finalize
        spSafe := Proof.Pbkdf2.Md.X86_64.StreamFnS.spSafeFn s.finalize },
      Spec.Sha256.digest256Api.artifact X86_64.target {
        suffix := s.suffix
        code := Impl.Scrub.X86_64.scrubSel s.digest.sel.level s.digest.f.retBits s.digest.f.stack s.digest.sel.runs
          s.digest.f.code
        verified := Proof.Pbkdf2.Md.X86_64.StreamFnS.scrubbed s.digest
        spSafe := Proof.Pbkdf2.Md.X86_64.StreamFnS.spSafeFn s.digest }])

spec_apis artifacts

end VG.Artifacts.Sha256.X86_64
