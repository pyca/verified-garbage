module

public import VerifiedGarbage.Impl.Sha1.X86_64.Fn
public import VerifiedGarbage.Proof.Sha1.X86_64.Shared
public import VerifiedGarbage.Proof.Sha1.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
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

/-! # SHA-1 (FIPS 180-4) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Sha1.X86_64

def artifacts : List Artifact := [
  Spec.Sha1.initApi.artifact X86_64.target { code := Impl.Sha1.X86_64.Fn.init, verified := Proof.Sha1.X86_64.init_scrubbed, spSafe := Proof.Sha1.X86_64.init_spSafe }] ++
  (VG.Proof.Variants.MdHash.X86_64.sha1Streams.flatMap
      fun (s : Proof.Pbkdf2.Md.X86_64.StreamFns Spec.Sha1.updateApi Spec.Sha1.finalizeApi Spec.Sha1.digestApi) => [
      Spec.Sha1.updateApi.artifact X86_64.target {
        suffix := s.suffix
        code := Impl.Scrub.X86_64.scrubSel s.update.sel.level s.update.f.retBits s.update.f.stack s.update.sel.runs
          s.update.f.code
        verified := Proof.Pbkdf2.Md.X86_64.StreamFnS.scrubbed s.update
        spSafe := Proof.Pbkdf2.Md.X86_64.StreamFnS.spSafeFn s.update },
      Spec.Sha1.finalizeApi.artifact X86_64.target {
        suffix := s.suffix
        code := Impl.Scrub.X86_64.scrubSel s.finalize.sel.level s.finalize.f.retBits s.finalize.f.stack s.finalize.sel.runs
          s.finalize.f.code
        verified := Proof.Pbkdf2.Md.X86_64.StreamFnS.scrubbed s.finalize
        spSafe := Proof.Pbkdf2.Md.X86_64.StreamFnS.spSafeFn s.finalize },
      Spec.Sha1.digestApi.artifact X86_64.target {
        suffix := s.suffix
        code := Impl.Scrub.X86_64.scrubSel s.digest.sel.level s.digest.f.retBits s.digest.f.stack s.digest.sel.runs
          s.digest.f.code
        verified := Proof.Pbkdf2.Md.X86_64.StreamFnS.scrubbed s.digest
        spSafe := Proof.Pbkdf2.Md.X86_64.StreamFnS.spSafeFn s.digest }])

end VG.Artifacts.Sha1.X86_64
