module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Hmac.Generic
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.ScrubStream
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Impl.Pbkdf2.Md.X86_64.Fn
import VerifiedGarbage.Proof.Framework.X86_64.Registration
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.Cold
import VerifiedGarbage.Proof.Framework.EntryBranch
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
import VerifiedGarbage.Proof.Hmac.AnyKey
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.MdStream.X86_64.Words
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.AnyKeyEntry
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PadW
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Words
import VerifiedGarbage.Proof.Pbkdf2.Scratch
import VerifiedGarbage.Proof.Sha256.X86_64.Compress
import VerifiedGarbage.Proof.Sha512.X86_64.Wide
import VerifiedGarbage.Proof.Variants.MdHash.X86_64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # HMAC-SHA-224 (RFC 2104) on x86-64 -/

namespace VG.Artifacts.HmacSha224.X86_64

public def artifacts : List (Artifact X86_64.target) :=
  (VG.Proof.Variants.MdHash.X86_64.sha224Inits.map fun (v : Proof.Pbkdf2.Md.X86_64.InitImpl Spec.Hmac.sha224I) =>
    Spec.Hmac.sha224I.initAnyKeyApi.artifact X86_64.target {
      suffix := v.suffix
      extra := v.extra
      code := Impl.Pbkdf2.Md.X86_64.Fn.hmacInit v.level Spec.Hmac.sha224I.S.H.blockSize v.H
      verified := Proof.Pbkdf2.Md.X86_64.InitImpl.scrubbed v
      spSafe := Proof.Pbkdf2.Md.X86_64.InitImpl.spSafe v }) ++
  (VG.Proof.Variants.MdHash.X86_64.sha224Fins.map fun (f : Proof.Pbkdf2.Md.X86_64.FinImpl) =>
    f.v.I.finalizeApi.artifact X86_64.target {
      suffix := f.v.suffix
      code := Impl.Pbkdf2.Md.X86_64.Fn.hmacFinalize f.sel.level f.sel.runs f.v.H
      verified := Proof.Pbkdf2.Md.X86_64.FinImpl.scrubbed f
      spSafe := Proof.Pbkdf2.Md.X86_64.FinImpl.spSafeFn f })

spec_apis artifacts

end VG.Artifacts.HmacSha224.X86_64
