module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.ScrubStream
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Proof.Framework.Cold
public import VerifiedGarbage.Proof.Framework.EntryBranch
public import VerifiedGarbage.Proof.Framework.OffsetBelow
public import VerifiedGarbage.Proof.Framework.RegSetOrder
public import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Sse
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
public import VerifiedGarbage.Proof.Hmac.AnyKey
public import VerifiedGarbage.Proof.Hmac.Generic.Implies
public import VerifiedGarbage.Proof.MdStream.X86_64.Words
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.AnyKeyEntry
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PadW
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Words
public import VerifiedGarbage.Proof.Pbkdf2.Scratch
public import VerifiedGarbage.Proof.Sha256.X86_64.Compress
public import VerifiedGarbage.Proof.Sha512.X86_64.Wide
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64

/-! # HMAC-SHA-512 (RFC 2104) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.HmacSha512.X86_64

def artifacts : List Artifact :=
  VG.Proof.Variants.MdHash.X86_64.sha512Variants.flatMap fun (v : Proof.Pbkdf2.Md.X86_64.MdHash) =>
    v.I.initAnyKeyApi.artifact X86_64.target v.hmacInitReg ::
      (if v.initOnly then [] else [v.I.finalizeApi.artifact X86_64.target v.hmacFinReg])

end VG.Artifacts.HmacSha512.X86_64
