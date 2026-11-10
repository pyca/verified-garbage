module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Proof.Framework.Cold
public import VerifiedGarbage.Proof.Framework.EntryBranch
public import VerifiedGarbage.Proof.Framework.OffsetBelow
public import VerifiedGarbage.Proof.Framework.RegSetOrder
public import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Sse
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

/-! # PBKDF2-HMAC-SHA-512/256 (RFC 8018) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Pbkdf2Sha512_256.X86_64

def artifacts : List Artifact :=
  (VG.Proof.Variants.MdHash.X86_64.sha512_256Variants.filter fun v => !v.initOnly).flatMap
    fun (v : Proof.Pbkdf2.Md.X86_64.MdHash) => [
    v.I.pbkdf2Api.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.StackScratch.X86_64.withStackArgScratch (Proof.Pbkdf2.Md.X86_64.pbkdf2Frame v.I) 1 v.H.pbkdf2
      stack := 24 + Proof.Pbkdf2.Md.X86_64.pbkdf2Frame v.I
      verified := v.pbkdf2F
      spSafe := X86_64.withStackArgScratch_spSafe v.pbkdf2Sp }]

end VG.Artifacts.Pbkdf2Sha512_256.X86_64
