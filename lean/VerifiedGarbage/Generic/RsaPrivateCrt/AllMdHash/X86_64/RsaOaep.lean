module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Spec.RsaOaep.Tables
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Sp
public import VerifiedGarbage.Proof.RsaOaep.X86_64.DecCtx
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Callees
import Mathlib.Tactic.Finiteness.Attr
public import VerifiedGarbage.Proof.RsaOaep.X86_64.DecCT
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.Cold
public import VerifiedGarbage.Proof.Framework.EntryBranch
public import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Framework.OffsetBelow
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Sse
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
public import VerifiedGarbage.Proof.Hmac.AnyKey
public import VerifiedGarbage.Proof.Hmac.Generic.Implies
public import VerifiedGarbage.Proof.MdStream.X86_64.Words
public import VerifiedGarbage.Proof.Mgf1.Bytes
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.AnyKeyEntry
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PadW
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Words
public import VerifiedGarbage.Proof.Pbkdf2.Scratch
public import VerifiedGarbage.Proof.RsaOaep.X86_64.DecCorrect
public import VerifiedGarbage.Proof.RsaOaep.X86_64.DecSpec
public import VerifiedGarbage.Proof.RsaOaep.X86_64.EncEm
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Good
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
public import VerifiedGarbage.Proof.Sha256.X86_64.Compress
public import VerifiedGarbage.Proof.Sha512.X86_64.Wide
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Verified
public import VerifiedGarbage.Proof.HashTable.X86_64
public import VerifiedGarbage.TCB.X86_64.Print

/-! # RSAES-OAEP decryption on x86-64, with both hash functions as tables -/

@[expose] public section

namespace VG.Generic.RsaPrivateCrt.AllMdHash.X86_64.RsaOaep

open VG.Proof.RsaOaep.X86_64 (decStack dec_ok dec_spSafe OK)
open VG.Proof.RsaPkcs1Enc.X86_64 (privOf)
open VG.Proof.HashTable.X86_64 (tables fnsOf)

def artifacts (c : Proof.Rsa.X86_64.CrtImpl) (vs : List Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact :=
  if h : OK vs then [
    Spec.RsaOaep.decryptTablesApi.artifact X86_64.target {
      suffix := Emit.qualifiedName "" [("crt", c.suffix)]
      tables := [("hash", tables vs), ("mgf1", tables vs)]
      code := Impl.RsaOaep.X86_64.decrypt (fnsOf vs) (privOf c).name (privOf c).code
      stack := decStack
      verified := dec_ok vs h (privOf c)
      spSafe := dec_spSafe vs (privOf c)
      features := c.features }]
  else []

end VG.Generic.RsaPrivateCrt.AllMdHash.X86_64.RsaOaep
