module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Sp
public import VerifiedGarbage.Proof.RsaOaep.X86_64.DecCtx
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Callees
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.RsaOaep.X86_64.DecCT
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaOaep.X86_64.DecCT
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
import VerifiedGarbage.Proof.Framework.Cold
import VerifiedGarbage.Proof.Framework.EntryBranch
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Registration
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
import VerifiedGarbage.Proof.Hmac.AnyKey
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.MdStream.X86_64.Words
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.AnyKeyEntry
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PadW
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Words
import VerifiedGarbage.Proof.Pbkdf2.Scratch
import VerifiedGarbage.Proof.RsaOaep.X86_64.DecCorrect
import VerifiedGarbage.Proof.RsaOaep.X86_64.DecSpec
import VerifiedGarbage.Proof.RsaOaep.X86_64.EncEm
import VerifiedGarbage.Proof.RsaOaep.X86_64.Good
import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
import VerifiedGarbage.Proof.Sha256.X86_64.Compress
import VerifiedGarbage.Proof.Sha512.X86_64.Wide
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Verified
public import VerifiedGarbage.Proof.HashTable.X86_64

/-! # RSAES-OAEP decryption on x86-64, with MGF1's hash function as a table -/

@[expose] public section

namespace VG.Generic.MdHash.RsaPrivateCrt.AllMdHash.X86_64.RsaOaep

open VG.Proof.RsaOaep.X86_64 (decStack dec_ok dec_spSafe OK)
open VG.Proof.RsaOaep.X86_64.Inst (emitted parts)
open VG.Proof.RsaPkcs1Enc.X86_64 (privOf)
open VG.Proof.HashTable.X86_64 (tables fnsOf)

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) (c : Proof.Rsa.X86_64.CrtImpl)
    (vs : List Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact :=
  if h : emitted v = true ∧ OK vs then [
    (Spec.RsaOaep.decryptTableApi v.mgf.G).artifact X86_64.target {
      suffix := Emit.qualifiedName "" (parts v ++ [("crt", c.suffix)])
      tables := [("mgf1", tables vs)]
      code := Impl.RsaOaep.X86_64.decrypt v.H.stream (fnsOf vs) (privOf c).name (privOf c).code
      stack := decStack
      verified := dec_ok v.ok v.K v.mgf vs h.2 (privOf c)
      spSafe := dec_spSafe v.ok v.K vs (privOf c)
      features := v.features ++ c.features.filter (!v.features.contains ·) }]
  else []

end VG.Generic.MdHash.RsaPrivateCrt.AllMdHash.X86_64.RsaOaep
