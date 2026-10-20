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

/-!
# RSAES-OAEP decryption on x86-64

A generic file of three interfaces (see `TCB/Emit.lean`):
`vg_rsa_oaep_<H>_mgf1_<G>_decrypt` calls the streaming functions of `H`,
made with the compression function of its `MdHash` variant `v` (for
`lHash`), and of `G`, made with that of its variant `v2` (for MGF1), and
`vg_rsa_private_checked` calling an implementation `c` of
`vg_rsa_private_crt` (`Variants/RsaPrivateCrt/X86_64/`). It is emitted for
the pairs of hash functions `Inst.emitted` says, with each `c`, named by
`Emit.qualifiedName` (`Inst.parts`, then `crt`), and needs all three's CPU
features.

Its stack is its frame, a return address and `vg_rsa_private_checked`'s
3256 bytes, which are more than the hash functions use.
-/

@[expose] public section

namespace VG.Generic.MdHash.MdHash.RsaPrivateCrt.X86_64.RsaOaep

open VG.Proof.RsaOaep.X86_64 (decStack dec_verified dec_spSafe)
open VG.Proof.RsaOaep.X86_64.Inst (emitted parts features)
open VG.Proof.RsaPkcs1Enc.X86_64 (privOf)

def artifacts (v v2 : Proof.Pbkdf2.Md.X86_64.MdHash) (c : Proof.Rsa.X86_64.CrtImpl) : List Artifact :=
  if emitted v v2 then [
    (Spec.RsaOaep.decryptApi v.mgf.G v2.mgf.G).artifact X86_64.target {
      suffix := Emit.qualifiedName "" (parts v v2 ++ [("crt", c.suffix)])
      notes := ["This implementation calls `" ++ (privOf c).name ++ "`, hashes the label with `" ++
          v.H.stream.updN ++ "` and unmasks the seed and `DB` with MGF1 calling `" ++ v2.H.stream.updN ++
          "`. The checks of `Y`, `lHash'` and the separator, the scan for it and the shift of the \
          message to the start of `out` are masks computed without branches, reading every byte of \
          `EM` whatever the outcome."]
      code := Impl.RsaOaep.X86_64.decrypt v.H.stream v2.H.stream (privOf c).name (privOf c).code
      stack := decStack
      verified := dec_verified v.ok v.K v2.ok v2.K v.mgf v2.mgf (privOf c)
      spSafe := dec_spSafe v.ok v.K v2.ok v2.K (privOf c)
      features := features v v2 ++ c.features.filter (!(features v v2).contains ·) }]
  else []

end VG.Generic.MdHash.MdHash.RsaPrivateCrt.X86_64.RsaOaep
