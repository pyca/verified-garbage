module

public import VerifiedGarbage.TCB.Emit
import VerifiedGarbage.Proof.RsaOaep.X86_64.PcSp
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Sp
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.RsaOaep.X86_64.Precomputed
public import VerifiedGarbage.Proof.Rsa.X86_64.PublicImpl
public import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCtx
public import VerifiedGarbage.Spec.RsaOaep.Precomputed
import VerifiedGarbage.Proof.RsaOaep.X86_64.PcCT

/-!
# RSAES-OAEP encryption with a precomputed public key on x86-64

A generic file of three interfaces (see `TCB/Emit.lean`):
`vg_rsa_oaep_<H>_mgf1_<G>_encrypt_precomputed` calls the streaming functions
of `H`, made with the compression function of its `MdHash` variant `v` (for
`lHash`), and of `G`, made with that of its variant `v2` (for MGF1), and an
implementation `c` of `vg_rsa_public_precomputed_checked`
(`Variants/RsaPublicPrecomputed/X86_64/`). It is emitted for the pairs of hash
functions `Inst.emitted` says, with each `c`, named by `Emit.qualifiedName`
(`Inst.parts`, then `rsa`), and needs all three's CPU features.

Its stack is its frame, a return address and what the hash functions'
calls use, as `vg_rsa_oaep_<H>_mgf1_<G>_encrypt`'s.
-/

@[expose] public section

namespace VG.Generic.MdHash.MdHash.RsaPublicPrecomputed.X86_64.RsaOaep

open VG.Proof.RsaOaep.X86_64 (encStack)
open VG.Proof.RsaOaep.X86_64.Inst (emitted parts features)

def artifacts (v v2 : Proof.Pbkdf2.Md.X86_64.MdHash) (c : Proof.Rsa.X86_64.PublicImpl) : List Artifact :=
  if emitted v v2 then [
    (Spec.RsaOaep.encryptPrecomputedApi v.mgf.G v2.mgf.G).artifact X86_64.target {
      suffix := Emit.qualifiedName "" (parts v v2 ++ [("rsa", c.suffix)])
      notes := ["This implementation hashes the label with `" ++ v.H.stream.updN ++ "`, masks `DB` \
          and the seed with MGF1 calling `" ++ v2.H.stream.updN ++ "`, and calls `" ++ c.name ++
          "` with the cached modulus values. The message's length is public; its bytes, the label's \
          and the seed's are only copied, hashed and masked."]
      code := Impl.RsaOaep.X86_64.Precomputed.encrypt v.H.stream v2.H.stream c.name c.code
      stack := encStack
      verified := Proof.RsaOaep.X86_64.Pc.code_verified v.ok v.K v2.ok v2.K v.mgf v2.mgf c
        (Proof.RsaOaep.X86_64.Pc.sat v.mgf.G v2.mgf.G v.mgf.mem)
      spSafe := Proof.RsaOaep.X86_64.Pc.code_spSafe v.ok v.K v2.ok v2.K c
      features := features v v2 ++ c.features.filter (!(features v v2).contains ·) }]
  else []

end VG.Generic.MdHash.MdHash.RsaPublicPrecomputed.X86_64.RsaOaep
