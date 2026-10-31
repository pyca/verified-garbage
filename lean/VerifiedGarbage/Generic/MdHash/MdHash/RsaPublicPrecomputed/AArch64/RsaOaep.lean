module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Inst
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.AArch64.TaintErase
public import VerifiedGarbage.Proof.Mgf1.Bytes
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Args
public import VerifiedGarbage.Proof.RsaOaep.AArch64.DecCT1
public import VerifiedGarbage.Proof.RsaOaep.AArch64.DecCT2
public import VerifiedGarbage.Proof.RsaOaep.AArch64.DecCorrect
public import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCT1
public import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCorrect
public import VerifiedGarbage.Proof.RsaOaep.AArch64.EncEm
public import VerifiedGarbage.Proof.RsaOaep.AArch64.EncMain
public import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelCT
public import VerifiedGarbage.Proof.RsaOaep.AArch64.MgfCT
public import VerifiedGarbage.Proof.RsaOaep.AArch64.TaintImm
import VerifiedGarbage.Proof.Framework.AArch64.TaintErase
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaOaep.AArch64.Args
import VerifiedGarbage.Proof.RsaOaep.AArch64.DecCT1
import VerifiedGarbage.Proof.RsaOaep.AArch64.DecCT2
import VerifiedGarbage.Proof.RsaOaep.AArch64.DecCorrect
import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCT1
import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCorrect
import VerifiedGarbage.Proof.RsaOaep.AArch64.EncEm
import VerifiedGarbage.Proof.RsaOaep.AArch64.EncMain
import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelCT
import VerifiedGarbage.Proof.RsaOaep.AArch64.MgfCT
import VerifiedGarbage.Proof.RsaOaep.AArch64.TaintImm

/-!
# RSAES-OAEP encryption with a precomputed public key on AArch64

A generic file of three interfaces (see `TCB/Emit.lean`):
`vg_rsa_oaep_<H>_mgf1_<G>_encrypt_precomputed` calls the streaming functions
of `H`, made with the compression function of its `MdHash` variant `v` (for
`lHash`), and of `G`, made with that of its variant `v2` (for MGF1), and an
implementation `c` of `vg_rsa_public_precomputed_checked`
(`Variants/RsaPublicPrecomputed/AArch64/`). It is emitted for the pairs of
hash functions `Inst.emitted` says, with each `c`, named by
`Emit.qualifiedName` (`Inst.parts`, then `rsa`), and needs all three's CPU
features.

Its stack is its frames, 288 bytes, and 16 bytes below them for the calls,
whose callees use no more.
-/

@[expose] public section

namespace VG.Generic.MdHash.MdHash.RsaPublicPrecomputed.AArch64.RsaOaep

open VG.Proof.RsaOaep.AArch64 (mgf_valid enc_sat)
open VG.Proof.RsaOaep.AArch64.Inst (emitted parts features)
open VG.Proof.RsaOaep.AArch64.Enc (encStack enc_verified)
open VG.Proof.RsaPkcs1Sig.AArch64 (pdOf)

def artifacts (v v2 : Proof.Pbkdf2.Md.AArch64.MdHash) (c : Proof.Rsa.AArch64.PublicImpl) : List Artifact :=
  if emitted v v2 then [
    (Spec.RsaOaep.encryptPrecomputedApi v.mgf.G v2.mgf.G).artifact AArch64.target {
      suffix := Emit.qualifiedName "" (parts v v2 ++ [("rsa", c.suffix)])
      code := Impl.RsaOaep.AArch64.Precomputed.encrypt v.H v2.H (pdOf c).name (pdOf c).code
      stack := encStack (pdOf c)
      verified := enc_verified v.ok.stream v2.ok.stream v.mgf.hash v.mgf.len (mgf_valid v.mgf) v2.mgf.hash
        v2.mgf.len (mgf_valid v2.mgf) (pdOf c) (enc_sat v2.mgf.G v.mgf.mem c)
      features := features v v2 ++ c.features.filter (!(features v v2).contains ·) }]
  else []

end VG.Generic.MdHash.MdHash.RsaPublicPrecomputed.AArch64.RsaOaep
