module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Inst
public import VerifiedGarbage.Proof.HashTable.AArch64
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

/-! # RSAES-OAEP encryption with a precomputed public key on AArch64, with MGF1's hash function as a table -/

@[expose] public section

namespace VG.Generic.MdHash.RsaPublicPrecomputed.AllMdHash.AArch64.RsaOaep

open VG.Proof.RsaOaep.AArch64 (enc_ok OK)
open VG.Proof.RsaOaep.AArch64.Inst (emitted parts)
open VG.Proof.RsaOaep.AArch64.Enc (encStack)
open VG.Proof.RsaPkcs1Sig.AArch64 (pdOf)
open VG.Proof.HashTable.AArch64 (tables fnsOf)

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) (c : Proof.Rsa.AArch64.PublicImpl)
    (vs : List Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact :=
  if h : emitted v = true ∧ OK vs then [
    (Spec.RsaOaep.encryptTableApi v.mgf.G).artifact AArch64.target {
      suffix := Emit.qualifiedName "" (parts v ++ [("rsa", c.suffix)])
      tables := [("mgf1", tables vs)]
      code := Impl.RsaOaep.AArch64.Precomputed.encrypt v.H (fnsOf vs) (pdOf c).name (pdOf c).code
      stack := encStack (pdOf c)
      verified := enc_ok v vs h.2 c
      features := v.features ++ c.features.filter (!v.features.contains ·) }]
  else []

end VG.Generic.MdHash.RsaPublicPrecomputed.AllMdHash.AArch64.RsaOaep
