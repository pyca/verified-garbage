module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Inst
public import VerifiedGarbage.Spec.RsaOaep.Tables
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
public import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelTCT
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
import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelTCT
import VerifiedGarbage.Proof.RsaOaep.AArch64.MgfCT
import VerifiedGarbage.Proof.RsaOaep.AArch64.TaintImm

/-! # RSAES-OAEP decryption on AArch64, with both hash functions as tables -/

@[expose] public section

namespace VG.Generic.RsaPrivateCrt.AllMdHash.AArch64.RsaOaep

open VG.Proof.RsaOaep.AArch64 (dec_ok OK)
open VG.Proof.RsaOaep.AArch64.Dec (decStack)
open VG.Proof.RsaPkcs1Enc.AArch64 (privOf)
open VG.Proof.HashTable.AArch64 (tables fnsOf)

def artifacts (c : Proof.Rsa.AArch64.CrtImpl) (vs : List Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact :=
  if h : OK vs then [
    Spec.RsaOaep.decryptTablesApi.artifact AArch64.target {
      suffix := Emit.qualifiedName "" [("crt", c.suffix)]
      tables := [("hash", tables vs), ("mgf1", tables vs)]
      code := Impl.RsaOaep.AArch64.decrypt (fnsOf vs) (privOf c).name (privOf c).code
      stack := decStack (privOf c)
      verified := dec_ok vs h c
      features := c.features }]
  else []

end VG.Generic.RsaPrivateCrt.AllMdHash.AArch64.RsaOaep
