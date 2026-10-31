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

/-! # RSAES-OAEP decryption on AArch64 -/

@[expose] public section

namespace VG.Generic.MdHash.MdHash.RsaPrivateCrt.AArch64.RsaOaep

open VG.Proof.RsaOaep.AArch64 (mgf_valid dec_sat)
open VG.Proof.RsaOaep.AArch64.Inst (emitted parts features)
open VG.Proof.RsaOaep.AArch64.Dec (decStack dec_verified)
open VG.Proof.RsaPkcs1Enc.AArch64 (privOf)

def artifacts (v v2 : Proof.Pbkdf2.Md.AArch64.MdHash) (c : Proof.Rsa.AArch64.CrtImpl) : List Artifact :=
  if emitted v v2 then [
    (Spec.RsaOaep.decryptApi v.mgf.G v2.mgf.G).artifact AArch64.target {
      suffix := Emit.qualifiedName "" (parts v v2 ++ [("crt", c.suffix)])
      code := Impl.RsaOaep.AArch64.decrypt v.H v2.H (privOf c).name (privOf c).code
      stack := decStack (privOf c)
      verified := dec_verified v.ok.stream v2.ok.stream v.mgf.hash v.mgf.len (mgf_valid v.mgf) v2.mgf.hash
        v2.mgf.len (mgf_valid v2.mgf) (privOf c) (dec_sat v.mgf.G v2.mgf.G c)
      features := features v v2 ++ c.features.filter (!(features v v2).contains ·) }]
  else []

end VG.Generic.MdHash.MdHash.RsaPrivateCrt.AArch64.RsaOaep
