module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPss.X86.Inst

/-! # RSASSA-PSS signing on x86, with the hash functions as tables -/

@[expose] public section

namespace VG.Generic.RsaPrivateCrt.AllSha1.AllSha256.X86.RsaPss

open VG.Proof.RsaPss.X86 (mvars sign_ok)
open VG.Proof.HashTable.X86 (vars)

def artifacts (c : Proof.Rsa.X86.PrivChecked.CrtImpl) (vs1 : List Proof.Sha1.X86.Variants.Backend)
    (vs256 : List Proof.Sha256.X86.Variants.Backend) : List Artifact :=
  if h : Proof.RsaPss.X86.Sg.OK (mvars vs1 vs256) (vars vs1 vs256) then [
    Spec.RsaPss.signTableApi.artifact X86.target {
      suffix := Emit.qualifiedName "" [("crt", c.suffix)]
      tables := [("hash", Proof.MdHashTable.X86.tables (mvars vs1 vs256)),
        ("mgf1", Proof.HashTable.X86.tables (vars vs1 vs256))]
      code := Proof.RsaPss.X86.Sg.signCode (mvars vs1 vs256) (vars vs1 vs256) c
      stack := Proof.RsaPss.X86.Sg.stackBytes
      verified := sign_ok _ _ h c
      spSafe := Proof.RsaPss.X86.Sg.code_sp h c
      features := c.features }]
  else []

end VG.Generic.RsaPrivateCrt.AllSha1.AllSha256.X86.RsaPss
