module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaOaep.Arm.Inst
public import VerifiedGarbage.Proof.Rsa.Arm.PublicOfCrt
public import VerifiedGarbage.Spec.RsaOaep.Tables
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.Arm

/-! # RSAES-OAEP on ARMv7, with both hash functions as tables -/

@[expose] public section

namespace VG.Artifacts.RsaOaep.Arm

open VG.Proof.Rsa.Arm (CrtImpl)
open VG.Proof.RsaOaep.Arm (OK dec_ok enc_ok)
open VG.Proof.HashTable.Arm (vars tables)

def artifactsFor (v : CrtImpl) : List Artifact :=
  if h : OK vars then [
    Spec.RsaOaep.decryptTablesApi.artifact Arm.target {
      suffix := v.suffix
      tables := [("hash", tables vars), ("mgf1", tables vars)]
      code := Proof.RsaOaep.Arm.Dec.decCode vars v
      stack := 3624
      verified := dec_ok vars h v
      features := v.features },
    Spec.RsaOaep.encryptTablesApi.artifact Arm.target {
      suffix := v.suffix
      tables := [("hash", tables vars), ("mgf1", tables vars)]
      code := Proof.RsaOaep.Arm.Enc.encryptCode vars (Proof.Rsa.Arm.pdOfCrt v)
      stack := 240
      verified := enc_ok vars h (Proof.Rsa.Arm.pdOfCrt v)
      features := v.features }]
  else []

def artifacts : List Artifact :=
  VG.Proof.Variants.RsaPrivateCrt.Arm.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.RsaOaep.Arm
