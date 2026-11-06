module

public import VerifiedGarbage.Proof.X448.PPC64LE.Verified
public import VerifiedGarbage.Proof.X448.PPC64LE.Exchange
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # X448 (RFC 7748) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.X448.PPC64LE

def artifacts : List Artifact := [
  Spec.X448.exchangeApi.artifact PPC64LE.target {
    code := Impl.Xdh.PPC64LE.exchange "vg_x448" Impl.X448.PPC64LE.x448 56
    stack := 48
    verified := Proof.X448.PPC64LE.Exchange.exchange_verified },
  Spec.X448.x448BaseApi.artifact PPC64LE.target {
    code := Impl.X448.PPC64LE.x448Base
    verified := Proof.X448.PPC64LE.x448Base_verified }]

end VG.Artifacts.X448.PPC64LE
