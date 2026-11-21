module

public import VerifiedGarbage.Proof.Zeroize.PPC64LE
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Zeroization on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Zeroize.PPC64LE
open VG.PPC64LE

def artifacts : List Artifact := [
  Spec.Zeroize.zeroizeApi.artifact target {
    code := Impl.Zeroize.PPC64LE.zeroize
    verified := Proof.Zeroize.PPC64LE.zeroize_scrubbed }]
end VG.Artifacts.Zeroize.PPC64LE
