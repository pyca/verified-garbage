module

public import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
public import VerifiedGarbage.Proof.Framework.Registration

/-! # GHASH on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Gcm.PPC64LE

def artifacts : List Artifact := [
  Spec.Gcm.ghashApi.artifact PPC64LE.target {
    notes := ["`•` is computed bit by bit as Algorithm 1 of §6.3 does, with masks instead of \
        branches; the nonvolatile registers it uses are saved in `scratch`."]
    code := Impl.Gcm.PPC64LE.ghash
    verified := Proof.Gcm.PPC64LE.ghash_verified }]

end VG.Artifacts.Gcm.PPC64LE
