module

public import VerifiedGarbage.Proof.Idea.PPC64LE.Invert
public import VerifiedGarbage.Proof.Idea.PPC64LE.Key
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.PPC64LE.Lit

/-! # IDEA artifacts on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Idea.PPC64LE

def artifacts : List Artifact := [
  Spec.Idea.expandKeyApi.artifact PPC64LE.target {
    notes := ["Each doubleword of subkeys is a fixed bit permutation of the key's two doublewords, assembled with rotations and masks, without branches."]
    code := Impl.Idea.PPC64LE.expandKey
    verified := Proof.Idea.PPC64LE.expandKey_verified },
  Spec.Idea.invertKeyApi.artifact PPC64LE.target {
    notes := ["Each inverse is `a ^ (2^16 - 1)` modulo 2^16 + 1, fifteen squarings and multiplications by `mulld`, each reduced without branches."]
    code := Impl.Idea.PPC64LE.invertKey
    verified := Proof.Idea.PPC64LE.invertKey_verified },
  Spec.Idea.ecbApi.artifact PPC64LE.target {
    notes := ["A block at a time in general-purpose registers: each multiplication modulo 2^16 + 1 is a `mulld` of the residues and a reduction of the product from its halves, without branches."]
    code := Impl.Idea.PPC64LE.ecb
    verified := Proof.Idea.PPC64LE.ecb_verified }]

end VG.Artifacts.Idea.PPC64LE
