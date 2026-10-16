module

public import VerifiedGarbage.Proof.Rc4.AArch64.VerifiedInit
public import VerifiedGarbage.Proof.Rc4.AArch64.VerifiedApply
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Raw RC4 on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.Rc4.AArch64

def artifacts : List Artifact := [
  Spec.Rc4.initApi.artifact AArch64.target {
    notes := [
      "The permutation stays in `v16`–`v31` for the whole key schedule: a \
       secret-indexed read is four `tbl`/`tbx` lookups of four registers each, and a \
       write sixteen `cmeq`/`bit` pairs, so no address or branch depends on the key, \
       the table or `j`."]
    code := Impl.Rc4.AArch64.init
    verified := Proof.Rc4.AArch64.init_verified },
  Spec.Rc4.applyApi.artifact AArch64.target {
    notes := [
      "The permutation stays in `v16`–`v31` for the whole call, rotated so that \
       the public `S[i]` is at a lane fixed in the code: a secret-indexed read is four \
       `tbl`/`tbx` lookups of four registers each, and a write sixteen `cmeq`/`bit` \
       pairs, so no address or branch depends on the table, `j` or the data."]
    code := Impl.Rc4.AArch64.apply
    verified := Proof.Rc4.AArch64.apply_verified }]

end VG.Artifacts.Rc4.AArch64
