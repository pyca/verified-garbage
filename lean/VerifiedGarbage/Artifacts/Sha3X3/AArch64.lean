module

public import VerifiedGarbage.Proof.Sha3.AArch64.Hybrid.X3
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Keccak-f[1600] on three states on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sha3X3.AArch64

def artifacts : List Artifact := [
  Spec.Sha3.permuteX3Api.artifact AArch64.target {
    suffix := "_sha3"
    features := ["sha3"]
    notes := ["Uses the Arm SHA-3 instructions (`EOR3`, `RAX1`, `XAR`, `BCAX`) for the two \
      interleaved states, each of `v0` to `v24` holding the same lane of both, and the general \
      registers for the third, its rounds woven into theirs; the 24 rounds are unrolled. `q8` to \
      `q15` are kept in `scratch`, and the callee-saved general registers in a 128-byte frame."]
    stack := 128
    code := Impl.Sha3.AArch64.Hybrid.X3.code
    verified := Proof.Sha3.AArch64.Hybrid.X3.verified }]

end VG.Artifacts.Sha3X3.AArch64
