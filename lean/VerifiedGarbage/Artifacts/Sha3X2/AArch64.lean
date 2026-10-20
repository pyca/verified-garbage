module

public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Keccak-f[1600] on two interleaved states on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sha3X2.AArch64

open VG.Impl.Sha3.AArch64.Neon

def artifact (sha3 : Bool) : Artifact :=
  Spec.Sha3.permuteX2Api.artifact AArch64.target {
    suffix := if sha3 then "_sha3" else ""
    features := if sha3 then ["sha3"] else []
    notes := [(if sha3 then
      "Uses the Arm SHA-3 instructions (`EOR3`, `RAX1`, `XAR`, `BCAX`)" else
      "Uses baseline AdvSIMD") ++ ": each of `v0` to `v24` holds the same lane of both states, \
      and the 24 rounds are unrolled. `q8` to `q15` are kept in `scratch`."]
    code := X2.code sha3
    verified := Proof.Sha3.AArch64.Neon.X2.verified sha3 }

def artifacts : List Artifact := [artifact false, artifact true]

end VG.Artifacts.Sha3X2.AArch64
