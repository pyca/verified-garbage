import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2

/-! # Keccak-f[1600] on two interleaved states on AArch64 -/

namespace VG.Artifacts.Sha3X2.AArch64

open VG.Impl.Sha3.AArch64.Neon

def artifact (sha3 : Bool) : Artifact :=
  { Spec.Sha3.permuteX2Api with
    name := X2.name sha3
    features := if sha3 then ["sha3"] else []
    target := AArch64.target
    doc := Spec.Sha3.permuteX2Api.doc (notes := [(if sha3 then
      "Uses the Arm SHA-3 instructions (`EOR3`, `RAX1`, `XAR`, `BCAX`)" else
      "Uses baseline AdvSIMD") ++ ": each of `v0` to `v24` holds the same lane of both states, \
      and the 24 rounds are unrolled. `q8` to `q15` are kept in `scratch`."])
    code := X2.code sha3
    contract := Spec.Sha3.permuteX2Contract AArch64.abi
    verified := Proof.Sha3.AArch64.Neon.X2.verified sha3
    spSafe := Code.all_of_forall (fun _ => rfl) _ }

def artifacts : List Artifact := [artifact false, artifact true]

end VG.Artifacts.Sha3X2.AArch64
