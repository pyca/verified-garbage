import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Ed25519.AArch64.Pow250Verified

/-! # Powers in curve25519's field, in radix `2^64`, on AArch64 -/

namespace VG.Artifacts.Gf25519R64.AArch64

open VG.Spec.X25519.Field64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519.AArch64.Pow250

def artifacts : List Artifact := [
  { pow250Api with
    target := AArch64.target
    doc := pow250Api.doc (notes := ["Uses baseline integer instructions, and AdvSIMD moves to keep \
      `x19` to `x24` in lanes of `v16` to `v18` while it runs. The addition chain of \
      `vg_x25519`'s inversion up to `a^(2^250 - 1)`, with Ed25519's field products (four 64-bit \
      words), the runs of squarings in loops counted by `x19`."])
    code := powFn
    contract := pow250Contract AArch64.abi
    verified := powFn_verified
    stack := 0
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Gf25519R64.AArch64
