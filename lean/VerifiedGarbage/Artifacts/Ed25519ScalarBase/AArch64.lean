import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseVerified

/-! Complete unsigned scalar multiplication by the Ed25519 base point. -/

namespace VG.Artifacts.Ed25519ScalarBase.AArch64

def artifacts : List Artifact := [
  { Spec.Ed25519.scalarBaseApi with
    target := AArch64.target
    doc := Spec.Ed25519.scalarBaseApi.doc (notes := ["Uses baseline integer instructions and \
      a comb: the scalar's 64 nibbles n give the digits n - 8, and each digit's multiple of \
      [16^i]B is one of 32 tables of [k 256^j]B for k <= 8, affine, cached as \
      [Y - X, Y + X, 2dT] in the static `VG_ED25519_COMB` and checked against the specification \
      in Lean. Each table serves two digits, n_{2j+1} and n_{2j}: one point accumulates the odd \
      digits' entries from [G']B, is doubled four times, and accumulates the even digits' \
      (G' makes up for the digits' offset). Each entry is selected in constant time (reading \
      every entry of the table) and negated under its sign's mask; the 64 additions are calls of \
      `vg_ed25519_r64_add_affine_ext`, the four doublings calls of `vg_ed25519_r64_double_ext`, \
      in a fixed schedule. The working values and saved registers reside in `scratch`."])
    consts := Impl.Ed25519.AArch64.combConsts
    code := Impl.Ed25519.AArch64.scalarBase
    contract := Spec.Ed25519.scalarBaseContract (AArch64.abi.withConsts Impl.Ed25519.AArch64.combConsts)
    verified := Proof.Ed25519.AArch64.scalarBase_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.Ed25519ScalarBase.AArch64
