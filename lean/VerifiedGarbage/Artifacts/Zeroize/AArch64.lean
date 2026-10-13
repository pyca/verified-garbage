module

public import VerifiedGarbage.Proof.Zeroize.AArch64Wide
import Mathlib.Tactic.SplitIfs

@[expose] public section

namespace VG.Artifacts.Zeroize.AArch64
open VG.AArch64

def artifacts : List Artifact := [
  { Spec.Zeroize.zeroizeApi with
    target := target
    doc := Spec.Zeroize.zeroizeApi.doc
    code := Impl.Zeroize.AArch64.zeroizeWide
    contract := Spec.Zeroize.zeroizeContract abi
    verified := Proof.Zeroize.AArch64.wideVerified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]
end VG.Artifacts.Zeroize.AArch64
