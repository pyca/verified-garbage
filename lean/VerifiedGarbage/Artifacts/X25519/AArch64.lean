import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Impl.X25519.AArch64.Word
import VerifiedGarbage.Proof.X25519.AArch64.Word.Verified
import VerifiedGarbage.Impl.X25519.AArch64.Base
import VerifiedGarbage.Proof.X25519.AArch64.Base.Verified

/-! # X25519 (RFC 7748) on AArch64 -/

namespace VG.Artifacts.X25519.AArch64

def artifacts : List Artifact := [
  { Spec.X25519.x25519Api with
    target := AArch64.target
    doc := Spec.X25519.x25519Api.doc (notes := ["The function saves the callee-saved registers \
      it uses (`x19`–`x24`) in `scratch`. Field elements use four 64-bit words with \
      `mul`/`umulh`, dedicated squaring, and reduction modulo 2^255 - 19. The inversion \
      uses the ref10 addition chain (254 squarings and 11 multiplications)."])
    code := Impl.X25519.AArch64.Word.x25519
    contract := Spec.X25519.x25519Contract AArch64.abi
    verified := Proof.X25519.AArch64.Word.x25519_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.X25519.x25519BaseApi with
    target := AArch64.target
    doc := Spec.X25519.x25519BaseApi.doc (notes := ["`X25519(k, 9)` is the u-coordinate \
      `(1 + y) / (1 - y)` of `[k] B` on edwards25519, `B` Ed25519's base point (RFC 7748 §4.1's \
      birational map), which the function computes with `vg_ed25519_scalar_base`'s comb rather \
      than the ladder: the scalar's bits are expanded one per byte in `scratch` and clamped there \
      (bits 0-2 and 255 cleared, bit 254 set), the comb's 64 additions accumulate `[k] B` in \
      extended coordinates, and `(Z + Y) / (Z - Y)` takes one inversion. The function saves the \
      callee-saved registers it uses (`x19`-`x24`) in `scratch`."])
    consts := Impl.Ed25519.AArch64.combConsts
    code := Impl.X25519.AArch64.Base.x25519Base
    contract := Spec.X25519.x25519BaseContract (AArch64.abi.withConsts Impl.Ed25519.AArch64.combConsts)
    verified := Proof.X25519.AArch64.Base.x25519Base_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.X25519.AArch64
