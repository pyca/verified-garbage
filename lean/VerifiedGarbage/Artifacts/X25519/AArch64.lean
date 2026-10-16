module

public import VerifiedGarbage.Proof.Ed25519.AArch64.DivstepSound
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Impl.X25519.AArch64.Hybrid
public import VerifiedGarbage.Proof.X25519.AArch64.Hybrid.Verified
public import VerifiedGarbage.Impl.X25519.AArch64.Base
public import VerifiedGarbage.Proof.X25519.AArch64.Base.Verified
import VerifiedGarbage.Impl.Mont.Mod
import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.Framework.Registration

/-! # X25519 (RFC 7748) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.X25519.AArch64

def artifacts : List Artifact := [
  Spec.X25519.x25519Api.artifact AArch64.target {
    notes := ["The function saves the callee-saved registers \
      it uses (`x19`–`x24`, and the low halves of `v8`–`v15`) in `scratch`. Field elements use \
      four 64-bit words with `mul`/`umulh`, dedicated squaring, and reduction modulo 2^255 - 19. \
      Each ladder step computes the products `DA` and `CB` with AdvSIMD, in radix 2^25.5 \
      (`umull`/`umlal` on two lanes), interleaved with the scalar field operations that do not \
      depend on them. The inversion uses the ref10 addition chain (254 squarings and 11 \
      multiplications)."]
    code := Impl.X25519.AArch64.Hybrid.x25519
    verified := Proof.X25519.AArch64.Hybrid.x25519_verified },
  Spec.X25519.x25519BaseApi.artifact AArch64.target {
    notes := ["`X25519(k, 9)` is the u-coordinate \
      `(1 + y) / (1 - y)` of `[k] B` on edwards25519, `B` Ed25519's base point (RFC 7748 §4.1's \
      birational map), which the function computes with `vg_ed25519_scalar_base`'s comb rather \
      than the ladder: the scalar's bits are expanded one per byte in `scratch` and clamped there \
      (bits 0-2 and 255 cleared, bit 254 set), the comb's 64 additions accumulate `[k] B` in \
      extended coordinates, and `(Z + Y) / (Z - Y)` takes one inversion. The function saves the \
      callee-saved registers it uses (`x19`-`x24`) in `scratch`."]
    consts := Impl.Ed25519.AArch64.combConsts
    code := Impl.X25519.AArch64.Base.x25519Base
    verified := Proof.X25519.AArch64.Base.x25519Base_verified }]

end VG.Artifacts.X25519.AArch64
