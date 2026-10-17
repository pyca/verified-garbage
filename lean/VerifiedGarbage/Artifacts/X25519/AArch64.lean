module

public import VerifiedGarbage.Proof.Ed25519.AArch64.DivstepSound
public import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Verified
public import VerifiedGarbage.Proof.X25519.AArch64.Base.Verified
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Registration

/-! # X25519 (RFC 7748) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.X25519.AArch64

def artifacts : List Artifact := [
  Spec.X25519.x25519Api.artifact AArch64.target {
    notes := ["The function saves the callee-saved registers \
      it uses (`x19`–`x24`) in `scratch`. The ladder is that of s2n-bignum's \
      `curve25519_x25519_byte_alt`, operation for operation: field elements of four 64-bit \
      words, below 2·(2^255 - 19) between operations, with `mul`/`umulh` products and \
      squares, sums and differences folding one carry, and `mux_4` choosing the point to double \
      rather than swapping the points. As in s2n-bignum, the iterations for the bits clamping \
      sets and clears are specialized: the one for bit 254 computes both points from `(u, 1)` \
      directly, and those for bits 2, 1 and 0 double the point the swap chooses three times. \
      The inversion uses Bernstein–Yang divsteps."]
    code := Impl.X25519.AArch64.AltLadder.x25519
    verified := Proof.X25519.AArch64.AltLadder.x25519_verified },
  Spec.X25519.x25519BaseApi.artifact AArch64.target {
    notes := ["`X25519(k, 9)` is the u-coordinate \
      `(1 + y) / (1 - y)` of `[k] B` on edwards25519, `B` Ed25519's base point (RFC 7748 §4.1's \
      birational map), which the function computes with `vg_ed25519_scalar_base`'s comb rather \
      than the ladder: the scalar's bits are expanded one per byte in `scratch` and clamped there \
      (bits 0-2 and 255 cleared, bit 254 set), the comb's 64 additions accumulate `[k] B` in \
      extended coordinates, and `(Z + Y) / (Z - Y)` takes one inversion. The function saves the \
      callee-saved registers it uses (`x19`-`x24`) in `scratch`."]
    consts := Impl.Ed25519.AArch64.combConsts
    written := [("scratch", 1024)]
    code := Impl.X25519.AArch64.Base.x25519Base
    verified := Proof.X25519.AArch64.Base.x25519Base_verified
    writtenOk := Proof.X25519.AArch64.Base.x25519Base_written }]

end VG.Artifacts.X25519.AArch64
