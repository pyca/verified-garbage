import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Impl.X448.AArch64.Field56
import VerifiedGarbage.Proof.X448.AArch64.Fast.Verified
import VerifiedGarbage.Proof.X448.AArch64.Base.Verified
import VerifiedGarbage.Proof.X448.AArch64.Fast.Lit

/-! # X448 (RFC 7748) on AArch64 -/

namespace VG.Artifacts.X448.AArch64

def artifacts : List Artifact := [
  { Spec.X448.x448Api with
    target := AArch64.target
    doc := Spec.X448.x448Api.doc (notes := ["The function saves its caller's callee-saved \
      registers in `scratch`. Field elements are eight 56-bit limbs. A multiplication keeps its \
      operands in registers and accumulates two-word coefficients with Karatsuba's identity for \
      `2^224` (48 products, 30 for a square), reduced with `2^448 = 2^224 + 1` (mod p); sums and \
      differences are not reduced. Each ladder step forms its sums and differences from the \
      conditionally swapped coordinates directly, and does four of its ten products as two pairs \
      of AdvSIMD multiplications (sixteen 28-bit limbs, the two products in the two 64-bit lanes), \
      each interleaved with scalar operations independent of it. Inversion uses an addition chain \
      for `p - 2`."])
    code := Impl.X448.AArch64.Fast.x448
    contract := Spec.X448.x448Contract AArch64.abi
    verified := Proof.X448.AArch64.Fast.x448_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { Spec.X448.x448BaseApi with
    target := AArch64.target
    doc := Spec.X448.x448BaseApi.doc (notes := ["`X448(k, 5)` is the u-coordinate `y² / x²` of \
      `[k] B` on edwards448, `B` Ed448's base point (RFC 7748 §4.2's 4-isogeny), which the function \
      computes with a comb rather than the ladder: the scalar's 112 signed radix-16 digits select, in \
      constant time (reading every entry), entries `[m 256^j] B` (`m ≤ 8`) of 56 tables in the \
      static `VG_X448_COMB`, added to two projective accumulators with RFC 8032's complete addition \
      (a call of `vg_ed448_r56_comb_base`), then `16 A + B` (five calls of \
      `vg_ed448_r56_point_add`) and `Y² / X²`. Field \
      elements are eight 56-bit limbs, multiplied as `vg_x448`'s are. The function saves its caller's \
      callee-saved registers in `scratch`."])
    consts := Impl.X448.AArch64.Base.combConsts
    code := Impl.X448.AArch64.Base.x448Base
    contract := Spec.X448.x448BaseContract (AArch64.abi.withConsts Impl.X448.AArch64.Base.combConsts)
    verified := Proof.X448.AArch64.Base.x448Base_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

end VG.Artifacts.X448.AArch64
