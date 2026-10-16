module

public import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseVerified
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseLit
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Ed25519ScalarBase.X86

def artifacts : List Artifact := [
  Spec.Ed25519.scalarBaseApi.artifact X86.target {
    notes := ["Multiplies with a comb of precomputed multiples of \
      the base point (64 signed radix-16 digits, 32 tables of 8 points, every entry of a table read \
      and masked), then writes a canonical compressed point. The tables are the static \
      `VG_ED25519_COMB`, whose address the function obtains with a position-independent four-byte \
      CALL frame and keeps in `scratch`. The odd digits' additions call \
      `vg_ed25519_r32_add_affine` (the even digits' are inline), the four doublings \
      `vg_ed25519_r32_double`, the final point addition `vg_ed25519_r32_point_add`, and the \
      inversion's addition chain `vg_gf25519_r32_pow250`. \
      Callee-saved registers are saved in the first 16 bytes of `scratch`."]
    consts := Impl.Ed25519.X86.combConsts
    code := Impl.Ed25519.X86.scalarBase
    stack := 8
    verified := Proof.Ed25519.X86.scalarBase_verified }]
end VG.Artifacts.Ed25519ScalarBase.X86
