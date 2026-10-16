module

public import VerifiedGarbage.Proof.X25519.X86.Verified
import VerifiedGarbage.Proof.X25519.X86.Lit
public import VerifiedGarbage.Proof.X25519.X86.Base.Verified
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.X25519.X86.Base.Lit

/-! # X25519 (RFC 7748) on x86 -/

@[expose] public section

namespace VG.Artifacts.X25519.X86

def artifacts : List Artifact := [
  Spec.X25519.x25519Api.artifact X86.target {
    notes := ["The function saves its caller's callee-saved \
      registers in `scratch`. Field elements are eight 32-bit words, multiplied by product scanning \
      (squared with each product of distinct words doubled) and reduced with `2^256 = 38` (mod p); \
      the inversion is ref10's addition chain, up to `z^(2^250 - 1)` by a call of \
      `vg_gf25519_r32_pow250`."]
    code := Impl.X25519.X86.x25519
    stack := 8
    verified := Proof.X25519.X86.x25519_verified },
  Spec.X25519.x25519BaseApi.artifact X86.target {
    notes := ["Computes `[k] B` on edwards25519 with \
      `vg_ed25519_scalar_base`'s comb (64 signed radix-16 digits, 32 tables of 8 points, every \
      entry of a table read and masked), for the clamped scalar `k`, then `u = (Z + Y) / (Z - Y)` \
      with one inversion: RFC 7748 §4.1's birational map, which takes edwards25519's base point to \
      `u = 9` and its group law to the ladder's (`VG.Proof.X25519.Edwards.x25519_basePoint`). \
      The tables are the static `VG_ED25519_COMB`, whose address the function obtains with a \
      position-independent four-byte CALL frame and keeps in `scratch`. The comb's odd digits' \
      additions call `vg_ed25519_r32_add_affine`, its doublings `vg_ed25519_r32_double` and its \
      final point addition `vg_ed25519_r32_point_add`, and the inversion's addition chain \
      `vg_gf25519_r32_pow250`. Callee-saved registers are saved in the first 16 bytes of `scratch`."]
    consts := Impl.Ed25519.X86.combConsts
    code := Impl.X25519.X86.Base.x25519Base
    stack := 8
    verified := Proof.X25519.X86.Base.x25519Base_verified }]

end VG.Artifacts.X25519.X86
