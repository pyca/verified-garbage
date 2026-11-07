module
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.Weierstrass

import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Dsa.Encoding

/-! # Short scalar exponents in a full-width arithmetic context -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic

theorem val32_prefix_of_lt {mem : Mem} {base : Addr} {d k n : Nat} (hk : k ≤ n)
    (hlt : val32 mem base d n < 2 ^ (32 * k)) : val32 mem base d k = val32 mem base d n := by
  have H := val32_append mem base d k (n - k)
  rw [Nat.add_sub_of_le hk] at H
  have Hm := congrArg (fun v => v % 2 ^ (32 * k)) H
  rw [Nat.mod_eq_of_lt hlt, Nat.add_mod, Nat.mul_mod_right, Nat.add_zero,
    Nat.mod_mod, Nat.mod_eq_of_lt (val32_lt mem base d k)] at Hm
  exact Hm.symm

theorem decoded_exponent_fits (mem : Mem) (p : Addr) (len : Nat) :
    Spec.Dsa.decodeBE (Spec.Rsa.bytesAt mem p len) < 2 ^ (32 * ((len + 3) / 4)) := by
  have H := VG.Proof.Dsa.decodeBE_lt (Spec.Rsa.bytesAt mem p len)
  simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at H
  have E : 256 ^ len = 2 ^ (8 * len) := by rw [Nat.pow_mul]
  rw [E] at H
  exact Nat.lt_of_lt_of_le H (Nat.pow_le_pow_right (by decide) (by omega))

end VG.Proof.Dsa.X86
