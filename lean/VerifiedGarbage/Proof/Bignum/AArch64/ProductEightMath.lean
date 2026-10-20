module

public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.InstancePriority
import Batteries.Tactic.Init
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcMath
import VerifiedGarbage.TCB.AArch64.Simd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcWord
import VerifiedGarbage.Proof.Bignum.AArch64.Run

@[expose] public section
namespace VG.Proof.Bignum.AArch64.ProductEight
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Bignum.AArch64.BlockedRedc

/-- A local write changes a multiword value only at the written window. -/
theorem wv_window_delta {s t : Mem} {B : Addr} {e n j k : Nat}
    (hn : e + 8 * n ≤ 2 ^ 64) (hjk : j + k ≤ n)
    (ho : Outside B (e + 8 * j) (8 * k) s t) :
    wv t B e n + 2 ^ (64 * j) * wv s B (e + 8 * j) k =
      wv s B e n + 2 ^ (64 * j) * wv t B (e + 8 * j) k := by
  have pre := ho.wv (d := e) (k := j) (by omega) (by omega)
  have post := ho.wv (d := e + 8 * (j + k)) (k := n - (j + k)) (by omega) (by omega)
  have hs := wv_add s B e j (k + (n - (j + k)))
  have ht := wv_add t B e j (k + (n - (j + k)))
  have hs' := wv_add s B (e + 8 * j) k (n - (j + k))
  have ht' := wv_add t B (e + 8 * j) k (n - (j + k))
  have len : j + (k + (n - (j + k))) = n := by omega
  have off : e + 8 * j + 8 * k = e + 8 * (j + k) := by omega
  rw [len] at hs ht
  rw [off] at hs' ht'
  rw [ht, hs, ht', hs', pre, post]
  simp only [Nat.mul_add]
  ac_rfl

/-- Lift a local arithmetic equation through an unchanged surrounding buffer. -/
theorem window_lift {before after old new weight cin cout term : Nat}
    (frame : after + weight * old = before + weight * new)
    (equation : new + cout = old + term + cin) :
    after + weight * cout = before + weight * term + weight * cin := by
  have h := congrArg (weight * ·) equation
  grind

/-- One more input block extends the accumulated row product. -/
theorem column_value {old next pending nextPending start q pref digit weight radix : Nat}
    (inv : old + weight * radix * pending = start + q * pref)
    (step : next + weight * radix * radix * nextPending =
      old + weight * (q * digit) + weight * radix * pending) :
    next + (weight * radix) * radix * nextPending = start + q * (pref + weight * digit) := by
  grind

/-- The final pending carry of a bounded row must vanish. -/
theorem row_carry_zero {radix span old q operand out c : Nat}
    (hr : 0 < radix) (ho : old ≤ operand)
    (hq : q < radix) (hb : operand < span)
    (hv : out + (radix * span) * c = old + q * operand) : c = 0 := by
  have hp := Nat.mul_le_mul_right operand (show q + 1 ≤ radix by omega)
  have hbound := Nat.mul_lt_mul_of_pos_left hb hr
  rw [Nat.add_mul, Nat.one_mul] at hp
  by_contra h
  have hc := Nat.mul_le_mul_left (radix * span) (show 1 ≤ c by omega)
  simp only [Nat.mul_one] at hc
  omega

end VG.Proof.Bignum.AArch64.ProductEight
