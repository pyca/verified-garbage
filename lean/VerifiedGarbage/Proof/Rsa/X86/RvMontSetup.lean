module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Rsa.X86.RvMontFrame

import VerifiedGarbage.Proof.Rsa.RecoverMath
import VerifiedGarbage.Proof.Rsa.X86.RvWrite
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Ops
import VerifiedGarbage.Proof.Bignum.Math

/-! # Montgomery setup preserves the tracked prime-recovery workspace -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Impl.Rsa.X86.RecoverRt (nar)
open VG.Impl.Rsa.X86.KeyRt (sub3)
open VG.Proof.Rsa.X86.Keys

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat} {m : Nat}

theorem KS.subMont {o a b : Nat} (h : KS g s0 A live AW liveW V ls s)
    (mr : MR g m s) (hom : o ≠ mBase) (ho : o < nArr) (ha : a ∈ live) (hb : b ∈ live)
    (le : A b ≤ A a) (hlW : ∀ j ∈ liveW, o / 2 ≠ j) :
    WP isa (sub3 nar o a b) s fun t =>
      KS g s0 (upd A o (A a - A b)) (o :: live) AW liveW V ls t ∧ MR g m t := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.sub3_ok h.rt ho (h.live_lt a ha) (h.live_lt b hb))
    fun t ⟨_, k, value, borrow, r⟩ => ?_
  rw [kw_nar] at k value
  have rest : Keeps opRegs s t := r.mono (by decide)
  have ht := h.write_w k ho (by simp) rest rfl hlW (by simp)
  rw [h.arrs a ha, h.arrs b hb] at value
  replace value : num t.mem g.B g.w o + A b = A a + 2 ^ (32 * g.w) * (t.gpr .ebx).toNat := value
  have bound : num t.mem g.B g.w o < 2 ^ (32 * g.w) := val32_lt _ _ _ _
  have result : num t.mem g.B g.w o = A a - A b := by
    have zero : (t.gpr .ebx).toNat = 0 := by
      by_contra ne
      have one : (t.gpr .ebx).toNat = 1 := by omega
      rw [one, Nat.mul_one] at value
      omega
    rw [zero, Nat.mul_zero, Nat.add_zero] at value
    omega
  rw [result] at ht
  exact ⟨ht, mr.keepD h.ws k (by simpa using hom) (by simp) (by simp)⟩

/-- Multiplying one by R squared yields the Montgomery representation of one. -/
theorem mont_one {n m X : Nat} (odd : m % 2 = 1) (bound : X < m)
    (value : X * 2 ^ (64 * n) % m = 1 * (2 ^ (128 * n) % m) % m) :
    X = 2 ^ (64 * n) % m := by
  apply VG.Proof.Rsa.r_one (VG.Proof.Bignum.coprime_pow2 odd _) bound
    (R2 := 2 ^ (128 * n) % m)
  · rw [Nat.mod_mod, ← Nat.pow_add]
    congr 2
    omega
  · simpa only [Nat.mul_comm 1] using value

end
end VG.Proof.Rsa.X86.Recover
