module

public import VerifiedGarbage.Proof.Rsa.X86.RvOps

/-! # Recovery subtraction without a borrow -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

theorem KS.sub_w {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
    {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat} {o a b : Nat}
    (h : KS g s0 A live AW liveW V ls s)
    (ho : o < nArr) (ha : a ∈ live) (hb : b ∈ live) (hoa : o ≠ a) (hob : o ≠ b)
    (le : A b ≤ A a) (hlW : ∀ j ∈ liveW, o / 2 ≠ j) :
    WP isa (sub3 g.w o a b) s fun t =>
      KS g s0 (upd A o (A a - A b)) (o :: live) AW liveW V ls t ∧ Keeps opRegs s t := by
  refine WP.mono (h.sub3_w ho ha hb hoa hob hlW) fun t ⟨X, ht, r, value, borrow⟩ => ?_
  have bound : X < 2 ^ (32 * g.w) := by
    have v := ht.arrs o (by simp)
    rw [upd_self] at v
    rw [← v]
    exact val32_lt _ _ _ _
  have result : X = A a - A b := by
    have zero : (t.gpr .ebx).toNat = 0 := by
      by_contra ne
      have one : (t.gpr .ebx).toNat = 1 := by omega
      rw [one, Nat.mul_one] at value
      omega
    rw [zero, Nat.mul_zero, Nat.add_zero] at value
    omega
  rw [result] at ht
  exact ⟨ht, r⟩

end VG.Proof.Rsa.X86.Recover
