module
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Proof.Framework.InstancePriority
import Batteries.Tactic.Init
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.RegSet


@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowLazy
open VG VG.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64

/-- A reduced product below R + m has a single carry bit above R. -/
theorem top_bound {R L H U m : Nat} (hm : m < R)
    (h : L + R*(H + 2^64*U) < R+m) : U = 0 ∧ H ≤ 1 := by
  have h2 : H + 2^64*U < 2 := by
    by_contra hn
    have hh := Nat.mul_le_mul_left R (show 2 ≤ H+2^64*U by omega)
    omega
  have hu : U = 0 := by
    by_contra hn
    have hh := Nat.mul_le_mul_left (2^64) (show 1 ≤ U by omega)
    omega
  exact ⟨hu, by omega⟩

/-- Expose the high carry as a Boolean without inspecting any secret in control
flow. This is a proof witness for the branch-free masked subtraction. -/
theorem top_bit {s : State} {B : Addr} {e w m : Nat}
    (hm : m < 2^(64*w)) (ht : wv s.mem B e (w+2) < 2^(64*w)+m) :
    ∃ bit : Bool, word s.mem B (e+8*w) = BitVec.ofNat 64 bit.toNat ∧
      wv s.mem B e (w+2) = wv s.mem B e w + 2^(64*w)*bit.toNat := by
  have hh := top_bound hm (by rwa [wv_top2] at ht)
  rcases hh with ⟨hu,hh⟩
  have hw : (word s.mem B (e+8*w)).toNat = 0 ∨ (word s.mem B (e+8*w)).toNat = 1 := by omega
  rcases hw with hw | hw
  · refine ⟨false, ?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      simpa using hw
    · rw [wv_top2, hw, hu]
      simp
  · refine ⟨true, ?_, ?_⟩
    · apply BitVec.eq_of_toNat_eq
      simpa using hw
    · rw [wv_top2, hw, hu]
      simp

end VG.Proof.Bignum.AArch64.WindowLazy
