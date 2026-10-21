module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyInverse
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.InvStep
import VerifiedGarbage.Proof.Rsa.X86.KeyCopy
import VerifiedGarbage.Proof.Rsa.X86.KeyWord
import VerifiedGarbage.Proof.Rsa.X86.KeySub

/-! # Initialize the native inverse's Euclidean bank and negated modulus -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

structure InverseReady (B : Addr) (n a m : Nat) (s : State) : Prop where
  modulus : num s.mem B n aM = m
  negated : num s.mem B n aNM + m = 2 ^ (32 * n)
  zero : num s.mem B n aZero = 0
  initial : bank s.mem B n 0 = (a, m, 1, 0)

theorem inverseBank_ok {s : State} {B : Addr} {Z n a m : Nat}
    (h : Ws s B Z n 15) (input : num s.mem B n 0 = a) (modulus : num s.mem B n aM = m)
    (positive : 0 < m) (zero : num s.mem B n aZero = 0)
    (x₁ : num s.mem B n 2 = 0) (x₂ : num s.mem B n 3 = 0) :
    WP isa (inverseBank n) s fun t =>
      Ws t B Z n 15 ∧ Keep B n [1, 2, aNM] [] s.mem t.mem ∧ InverseReady B n a m t ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have f0 := h.fit64 (j := 0) (by decide)
  have f1 := h.fit64 (j := 1) (by decide)
  have f2 := h.fit64 (j := 2) (by decide)
  have f3 := h.fit64 (j := 3) (by decide)
  have fm := h.fit64 (j := aM) (by decide)
  have fz := h.fit64 (j := aZero) (by decide)
  unfold inverseBank seqs
  refine WP.seq (WP.mono (copy_ok h (by decide) (by decide)) fun u ⟨hu, Ou, v1, Ku, _⟩ => ?_)
  have two : num u.mem B n 2 = 0 := by rw [Ou.num (by decide) (by simp) f2, x₁]
  refine WP.seq (WP.mono (setOne_ok hu (by decide)) fun v ⟨hv, Ov, v2, Kv⟩ => ?_)
  rw [two, Nat.zero_div, Nat.mul_zero, Nat.add_zero] at v2
  have z : num v.mem B n aZero = 0 := by
    rw [Ov.num (by decide) (by simp) fz, Ou.num (by decide) (by simp) fz, zero]
  have mV : num v.mem B n aM = m := by
    rw [Ov.num (by decide) (by simp) fm, Ou.num (by decide) (by simp) fm, modulus]
  refine WP.mono (sub3_ok hv (by decide) (by decide) (by decide) (by decide) (by decide))
    fun t ⟨ht, Ot, subtract, bit, Kt⟩ => ?_
  rw [z, mV, Nat.zero_add] at subtract
  have borrow : (t.gpr .ebx).toNat = 1 := by
    by_cases p : (t.gpr .ebx).toNat = 0
    · rw [p, Nat.mul_zero] at subtract
      omega
    · omega
  rw [borrow, Nat.mul_one] at subtract
  have one : num t.mem B n 1 = m := by
    rw [Ot.num (by decide) (by simp) f1, Ov.num (by decide) (by simp) f1, v1, modulus]
  have twoT : num t.mem B n 2 = 1 := by rw [Ot.num (by decide) (by simp) f2, v2]
  have value0 : num t.mem B n 0 = a := by
    rw [Ot.num (by decide) (by simp) f0, Ov.num (by decide) (by simp) f0,
      Ou.num (by decide) (by simp) f0, input]
  have value3 : num t.mem B n 3 = 0 := by
    rw [Ot.num (by decide) (by simp) f3, Ov.num (by decide) (by simp) f3,
      Ou.num (by decide) (by simp) f3, x₂]
  refine ⟨ht, (Ou.join Ov (js := [1, 2, aNM]) (ds := [])).join Ot
    (js := [1, 2, aNM]) (ds := []), ⟨?_, subtract, ?_, ?_⟩,
    (Ku.mono (by decide)).trans ((Kv.mono (by decide)).trans Kt)⟩
  · rw [Ot.num (by decide) (by simp) fm, mV]
  · rw [Ot.num (by decide) (by simp) fz, z]
  · simp only [bank, Nat.zero_add, value0, one, twoT, value3]

end VG.Proof.RsaKeyGen.X86.Key
