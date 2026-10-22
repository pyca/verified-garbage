module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.ReduceDivision
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar

/-! # Subtract the remainder and add one using existing RSA operations -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.Keys (Keep num slot)
open VG.Impl.Rsa.X86.KeyRt (Lay)

structure SubtractedState (L : Lay) (base : Addr) (bytes len count x q : Nat) (s : State) : Prop where
  workspace : RtWs L s base bytes len count
  quotient : num s.mem base (kw len) 0 = x / (2 * q)
  difference : num s.mem base (kw len) 5 = x - x % (2 * q)
  one : slot s.mem base Impl.Dsa.X86.Generation.reductionOne = 1
  bound : x < 2 ^ (32 * kw len)

theorem reduction_subtract {L : Lay} {s : State} {base : Addr} {bytes len count x q : Nat}
    (h : ReductionState L base bytes len count x q s) (hc : 6 ≤ count) :
    WP isa (Impl.Rsa.X86.KeyRt.sub3 L 5 4 1) s fun t =>
      SubtractedState L base bytes len count x q t ∧ Keep base (kw len) [5] [] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  refine WP.mono (sub3_ok h.workspace (o := 5) (a := 4) (b := 1) (by omega) (by omega) (by omega)) ?_
  rintro t ⟨ht, frame, value, borrow, K⟩
  rw [h.saved, h.remainder] at value
  have resultBound : num t.mem base (kw len) 5 < 2 ^ (32 * kw len) := val32_lt _ _ _ _
  have remBound := Nat.mod_le x (2 * q)
  have difference : num t.mem base (kw len) 5 = x - x % (2 * q) := by
    have cases : (t.gpr .ebx).toNat = 0 ∨ (t.gpr .ebx).toNat = 1 := by omega
    rcases cases with zero | one
    · rw [zero, Nat.mul_zero, Nat.add_zero] at value
      omega
    · rw [one, Nat.mul_one] at value
      omega
  have quotient := (frame.num (j := 0) (by simp) (by simp) (h.workspace.ws.fit64 (by omega))).trans h.quotient
  have one := (frame.slot (by decide : Impl.Dsa.X86.Generation.reductionOne + 4 ≤ Impl.Rsa.X86.Keys.hdr)
    (by simp)).trans h.one
  exact ⟨⟨ht, quotient, difference, one, h.bound⟩, frame, K⟩

theorem reduction_increment {L : Lay} {s : State} {base : Addr} {bytes len count x q : Nat}
    (h : SubtractedState L base bytes len count x q s) (hc : 6 ≤ count) :
    WP isa (.block (Impl.Rsa.X86.KeyRt.addLow L 5 Impl.Dsa.X86.Generation.reductionOne)) s fun t =>
      RtWs L t base bytes len count ∧ Keep base (kw len) [5] [] s.mem t.mem ∧
      num t.mem base (kw len) 5 = x + 1 - x % (2 * q) ∧
      num t.mem base (kw len) 0 = x / (2 * q) ∧ Keeps [.eax, .ecx, .edx] s t := by
  have even : num s.mem base (kw len) 5 % 2 = 0 := by
    rw [h.difference]
    have divEq := Nat.mod_add_div x (2 * q)
    have diff : x - x % (2 * q) = 2 * q * (x / (2 * q)) := by omega
    rw [diff]
    simp [Nat.mul_mod]
  refine WP.mono (addLow_ok h.workspace (j := 5) (sl := Impl.Dsa.X86.Generation.reductionOne)
    (by omega) (by decide)) ?_
  rintro t ⟨ht, frame, value, K, _⟩
  have result := value even (by rw [h.one])
  rw [h.difference, h.one] at result
  refine ⟨ht, frame, ?_, ?_, K⟩
  · rw [VG.Proof.Dsa.Generation.pReduction_sub]
    exact result
  · exact (frame.num (j := 0) (by simp) (by simp) (h.workspace.ws.fit64 (by omega))).trans h.quotient

end VG.Proof.Dsa.X86.Generation
