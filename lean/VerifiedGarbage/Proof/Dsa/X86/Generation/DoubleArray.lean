module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.Reduce
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain

/-! # Exact doubling from the already verified RSA carry chain -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.Keys (Keep num)
open VG.Impl.Rsa.X86.KeyRt (Lay)

theorem double_array {L : Lay} {s : State} {base : Addr} {bytes len count j : Nat}
    (h : RtWs L s base bytes len count) (hj : j < count)
    (bound : 2 * num s.mem base (kw len) j < 2 ^ (32 * kw len)) :
    WP isa (Impl.Dsa.X86.Generation.doubleArray L j) s fun t =>
      RtWs L t base bytes len count ∧ Keep base (kw len) [j] [] s.mem t.mem ∧
      num t.mem base (kw len) j = 2 * num s.mem base (kw len) j ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  refine WP.mono (chainAdd_ok h hj hj hj false) ?_
  rintro t ⟨ht, frame, ⟨c, _, value⟩, K⟩
  change num t.mem base (kw len) j + 2 ^ (32 * kw len) * c.toNat =
    num s.mem base (kw len) j + num s.mem base (kw len) j at value
  refine ⟨ht, frame, ?_, K⟩
  have zero : c = false := by cases c <;> simp_all only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one] <;> omega
  rw [zero] at value
  simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at value
  omega

end VG.Proof.Dsa.X86.Generation
