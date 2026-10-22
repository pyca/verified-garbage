module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.Trial
public import VerifiedGarbage.Proof.Mont.X86.Inverse
public import VerifiedGarbage.Proof.Mont.X86.Instr

/-! Trial-prime inverses reuse the verified runtime Montgomery inverse. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86

theorem trial_inverse (s : State) (odd : (s.gpr .ebx).toNat % 2 = 1) :
    WP isa (.block Impl.Dsa.X86.Generation.trialInverse) s fun t =>
      ((s.gpr .ebx).toNat * (t.gpr .esi).toNat + 1) % 2 ^ 16 = 0 ∧
      t.mem = s.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .esi] s t := by
  unfold Impl.Dsa.X86.Generation.trialInverse
  refine WP.block_append (WP.mono (Dynamic.inverse_ok s odd) ?_)
  rintro u ⟨inverse, K, mem⟩
  refine wp_movS rfl fun t U _ => WP.block_nil ⟨?_, by rw [U.mem, mem],
    (K.mono (by decide)).trans (U.keeps.mono (by decide))⟩
  rw [U.gpr]
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (by decide : 2 ^ 16 ∣ 2 ^ 32)
    (Nat.dvd_of_mod_eq_zero inverse))

end VG.Proof.Dsa.X86.Generation
