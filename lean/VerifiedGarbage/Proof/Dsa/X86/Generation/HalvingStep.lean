module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.HalvingTemp
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HalvingCount
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HalvingSelect

/-! The native iteration implements the shared RSA conditional-halving step. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.Keys (Keep)
open VG.Impl.Rsa.X86.KeyRt (Lay)

theorem halving_step {L : Lay} {s : State} {base : Addr} {bytes len count value twos remaining : Nat}
    (h : HalvingState L base bytes len count value twos remaining s)
    (arrays : 2 ≤ count) (bound : twos ≤ 16384) (positive : 0 < remaining) :
    WP isa (Impl.Dsa.X86.Generation.halvingStep L) s fun t =>
      HalvingState L base bytes len count (VG.Proof.Rsa.halveStep (value, twos)).1
        (VG.Proof.Rsa.halveStep (value, twos)).2 (remaining - 1) t ∧
      Keep base (kw len) [0, 1] [28, 20, 56] s.mem t.mem ∧
      t.zf = some (decide (remaining - 1 = 0)) ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  unfold Impl.Dsa.X86.Generation.halvingStep
  refine WP.seq (WP.mono (halving_temp h arrays) ?_)
  rintro u ⟨hu, F, K⟩
  refine WP.seq (WP.mono (halving_count hu arrays bound) ?_)
  rintro v ⟨hv, bit, F', K'⟩
  refine WP.mono (halving_select hv arrays bit positive) ?_
  rintro t ⟨ht, F'', zf, K''⟩
  have pair : VG.Proof.Rsa.halveStep (value, twos) =
      (if value % 2 = 0 then value / 2 else value, twos + (1 - value % 2)) := by
    unfold VG.Proof.Rsa.halveStep
    by_cases even : value % 2 = 0
    · simp only [even, ite_true, Nat.sub_zero]
    · have odd : value % 2 = 1 := by omega
      simp only [odd, show ¬ (1 : Nat) = 0 by decide, ite_false, Nat.sub_self, Nat.add_zero]
  rw [pair]
  exact ⟨ht, (F.join F' (js := [0, 1]) (ds := [28, 20, 56])).join F'',
    zf, (K.trans (K'.mono (by decide))).trans K''⟩

end VG.Proof.Dsa.X86.Generation
