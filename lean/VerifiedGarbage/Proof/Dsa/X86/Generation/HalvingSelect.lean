module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.HalvingState

/-! Select the halved array under the existing RSA mask, then count down. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.Keys (Keep num slot)
open VG.Impl.Rsa.X86.KeyRt (Lay)

theorem halving_select {L : Lay} {s : State} {base : Addr} {bytes len count value twos remaining : Nat}
    (h : HalvingTemp L base bytes len count value twos remaining s)
    (arrays : 2 ≤ count) (bit : slot s.mem base 28 = 1 - value % 2) (positive : 0 < remaining) :
    WP isa (.seq (Impl.Rsa.X86.KeyRt.sel L 0 0 1 28)
      (.block Impl.Dsa.X86.Generation.halvingNext)) s fun t =>
      HalvingState L base bytes len count (if value % 2 = 0 then value / 2 else value) twos (remaining - 1) t ∧
      Keep base (kw len) [0] [56] s.mem t.mem ∧
      t.zf = some (decide (remaining - 1 = 0)) ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  refine WP.seq (WP.mono (sel_ok h.workspace (o := 0) (a := 0) (b := 1) (sl := 28)
    (by omega) (by omega) (by omega) (by decide) (by rw [bit]; omega) (Or.inr (by decide))) ?_)
  rintro u ⟨hu, F, selected, K⟩
  rw [bit, h.value, h.temp] at selected
  have val : num u.mem base (kw len) 0 = if value % 2 = 0 then value / 2 else value := by
    by_cases even : value % 2 = 0
    · simpa only [even, Nat.sub_zero, ite_false, ite_true, show ¬ (1 : Nat) = 0 by decide] using selected
    · have odd : value % 2 = 1 := by omega
      simpa only [odd, Nat.sub_self, ite_true, show ¬ (1 : Nat) = 0 by decide, ite_false] using selected
  have tc : slot u.mem base 20 = twos := (F.slot (by decide) (by simp)).trans h.twos
  have rc : slot u.mem base 56 = remaining := (F.slot (by decide) (by simp)).trans h.remaining
  refine WP.mono (halving_next hu (by rw [rc]; exact positive)) ?_
  rintro t ⟨ht, F', remaining', zf, K'⟩
  rw [rc] at remaining' zf
  refine ⟨⟨ht, ?_, ?_, remaining'⟩, F.join F', zf, K.trans (K'.mono (by decide))⟩
  · exact (F'.num (by simp) (by decide) (h.workspace.ws.fit64 (by omega : 0 < count))).trans val
  · exact (F'.slot (by decide) (by simp)).trans tc

end VG.Proof.Dsa.X86.Generation
