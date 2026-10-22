module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.HalvingState

/-! The shared parity counter preserves both candidate arrays. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.Keys (Keep num slot)
open VG.Impl.Rsa.X86.KeyRt (Lay)

theorem halving_count {L : Lay} {s : State} {base : Addr} {bytes len count value twos remaining : Nat}
    (h : HalvingTemp L base bytes len count value twos remaining s)
    (arrays : 2 ≤ count) (bound : twos ≤ 16384) :
    WP isa (.block (Impl.Rsa.X86.KeyRt.countEven L 28 20 0)) s fun t =>
      HalvingTemp L base bytes len count value (twos + (1 - value % 2)) remaining t ∧
      slot t.mem base 28 = 1 - value % 2 ∧
      Keep base (kw len) [] [28, 20] s.mem t.mem ∧ Keeps [.eax, .edx] s t := by
  refine WP.mono (count_even h.workspace (j := 0) (by omega) (by rw [h.twos]; exact bound)) ?_
  rintro t ⟨ht, F, bit, tc, K⟩
  rw [h.value] at bit tc
  rw [h.twos] at tc
  refine ⟨⟨⟨ht, ?_, tc, ?_⟩, ?_⟩, bit, F, K⟩
  · exact (F.num (by simp) (by decide) (h.workspace.ws.fit64 (by omega : 0 < count))).trans h.value
  · exact (F.slot (by decide) (by decide)).trans h.remaining
  · exact (F.num (by simp) (by decide) (h.workspace.ws.fit64 (by omega : 1 < count))).trans h.temp

end VG.Proof.Dsa.X86.Generation
