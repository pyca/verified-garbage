module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.TransferGeometry
import VerifiedGarbage.Proof.Mont.Words32Parts

/-! Saved exponents and compact Miller–Rabin numbers retain their exact values. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.Generation

theorem save_exponent {s : State} {base : Addr} {n bytes : Nat}
    (scr : Scr s base bytes) (hn : n ≤ 48) (capacity : 40960 ≤ bytes) :
    WP isa (transferWords (saveExponentTransfers n)) s fun t =>
      val32 t.mem base (slot n 8) (2 * n) = val32 s.mem base (Layout.arithmetic + 160) (2 * n) ∧
      val32 t.mem base (slot n 8 + 8 * n) 2 = val32 s.mem base (Layout.arithmetic + 64) 2 ∧
      Outs base (transferRanges (saveExponentTransfers n)) s.mem t.mem ∧ Keeps [.eax] s t := by
  refine WP.mono (transfer_words scr ((save_exponent_plan hn).mono capacity)) fun t ⟨values, F, K⟩ =>
    ⟨?_, ?_, F, K⟩
  · exact values ⟨2 * n, slot n 8, Layout.arithmetic + 160⟩ (by simp [saveExponentTransfers])
  · exact values ⟨2, slot n 8 + 8 * n, Layout.arithmetic + 64⟩ (by simp [saveExponentTransfers])

theorem compact_numbers {s : State} {base : Addr} {n bytes : Nat}
    (scr : Scr s base bytes) (hn : n ≤ 48) (capacity : 40960 ≤ bytes) :
    WP isa (transferWords (compactTransfers n)) s fun t =>
      (∀ j ∈ [(0, 0), (5, 3), (7, 4), (9, 6), (10, 7)],
        val32 t.mem base (Layout.arithmetic + Spec.Rsa.Mont.arrAt n j.1) (2 * n) =
          val32 s.mem base (slot n j.2) (2 * n)) ∧
      val32 t.mem base (Layout.arithmetic + Spec.Rsa.Mont.arrAt n 27) (2 * n) =
        val32 s.mem base (slot n 8) (2 * n) ∧
      val32 t.mem base (Layout.arithmetic + Spec.Rsa.Mont.arrAt n 27 + 8 * n) 2 =
        val32 s.mem base (slot n 8 + 8 * n) 2 ∧
      Outs base (transferRanges (compactTransfers n)) s.mem t.mem ∧ Keeps [.eax] s t := by
  refine WP.mono (transfer_words scr ((compact_plan hn).mono capacity)) fun t ⟨values, F, K⟩ => ?_
  have exp := values ⟨2 * n + 2, Layout.arithmetic + Spec.Rsa.Mont.arrAt n 27, slot n 8⟩
    (by simp [compactTransfers])
  obtain ⟨low, high⟩ := val32_parts (j := 2 * n) (k := 2) exp
  rw [show 4 * (2 * n) = 8 * n by omega] at high
  refine ⟨?_, low, high, F, K⟩
  intro j hj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl
  · exact values (compactNumberTransfer n 0 0) (by simp [compactTransfers])
  · exact values (compactNumberTransfer n 5 3) (by simp [compactTransfers])
  · exact values (compactNumberTransfer n 7 4) (by simp [compactTransfers])
  · exact values (compactNumberTransfer n 9 6) (by simp [compactTransfers])
  · exact values (compactNumberTransfer n 10 7) (by simp [compactTransfers])

end VG.Proof.Dsa.X86.Generation
