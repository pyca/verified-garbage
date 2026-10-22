module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.ParentConstants
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Transfer
import VerifiedGarbage.Proof.Mont.Words32Offset
import VerifiedGarbage.Proof.Mont.X86.ContextLayout

/-! Seed candidate factorization without disturbing the reusable Montgomery context. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem candidate_transfer {s : State} {base : Addr} {bytes n m : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes)
    (C : ParentContext base n m s) (hn : n ≤ 48) :
    WP isa (candidateTransfer n).code s fun t =>
      ParentContext base n m t ∧
      val32 t.mem (off base Layout.arithmetic) 160 (2 * n) = m ∧
      (∀ j < 9, wordsVal t.mem base (slot n j) n = wordsVal s.mem base (slot n j) n) ∧
      Outside base (Layout.arithmetic + 160) (8 * n) s.mem t.mem ∧ Keeps [.eax] s t := by
  have fit := candidate_transfer_fit hn
  have fit' : TransferFits bytes (candidateTransfer n) :=
    ⟨Nat.le_trans fit.1 capacity, Nat.le_trans fit.2.1 capacity, fit.2.2⟩
  refine WP.mono (word_transfer scr fit') fun t ⟨value, K, F⟩ => ?_
  have frame : Outside base (Layout.arithmetic + 160) (8 * n) s.mem t.mem := by
    simpa only [candidateTransfer, show 4 * (2 * n) = 8 * n by omega] using F
  refine ⟨C.outside_keep K (by decide) (by decide) frame
    (.inl (by simp only [slot, stride, Layout.arithmetic]; omega)) (by decide), ?_, ?_, frame, K⟩
  · rw [val32_off]
    simp only [candidateTransfer] at value
    change val32 t.mem base (Layout.arithmetic + 160) (2 * n) = m
    rw [value, ← wordsVal_eq_val32]
    exact C.modulus.val
  · intro j hj
    have bound := slot_bound (n := n) hj
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    apply frame.val32
    · left
      simp only [contextBytes, slot, stride, Layout.arithmetic] at bound ⊢
      omega
    · have nw := scr.nowrap
      simp only [contextBytes, slot, stride] at bound ⊢
      omega

end VG.Proof.Dsa.X86.Generation
