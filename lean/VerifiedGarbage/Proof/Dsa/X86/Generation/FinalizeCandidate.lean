module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.InverseAt
public import VerifiedGarbage.Proof.Dsa.X86.Generation.CompactFrame

/-! Finalize the shared prepared-round contract after transferring the candidate. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation
open VG.Proof.Mont VG.Proof.Mont.X86

theorem finalize_candidate {s : State} {base : Addr} {bytes n candidate : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes)
    (C : ParentContext base n candidate s) (lower : 4 ≤ n) (upper : n ≤ 48)
    (large : 3 ≤ candidate) (odd : candidate % 2 = 1)
    (layout : Spec.MillerRabin.Layout Spec.MillerRabin.compact s.mem (off base Layout.arithmetic)
      (Layout.arithmeticBytes / 8))
    (width : Spec.Rsa.Mont.wOf s.mem (off base Layout.arithmetic) = n)
    (value : Spec.Rsa.Mont.numAt s.mem (off base Layout.arithmetic) n 0 = candidate)
    (witness : Spec.Rsa.Mont.numAt s.mem (off base Layout.arithmetic) n 5 = 1)
    (one : Spec.Rsa.Mont.numAt s.mem (off base Layout.arithmetic) n 9 = 2 ^ (64 * n) % candidate)
    (minus : Spec.Rsa.Mont.numAt s.mem (off base Layout.arithmetic) n 10 = candidate - 2 ^ (64 * n) % candidate)
    (exponent : Spec.Rsa.Mont.numAt s.mem (off base Layout.arithmetic) n 27 = Spec.MillerRabin.exponent candidate)
    (tail : word s.mem (off base Layout.arithmetic) (Spec.Rsa.Mont.arrAt n 27 + 8 * n) =
      BitVec.twoPow 64 ((Spec.Rsa.splitTwos (candidate - 1)).1 % 64)) :
    WP isa (.block ([.mov .ecx (.mem (VG.Impl.Mont.X86.sc 0))] ++
      enterArithmetic ++ compactInverse ++ leaveArithmetic)) s fun t =>
      Spec.MillerRabin.Layout Spec.MillerRabin.compact t.mem (off base Layout.arithmetic)
        (Layout.arithmeticBytes / 8) ∧
      Spec.MillerRabin.Prepared Spec.MillerRabin.compact t.mem (off base Layout.arithmetic) ∧
      Spec.Rsa.Mont.wOf t.mem (off base Layout.arithmetic) = n ∧
      Frame [⟨off base Layout.arithmetic, 256⟩] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  refine WP.mono (inverse_at scr capacity layout (compact_inverse_input C (by omega) value))
    fun t ⟨L, W, inv, F, K⟩ => ?_
  rw [width] at W
  have number : ∀ j < 28, Spec.Rsa.Mont.numAt t.mem (off base Layout.arithmetic) n j =
      Spec.Rsa.Mont.numAt s.mem (off base Layout.arithmetic) n j := fun _ hj =>
    compact_frame_number F upper hj
  have candidateT := (number 0 (by decide)).trans value
  refine ⟨L, ?_, W, F, K⟩
  dsimp only [Spec.MillerRabin.Prepared]
  rw [W, candidateT]
  refine ⟨large, odd, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Spec.Rsa.Mont.arrAt, Spec.Rsa.Mont.hdrBytes, Nat.zero_mul, Nat.add_zero,
      Spec.Rsa.Mont.wordAt, Spec.Rsa.Mont.minvWord, VG.Proof.Mont.word, off] using inv
  · rw [number 5 (by decide), witness]; omega
  · exact (number 9 (by decide)).trans one
  · exact (number 10 (by decide)).trans minus
  · exact (number 27 (by decide)).trans exponent
  · exact (compact_frame_tail F upper).trans tail

end VG.Proof.Dsa.X86.Generation
