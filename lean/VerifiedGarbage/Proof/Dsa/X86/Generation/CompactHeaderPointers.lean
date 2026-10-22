module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.CompactHeaderPointer

/-! Initialize the eight public pointers with one framed induction. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Spec.Rsa.Mont (arrAt)

theorem compact_header_pointers {s : State} {base : Addr} {bytes w : Nat}
    (h : Scr s base bytes) (fit : arrAt w 8 ≤ bytes) (zero : s.gpr .edx = 0) :
    ∀ n, n ≤ 8 →
    WP isa (.block ((List.range n).flatMap (compactHeaderPointer w))) s fun t =>
      Scr t base bytes ∧ Outside base 64 (8 * n) s.mem t.mem ∧
      (∀ j < n, word t.mem base (64 + 8 * j) = off base (arrAt w j)) ∧
      t.gpr .edx = 0 ∧ Keeps [.eax] s t
  | 0, _ => WP.block_nil ⟨h, Outside.refl _ _ _ _, fun _ h => by omega, zero, Keeps.refl _ _⟩
  | n + 1, bound => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (compact_header_pointers h fit zero n (by omega)) ?_)
    rintro u ⟨hu, F, pointers, zu, K⟩
    have head : 256 ≤ bytes := by unfold arrAt Spec.Rsa.Mont.hdrBytes at fit; omega
    have lastFits : arrAt w n + 1 ≤ bytes := by
      have mult : n * (8 * (w + 2)) < 8 * (8 * (w + 2)) :=
        Nat.mul_lt_mul_of_pos_right (by omega : n < 8) (by omega)
      unfold arrAt Spec.Rsa.Mont.hdrBytes at fit ⊢
      omega
    refine WP.mono (compact_header_pointer hu head (by omega) lastFits zu) ?_
    rintro t ⟨ht, F', ptr, zt, K'⟩
    refine ⟨ht, (F.mono (by omega) (by omega)).trans (F'.mono (by omega) (by omega)), ?_, zt, K.trans K'⟩
    intro j hj
    by_cases old : j < n
    · rw [F'.word (by omega) (by omega)]
      exact pointers j old
    · have eq : j = n := by omega
      subst j
      exact ptr

end VG.Proof.Dsa.X86.Generation
