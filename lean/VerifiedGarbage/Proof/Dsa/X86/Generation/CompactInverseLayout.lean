module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.CompactInverse
public import VerifiedGarbage.Proof.MillerRabin.Workspace

/-! Installing the inverse retains the established shared compact layout. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Spec.Rsa.Mont (wordAt arrWord wOf)

theorem compact_inverse_layout {s : State} {base : Addr} {bytes wsLen : Nat}
    (h : Scr s base bytes) (fit : 264 ≤ bytes)
    (layout : Spec.MillerRabin.Layout Spec.MillerRabin.compact s.mem base wsLen)
    (inverse : (w32 s.mem base 256 * (s.gpr .ecx).toNat + 1) % 2 ^ 32 = 0) :
    WP isa (.block Impl.Dsa.X86.Generation.compactInverse) s fun t =>
      Scr t base bytes ∧ Outside base 56 8 s.mem t.mem ∧
      Spec.MillerRabin.Layout Spec.MillerRabin.compact t.mem base wsLen ∧
      wOf t.mem base = wOf s.mem base ∧
      ((word t.mem base 256).toNat * (word t.mem base 56).toNat + 1) % 2 ^ 64 = 0 ∧
      Keeps [.eax, .ebx, .edx, .ebp] s t := by
  refine WP.mono (compact_inverse h fit inverse) ?_
  rintro t ⟨ht, F, inv, K⟩
  have width : wordAt t.mem base 6 = wordAt s.mem base 6 := F.word (by decide) (by decide)
  have pointers : ∀ j < 8, wordAt t.mem base (arrWord j) = wordAt s.mem base (arrWord j) := by
    intro j hj
    change word t.mem base (8 * (8 + j)) = word s.mem base (8 * (8 + j))
    exact F.word (by omega) (by omega)
  have stride : wordAt t.mem base 28 = wordAt s.mem base 28 := F.word (by decide) (by decide)
  obtain ⟨L, W⟩ := VG.Proof.MillerRabin.Workspace.compact_layout_header_congr width pointers stride layout
  exact ⟨ht, F, L, W, inv, K⟩

end VG.Proof.Dsa.X86.Generation
