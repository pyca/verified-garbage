module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameWords
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem

/-! # Arithmetic and hash helpers preserve the persistent search slots -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.Proof.Mont VG.Impl.Dsa.X86.Generation

theorem FrameWords.keep {s t : Mem} {base : Addr} {words : Nat → BitVec 32} {rs : List Region}
    (R : FrameWords s base words) (O : Frame rs s t)
    (apart : ∀ r ∈ rs, Region.Disjoint ⟨base, frameBytes⟩ r) : FrameWords t base words := by
  intro i hi
  rw [O.readW (r := ⟨base, frameBytes⟩)
    (Offset.contains_base _ (by unfold frameBytes; omega) (by omega)) apart (by decide), R i hi]

theorem FrameWords.exists (mem : Mem) (base : Addr) : ∃ words, FrameWords mem base words :=
  ⟨fun i => mem.readW (off base (4 * i)) 32, fun _ _ => rfl⟩
end VG.Proof.Dsa.X86.Generation
