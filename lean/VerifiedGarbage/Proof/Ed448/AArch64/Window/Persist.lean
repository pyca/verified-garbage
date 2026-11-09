module

public import VerifiedGarbage.Proof.Ed448.AArch64.Window.Front
import VerifiedGarbage.Proof.Ed448.AArch64.Window.CopyK

/-!
# Ed448 verification on AArch64: what every phase keeps

Untrusted: everything here is checked by Lean. The saved registers and the
challenge's copy (`Persist`), kept by a frame that keeps their bytes
(`Persist.of_frame`), such as the field operations' (`Outside2`).
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Window

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (ld st slot ACC BITS)
open VG.Impl.X448.AArch64.Fast (saved SAVE VSAVE)
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 ofs Saved)
open VG.Proof.X448.AArch64.Fast (SavedX SavedV)
open VG.Proof.X448.AArch64.Base (Bits)
open VG.Spec.Ed448 (Point)

/-- The saved registers and the challenge's copy. -/
structure Persist (base : Addr) (g : Reg → BitVec 64) (gv : VReg → BitVec 128) (b : Nat → BitVec 8) (m : Mem) :
    Prop where
  saved : Saved base g m
  savedX : SavedX base g m
  savedV : SavedV base gv m
  lrs : VG.Proof.Ed448.AArch64.LrSaved base g m
  kb : KBytes base m b

/-- A frame that keeps `[0, 64)`, `[2880, 3072)` and `[4736, 4864)`. -/
theorem Persist.of_frame {base : Addr} {g gv b} {m m' : Mem} (h : Persist base g gv b m)
    (hf : ∀ x, (ofs base x < 64 ∨ (2880 ≤ ofs base x ∧ ofs base x < 3072) ∨
      (4736 ≤ ofs base x ∧ ofs base x < 4864)) → m' x = m x) : Persist base g gv b m' := by
  have hw : ∀ d, (d + 8 ≤ 64 ∨ (2880 ≤ d ∧ d + 8 ≤ 3072)) → d + 8 ≤ 8192 → word m' base d = word m base d :=
    fun d hd hd' => Mem.readW_congr fun i hi => (hf _ (by
      rw [VG.Proof.X448.AArch64.ofs_off base (by omega)]; omega)).symm |>.symm
  have hV : VSAVE = 4736 := rfl
  have hS : SAVE = 2880 := rfl
  refine ⟨⟨(hw 0 (by decide) (by decide)).trans h.saved.1, (hw 8 (by decide) (by decide)).trans h.saved.2⟩,
    fun k hk => (hw _ (by omega) (by omega)).trans (h.savedX k hk),
    h.savedV.frame fun d h1 h2 => hf _ (by rw [ofs_off0' base (by omega)]; omega),
    (hw LRS (by simp only [LRS]; omega) (by simp only [LRS]; omega)).trans h.lrs,
    h.kb.of_frame fun i hi => hf _ (by rw [kb_ofs base hi]; simp only [KB]; omega)⟩

theorem Persist.outside2 {base : Addr} {g gv b} {m m' : Mem} (h : Persist base g gv b m)
    (hf : Outside2 base 64 2816 ACC 1152 m m') : Persist base g gv b m' :=
  h.of_frame fun x hx => hf x (by omega) (by simp only [ACC]; omega)

end VG.Proof.Ed448.AArch64.Window
