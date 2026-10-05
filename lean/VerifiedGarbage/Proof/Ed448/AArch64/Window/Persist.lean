import VerifiedGarbage.Proof.Ed448.AArch64.Window.Front
import VerifiedGarbage.Proof.Ed448.AArch64.Window.Table

/-!
# Ed448 verification on AArch64: what every phase keeps

Untrusted: everything here is checked by Lean. The saved registers and the
challenge's copy (`Persist`), and the bits of `S` and `R`'s coordinates, are
kept by `tabInit` (`IFrame`), the table's loop (`TFrame`) and the field
operations (`Outside2`).
-/

namespace VG.Proof.Ed448.AArch64.Window

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (ld st slot ACC BITS)
open VG.Impl.X448.AArch64.Fast (saved SAVE VSAVE)
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 ofs Saved)
open VG.Proof.X448.AArch64.Fast (SavedX SavedV)
open VG.Proof.X448.AArch64.Base (Bits)

/-- The saved registers and the challenge's copy. -/
structure Persist (base : Addr) (g : Reg → BitVec 64) (gv : VReg → BitVec 128) (b : Nat → BitVec 8) (m : Mem) :
    Prop where
  saved : Saved base g m
  savedX : SavedX base g m
  savedV : SavedV base gv m
  kb : KBytes base m b

/-- A frame that keeps `[0, 64)`, `[2880, 3584)` and `[4736, 4864)`. -/
theorem Persist.of_frame {base : Addr} {g gv b} {m m' : Mem} (h : Persist base g gv b m)
    (hf : ∀ x, (ofs base x < 64 ∨ (2880 ≤ ofs base x ∧ ofs base x < 3584) ∨
      (4736 ≤ ofs base x ∧ ofs base x < 4864)) → m' x = m x) : Persist base g gv b m' := by
  have hw : ∀ d, (d + 8 ≤ 64 ∨ (2880 ≤ d ∧ d + 8 ≤ 3584)) → d + 8 ≤ 8192 → word m' base d = word m base d :=
    fun d hd hd' => Mem.readW_congr fun i hi => (hf _ (by
      rw [VG.Proof.X448.AArch64.ofs_off base (by omega)]; omega)).symm |>.symm
  have hV : VSAVE = 4736 := rfl
  have hS : SAVE = 2880 := rfl
  refine ⟨⟨(hw 0 (by decide) (by decide)).trans h.saved.1, (hw 8 (by decide) (by decide)).trans h.saved.2⟩,
    fun k hk => (hw _ (by omega) (by omega)).trans (h.savedX k hk),
    h.savedV.frame fun d h1 h2 => hf _ (by rw [ofs_off0' base (by omega)]; omega),
    h.kb.of_frame fun i hi => hf _ (by rw [kb_ofs base hi]; simp only [KB]; omega)⟩

theorem Persist.iframe {base : Addr} {g gv b} {m m' : Mem} (h : Persist base g gv b m) (hf : IFrame base m m') :
    Persist base g gv b m' :=
  h.of_frame fun x hx => hf x (by omega) (by simp only [RX]; omega) (by simp only [RY, CAN]; omega)

theorem Persist.tframe {base : Addr} {g gv b} {m m' : Mem} (h : Persist base g gv b m) (hf : TFrame base m m') :
    Persist base g gv b m' :=
  h.of_frame fun x hx => hf x (by omega) (by simp only [ACC]; omega) (by simp only [TAB]; omega)

theorem Persist.outside2 {base : Addr} {g gv b} {m m' : Mem} (h : Persist base g gv b m)
    (hf : Outside2 base 64 2816 ACC 1152 m m') : Persist base g gv b m' :=
  h.of_frame fun x hx => hf x (by omega) (by simp only [ACC]; omega)

/-- The bits of `S`, through `IFrame` and `TFrame`. -/
theorem Bits.iframe {base : Addr} {k : Nat} {m m' : Mem} (h : Bits 57 base k m) (hf : IFrame base m m') :
    Bits 57 base k m' := fun t ht => by
  rw [hf _ (by rw [bits_ofs base (by omega)]; simp only [BITS]; omega)
    (by rw [bits_ofs base (by omega)]; simp only [BITS, RX]; omega)
    (by rw [bits_ofs base (by omega)]; simp only [BITS, RY, CAN]; omega)]
  exact h t ht

theorem Bits.tframe {base : Addr} {k : Nat} {m m' : Mem} (h : Bits 57 base k m) (hf : TFrame base m m') :
    Bits 57 base k m' := fun t ht => by
  rw [hf _ (by rw [bits_ofs base (by omega)]; simp only [BITS]; omega)
    (by rw [bits_ofs base (by omega)]; simp only [BITS, ACC]; omega)
    (by rw [bits_ofs base (by omega)]; simp only [BITS, TAB]; omega)]
  exact h t ht

/-- `R`'s coordinates at `RX` and `RY`, through `TFrame` and `Outside2`. -/
theorem rlimbs_tframe {base : Addr} {m m' : Mem} (hf : TFrame base m m') {o : Nat} (ho : o = RX ∨ o = RY) {i : Nat}
    (hi : i < 8) : limbs m' base o i = limbs m base o i := by
  have hn : o + 8 * i + 8 ≤ 8192 := by rcases ho with rfl | rfl <;> simp only [RX, RY, CAN] <;> omega
  refine congrArg BitVec.toNat (Mem.readW_congr fun j hj => (hf _ ?_ ?_ ?_).symm |>.symm) <;>
    rw [VG.Proof.X448.AArch64.ofs_off base (by omega)] <;> rcases ho with rfl | rfl <;>
    simp only [RX, RY, CAN, ACC, TAB] <;> omega

theorem rlimbs_outside2 {base : Addr} {m m' : Mem} (hf : Outside2 base 64 2816 ACC 1152 m m') {o : Nat}
    (ho : o = RX ∨ o = RY) {i : Nat} (hi : i < 8) : limbs m' base o i = limbs m base o i := by
  have hn : o + 8 * i + 8 ≤ 8192 := by rcases ho with rfl | rfl <;> simp only [RX, RY, CAN] <;> omega
  refine congrArg BitVec.toNat (hf.word ?_ ?_ hn) <;> rcases ho with rfl | rfl <;>
    simp only [RX, RY, CAN, ACC] <;> omega

end VG.Proof.Ed448.AArch64.Window
