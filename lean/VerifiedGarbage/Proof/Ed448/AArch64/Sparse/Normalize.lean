module

public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Table
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Const
public import VerifiedGarbage.Proof.Ed448.AArch64.Window.TableInit
import VerifiedGarbage.Proof.Ed448.AArch64.Point56.MulSlots
public import VerifiedGarbage.Proof.Ed448.AArch64.Window.Front
import VerifiedGarbage.Proof.Ed448.AArch64.Window.CopyK

/-! ### `Ed448.AArch64.Window.Persist`, which the modules that import this one used -/

section

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
      rw [VG.Proof.X448.AArch64.ofs_off base (by omega_using [hd, hi])]; omega_using [hd, hi])).symm |>.symm
  have hV : VSAVE = 4736 := rfl
  have hS : SAVE = 2880 := rfl
  refine ⟨⟨(hw 0 (by decide) (by decide)).trans h.saved.1, (hw 8 (by decide) (by decide)).trans h.saved.2⟩,
    fun k hk => (hw _ (by omega_using [hS, hk]) (by omega_using [hS, hk])).trans (h.savedX k hk),
    h.savedV.frame fun d h1 h2 => hf _ (by rw [ofs_off0' base (by omega_using [hV, h2])]; omega_using [hV, h1, h2]),
    (hw LRS (by simp only [LRS]; omega_using []) (by simp only [LRS]; omega_using [])).trans h.lrs,
    h.kb.of_frame fun i hi => hf _ (by rw [kb_ofs base hi]; simp only [KB]; omega_using [hi])⟩

theorem Persist.outside2 {base : Addr} {g gv b} {m m' : Mem} (h : Persist base g gv b m)
    (hf : Outside2 base 64 2816 ACC 1152 m m') : Persist base g gv b m' :=
  h.of_frame fun x hx => hf x (by omega_using [hx]) (by simp only [ACC]; omega_using [hx])

end VG.Proof.Ed448.AArch64.Window

end

end

/-! Normalize negative A's X coordinate once to the product output bound. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.X448.AArch64 (slot)
open VG.Proof.X448.AArch64 (Scr)
open VG.Proof.X448.AArch64.Weak (Index)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd FKeep Same)
open VG.Proof.Curve448.AArch64.Fast (Mb)
open VG.Proof.Ed448.AArch64.Window (slotPt)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

theorem normalizeKey_ok {s:State} {base:Addr} (hs:Scr s base) (hb:BEnv s.mem base) :
    WP isa normalizeKey s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Bnd Mb t.mem base (slot 6) ∧
      Same base [6,20] s.mem t.mem ∧ slotPt t.mem base=slotPt s.mem base := by
  unfold normalizeKey
  refine WP.seq (WP.mono (constE hs hb 20 1) fun a ⟨ab,asm,ae,_,ao,ak⟩ => ?_)
  have af:FKeep base s a:=⟨ak.mono (by decide),fun x hx _ => ao x (by simp only [slot] at hx ⊢;omega_using [hx])⟩
  refine Point56.mulOpK (af.scr hs) ab 6 6 20 (Or.inr (by decide))
    fun t tk tb tm tsm te => WP.block_nil ?_
  refine ⟨af.trans tk,tb,tm,?_,?_⟩
  · exact VG.Proof.X448.AArch64.Base.Same.mono (asm.append tsm) (by decide)
  · rw [slotPt,slotPt,te,ae]
    change (⟨EV s.mem base 6*1,EV s.mem base 7,1⟩:VG.Spec.Ed448.Point)=_
    rw [Fin.mul_one]

end VG.Proof.Ed448.AArch64.Sparse
