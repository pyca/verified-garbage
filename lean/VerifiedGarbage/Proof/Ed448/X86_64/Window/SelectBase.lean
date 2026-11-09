module

public import VerifiedGarbage.Proof.Ed448.X86_64.Window.Scan
public import VerifiedGarbage.Impl.Ed448.X86_64.Window
public import VerifiedGarbage.Proof.Ed448.X86_64.Window.Mask
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Register
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Impl.Ed448.X86_64.WindowRegister

/-! Constant-time selection of the fixed-base verification window point. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Window

open VG VG.X86_64 VG.Impl.Ed448.X86_64 VG.Impl.Ed448.X86_64.Window VG.Proof.Ed448.X86_64
open VG.Proof.X448.X86_64 (Scr Index Env E Keep mask cswapE opSwap)
open VG.Impl.X448.X86_64 (BITS slot)

private theorem entry_words : ∀ i < 17,
    VG.Proof.X448.toFe (VG.Proof.X448.X86_64.wv (words7 (Impl.Ed448.SignedWindow.entry i).1.val)) =
      (Impl.Ed448.SignedWindow.entry i).1 ∧
    VG.Proof.X448.toFe (VG.Proof.X448.X86_64.wv (words7 (Impl.Ed448.SignedWindow.entry i).2.val)) =
      (Impl.Ed448.SignedWindow.entry i).2 := by decide +kernel

/-- Selection changes only the selected coordinates and two temporary coordinates. -/
def SelKeeps (e e' : Env) : Prop :=
  ∀ j, j ≠ 3 → j ≠ 4 → j ≠ 8 → j ≠ 9 → e' j = e j

theorem base_pick (c : Nat) :
    PickOk (fun i => chooseConst (if c = 0 then (Impl.Ed448.SignedWindow.entry i).1 else (Impl.Ed448.SignedWindow.entry i).2))
      (fun _ _ i => if c = 0 then (Impl.Ed448.SignedWindow.entry i).1 else (Impl.Ed448.SignedWindow.entry i).2) := by
  intro i hi s base hs sw hz
  refine WP.mono (chooseConst_ok _ hz) fun u ⟨eu, ku⟩ => ⟨?_, ku⟩
  rw [eu]
  cases sw
  · rfl
  · simp only [ite_true]
    split
    · exact (entry_words i hi).1
    · exact (entry_words i hi).2

end VG.Proof.Ed448.X86_64.Window
