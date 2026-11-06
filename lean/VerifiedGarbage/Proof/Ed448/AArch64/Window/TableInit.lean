module

public import VerifiedGarbage.Proof.Ed448.AArch64.Window.Table
import VerifiedGarbage.Proof.Curve448.AArch64.Copy
import VerifiedGarbage.Proof.X448.AArch64.Weak.Counters
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.X448.AArch64.Base.Const
public import VerifiedGarbage.Impl.Curve448.AArch64
public import VerifiedGarbage.Proof.X448.AArch64.Mul
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# Ed448 verification on AArch64: copies between slots

Untrusted: everything here is checked by Lean. Copies between slots
(`copyS_ok`), which keep their values (`FV_of_limbs`) and bounds
(`ib_of_limbs`), and the point `(x, y, 1)` of slots 6–7 (`slotPt`).
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Window

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (ld st slot ACC)
open VG.Impl.X448.AArch64.Base (constSlot limb)
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside ofs)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448.AArch64.Base (pt constSlot_ok F_of_words bnd_of_words limb_lt)
open VG.Spec.Ed448 (Point)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E
local notation "FV" => VG.Proof.X448.AArch64.Weak.F

/-! ## The steps -/

/-- A copy between slots or from a slot to `RX` or `RY`. -/
theorem copyS_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat} (ho : o + 128 ≤ 8192)
    (ha : a + 128 ≤ 8192) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0) (hsep : o + 128 ≤ a ∨ a + 128 ≤ o) :
    WP isa (.block (Impl.Curve448.AArch64.copy o a)) s fun t =>
      (∀ i < 8, limbs t.mem base o i = limbs s.mem base a i) ∧ Outside base o 128 s.mem t.mem ∧
      Keeps VG.Proof.X448.AArch64.clob s t :=
  VG.Proof.Curve448.AArch64.copy_ok hs ho ha ho8 ha8 (Or.inr hsep)

theorem FV_of_limbs {m m' : Mem} {base : Addr} {o o' : Nat} (h : ∀ i < 8, limbs m' base o' i = limbs m base o i) :
    FV m' base o' = FV m base o := congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr h)

/-- The point `(x, y, 1)` of slots 6–7 (`-A`, once decoded). -/
def slotPt (m : Mem) (base : Addr) : Point := ⟨EV m base 6, EV m base 7, 1⟩

/-! ## The copies and constants -/

theorem limb_zero (w : Nat) : limb 0 w = 0 := by
  rw [limb, Fin.val_zero, Nat.zero_shiftRight, Nat.zero_mod]; rfl

/-! ## `tabInit` -/

/-- A slot equal limb by limb to a bounded slot is bounded. -/
theorem ib_of_limbs {m m' : Mem} {base : Addr} {o o' : Nat} (h : ∀ i < 8, limbs m' base o' i = limbs m base o i)
    (hb : Bnd Ib m base o) : Bnd Ib m' base o' := fun i hi => by rw [h i hi]; exact hb i hi

end VG.Proof.Ed448.AArch64.Window
