module

public import VerifiedGarbage.Proof.Ed448.AArch64.Window.Store
public import VerifiedGarbage.Proof.Ed448.AArch64.Window.Select
public import VerifiedGarbage.Proof.X448.AArch64.Base.AddGen
public import VerifiedGarbage.Proof.Ed448.AArch64.Window.Dbl
import VerifiedGarbage.Proof.X448.AArch64.Fast.Weave
public import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Call
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.X448.BaseAdd
public import VerifiedGarbage.Impl.X448.AArch64.Common
public import VerifiedGarbage.Proof.Framework.AArch64.Footprint
public import VerifiedGarbage.Proof.Framework.Semantics

/-!
# Ed448 verification on AArch64: the table of `[n](-A)`

Untrusted: everything here is checked by Lean. Entry `e` of the table as a
point (`TPt`) and its words' bounds (`TBnd`); a store of slots 3–5 to an
entry (`tabStore_pt`, `tabStore_bnd`), which keeps the other entries
(`TPt_outside`).
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Window

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (ld st slot ACC)
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 ofs)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd FKeep Same block_codeOf)
open VG.Impl.X448.AArch64.Fast (codeOf)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448.AArch64.Base (pt genEnv genPt temps addOps_ok zero_env next_ok)
open VG.Spec.Ed448 (Point)
open VG.Proof.X448 (addPt)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E
local notation "FV" => VG.Proof.X448.AArch64.Weak.F

/-! ## The entries -/

/-- Entry `e` of the table, as a point. -/
def TPt (m : Mem) (base : Addr) (e : Nat) : Point :=
  ⟨FV m base (TAB + 192 * e), FV m base (TAB + 192 * e + 64), FV m base (TAB + 192 * e + 128)⟩

/-- Entry `e`'s words below `Ib`. -/
def TBnd (m : Mem) (base : Addr) (e : Nat) : Prop := ∀ w < 24, (tw m base e w).toNat < Ib

/-- Coordinate `c` of entry `e` from the words `8c`, …, `8c + 7` of the entry. -/
theorem FV_entry (m m' : Mem) (base : Addr) {e c o : Nat} (ho : o = TAB + 192 * e + 64 * c)
    {o' : Nat} (h : ∀ i < 8, tw m base e (8 * c + i) = word m' base (o' + 8 * i)) :
    FV m base o = FV m' base o' := by
  simp only [VG.Proof.X448.AArch64.Weak.F]
  refine congrArg _ (VG.Proof.X448.Wide.valN_congr fun i hi => ?_)
  simp only [limbs]
  rw [← h i hi, tw]
  congr 2
  omega_arith

/-- After `tabStore` from slots 3–5 of `s`, entry `e` is their point, with their bounds. -/
theorem tabStore_pt {s t : State} {base : Addr} {e : Nat}
    (h : ∀ w < 24, word t.mem base (TAB + 192 * e + 8 * w) = word s.mem base (src w)) :
    TPt t.mem base e = pt (EV s.mem base) 3 4 5 := by
  have hs : ∀ c < 3, ∀ i < 8, tw t.mem base e (8 * c + i) = word s.mem base (slot (3 + c) + 8 * i) :=
    fun c hc i hi => by
      rw [tw, h _ (by omega_arith), src]
      congr 2
      all_goals (try simp only [slot])
      all_goals omega_arith
  simp only [TPt, pt]
  refine Point.mk.injEq _ _ _ _ _ _ |>.mpr ⟨?_, ?_, ?_⟩
  · exact FV_entry _ _ _ (e := e) (c := 0) (o := TAB + 192 * e) (by omega_arith) (hs 0 (by decide))
  · exact FV_entry _ _ _ (e := e) (c := 1) rfl (hs 1 (by decide))
  · exact FV_entry _ _ _ (e := e) (c := 2) rfl (hs 2 (by decide))

theorem tabStore_bnd {s t : State} {base : Addr} {e : Nat} (hb : BEnv s.mem base)
    (h : ∀ w < 24, word t.mem base (TAB + 192 * e + 8 * w) = word s.mem base (src w)) : TBnd t.mem base e := by
  intro w hw
  rw [tw, h w hw]
  have := hb ⟨3 + w / 8, by omega_arith⟩ (w % 8) (Nat.mod_lt _ (by decide))
  exact this

/-- Entries other than `e` are kept by a store to entry `e`. -/
theorem tw_outside {m m' : Mem} {base : Addr} {e : Nat} (h : Outside base (TAB + 192 * e) 192 m m')
    {e' w : Nat} (he : e' ≠ e) (he' : e' < 16) (hw : w < 24) :
    tw m' base e' w = tw m base e' w := by
  unfold tw
  refine h.word ?_ (by simp only [TAB]; omega_arith)
  rcases Nat.lt_or_gt_of_ne he with h1 | h1 <;> [left; right] <;> omega_arith

/-- An entry is its words. -/
theorem TPt_of_tw {m m' : Mem} {base : Addr} {e : Nat} (h : ∀ w < 24, tw m' base e w = tw m base e w) :
    TPt m' base e = TPt m base e := by
  have hc : ∀ c < 3, ∀ i < 8, tw m' base e (8 * c + i) = word m base (TAB + 192 * e + 64 * c + 8 * i) :=
    fun c hc i hi => by
      rw [h _ (by omega_arith)]
      unfold tw
      rw [show TAB + 192 * e + 8 * (8 * c + i) = TAB + 192 * e + 64 * c + 8 * i by omega_arith]
  unfold TPt
  rw [FV_entry m' m base (e := e) (c := 0) (o := TAB + 192 * e) (o' := TAB + 192 * e) (by omega_arith)
      (fun i hi => by rw [hc 0 (by decide) i hi, show TAB + 192 * e + 64 * 0 = TAB + 192 * e by omega_arith]),
    FV_entry m' m base (e := e) (c := 1) (o' := TAB + 192 * e + 64) rfl (fun i hi => hc 1 (by decide) i hi),
    FV_entry m' m base (e := e) (c := 2) (o' := TAB + 192 * e + 128) rfl (fun i hi => hc 2 (by decide) i hi)]

theorem TPt_outside {m m' : Mem} {base : Addr} {e : Nat} (h : Outside base (TAB + 192 * e) 192 m m')
    {e' : Nat} (he : e' ≠ e) (he' : e' < 16) : TPt m' base e' = TPt m base e' :=
  TPt_of_tw fun _ hw => tw_outside h he he' hw

end VG.Proof.Ed448.AArch64.Window
