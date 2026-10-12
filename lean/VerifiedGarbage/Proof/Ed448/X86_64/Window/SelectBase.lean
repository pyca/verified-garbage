module

public import VerifiedGarbage.Proof.Ed448.X86_64.Window.Direct
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! Constant-time selection of the fixed-base verification window point. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Window

open VG VG.X86_64 VG.Impl.Ed448.X86_64 VG.Impl.Ed448.X86_64.Window VG.Proof.Ed448.X86_64
open VG.Proof.X448.X86_64 (Scr Index Env E Keep mask cswapE opSwap)
open VG.Impl.X448.X86_64 (BITS slot)

private theorem entry_words : ∀ i < 16,
    VG.Proof.X448.toFe (VG.Proof.X448.X86_64.wv (words7 (Impl.Ed448.Window.entry i).1.val)) =
      (Impl.Ed448.Window.entry i).1 ∧
    VG.Proof.X448.toFe (VG.Proof.X448.X86_64.wv (words7 (Impl.Ed448.Window.entry i).2.val)) =
      (Impl.Ed448.Window.entry i).2 := by decide +kernel

/-- Selection changes only the selected coordinates and two temporary coordinates. -/
def SelKeeps (e e' : Env) : Prop :=
  ∀ j, j ≠ 3 → j ≠ 4 → j ≠ 8 → j ≠ 9 → e' j = e j

theorem base_entry_ok {s : State} {base : Addr} (hs : Scr s base) {k t i : Nat}
    (ht : t + 4 ≤ 456) (hi : i < 16) (hb : s.gpr .rbx = BitVec.ofNat 64 t) (bs : Bits base BITS k s) :
    WP isa (.block (baseEntry i)) s fun u =>
      Keep base s u ∧
      (E u.mem base 8, E u.mem base 9) =
        (if Proof.Ed448.Window.digit k t = i then Impl.Ed448.Window.entry i
          else (E s.mem base 8, E s.mem base 9)) ∧
      SelKeeps (E s.mem base) (E u.mem base) := by
  rw [baseEntry, List.append_assoc, WP.block_append_iff]
  refine WP.mono (mask_bits_ok hs (by decide) ht hi hb bs) fun s1 ⟨c1, k1, m1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (selectConst_ok (k1.scr hs) 8 _ (entry_words i hi).1 c1)
    fun s2 ⟨k2, c2, e2⟩ => ?_
  refine WP.mono (selectConst_ok (k2.scr (k1.scr hs)) 9 _ (entry_words i hi).2 (c2.trans c1))
    fun u ⟨ku, _, eu⟩ => ?_
  refine ⟨(k1.trans k2).trans ku, ?_, ?_⟩
  · rw [eu, e2, m1]
    by_cases he : Proof.Ed448.Window.digit k t = i <;> simp [he]
  · intro j _ _ h8 h9
    rw [eu, e2, m1]
    simp only [Function.update_of_ne h8, Function.update_of_ne h9]

private def picked (xs : List Nat) (d : Nat) (q : Spec.X448.Fe × Spec.X448.Fe) :=
  xs.foldl (fun q i => if d = i then Impl.Ed448.Window.entry i else q) q

private theorem picked_eq (xs : List Nat) (d : Nat) (q : Spec.X448.Fe × Spec.X448.Fe) :
    picked xs d q = if d ∈ xs then Impl.Ed448.Window.entry d else q := by
  induction xs generalizing q with
  | nil => simp [picked]
  | cons i xs ih =>
    change picked xs d (if d = i then Impl.Ed448.Window.entry i else q) = _
    rw [ih]
    by_cases hi : d = i
    · subst i; simp
    · by_cases hx : d ∈ xs <;> simp [hi, hx]

private theorem entries_ok (xs : List Nat) (hx : ∀ i ∈ xs, i < 16)
    {s : State} {base : Addr} (hs : Scr s base) {k t : Nat}
    (ht : t + 4 ≤ 456) (hb : s.gpr .rbx = BitVec.ofNat 64 t) (bs : Bits base BITS k s) :
    WP isa (.block (xs.flatMap baseEntry)) s fun u => Keep base s u ∧
      (E u.mem base 8, E u.mem base 9) =
        picked xs (Proof.Ed448.Window.digit k t) (E s.mem base 8, E s.mem base 9) ∧
      SelKeeps (E s.mem base) (E u.mem base) := by
  induction xs generalizing s with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, rfl, fun _ _ _ _ _ => rfl⟩
  | cons i xs ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (base_entry_ok hs ht (hx i List.mem_cons_self) hb bs) fun v ⟨kv, ev, fv⟩ => ?_
    refine WP.mono (ih (fun j hj => hx j (List.mem_cons_of_mem _ hj)) (kv.scr hs)
      (by rw [kv.gpr _ (by decide), hb]) (bs.keep (by decide) (by decide) kv)) fun u ⟨ku, eu, fu⟩ => ?_
    refine ⟨kv.trans ku, ?_, fun j h3 h4 h8 h9 => (fu j h3 h4 h8 h9).trans (fv j h3 h4 h8 h9)⟩
    rw [eu, ev]; rfl

/-- The selected affine point, while preserving the accumulator and curve constant. -/
theorem selectBase_ok {s : State} {base : Addr} (hs : Scr s base) {k t : Nat}
    (ht : t + 4 ≤ 456) (hb : s.gpr .rbx = BitVec.ofNat 64 t) (bs : Bits base BITS k s) :
    WP isa (.block selectBase) s fun u => Keep base s u ∧
      (E u.mem base 8, E u.mem base 9) = Impl.Ed448.Window.entry (Proof.Ed448.Window.digit k t) ∧
      SelKeeps (E s.mem base) (E u.mem base) := by
  refine WP.mono (entries_ok (List.range 16) (fun i hi => List.mem_range.mp hi) hs ht hb bs)
    fun u ⟨ku, eu, fu⟩ => ⟨ku, ?_, fu⟩
  rw [eu, picked_eq]
  simp only [List.mem_range, Proof.Ed448.Window.digit_lt k t, ite_true]

end VG.Proof.Ed448.X86_64.Window
