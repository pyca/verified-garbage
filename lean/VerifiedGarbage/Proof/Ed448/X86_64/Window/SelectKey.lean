import VerifiedGarbage.Proof.Ed448.X86_64.Window.Memory

/-! Constant-time selection from the runtime projective table. -/
namespace VG.Proof.Ed448.X86_64.Window

open VG VG.X86_64 VG.Impl.Ed448.X86_64 VG.Impl.Ed448.X86_64.Window VG.Proof.Ed448.X86_64
open VG.Proof.Ed448 (pt)
open VG.Proof.X448.X86_64 (Scr Index Env E F Keep mask cswapE opSwap)
open VG.Impl.X448.X86_64 (slot)

private theorem coord_keep {base : Addr} {s u : State} (h : Keep base s u) {i c : Nat}
    (hi : i < 16) (hc : c < 3) : F u.mem base (tabOffset i c) = F s.mem base (tabOffset i c) := by
  unfold F
  rw [h.mem.fe (by simp only [tabOffset, TAB]; omega) (by simp only [tabOffset, TAB]; omega)]

private theorem loadEntry_ok {s : State} {base : Addr} (hs : Scr s base) (i : Nat) (hi : i < 16) :
    WP isa (.block (loadEntry i)) s fun u => Keep base s u ∧
      E u.mem base = Function.update (Function.update (Function.update (E s.mem base)
        3 (tablePoint s.mem base i).X) 4 (tablePoint s.mem base i).Y) 5 (tablePoint s.mem base i).Z := by
  rw [loadEntry, List.append_assoc, WP.block_append_iff]
  refine WP.mono (load_ok hs 3 (a := tabOffset i 0) (by simp only [tabOffset, TAB]; omega)) fun s1 ⟨k1, e1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (load_ok (k1.scr hs) 4 (a := tabOffset i 1) (by simp only [tabOffset, TAB]; omega))
    fun s2 ⟨k2, e2⟩ => ?_
  refine WP.mono (load_ok (k2.scr (k1.scr hs)) 5 (a := tabOffset i 2) (by simp only [tabOffset, TAB]; omega))
    fun u ⟨ku, eu⟩ => ?_
  refine ⟨(k1.trans k2).trans ku, ?_⟩
  rw [eu, e2, e1, coord_keep k2 hi (by decide), coord_keep k1 hi (by decide), coord_keep k1 hi (by decide)]
  rfl

def KeyKeeps (e e' : Env) : Prop :=
  ∀ j : Index, j ≠ 3 → j ≠ 4 → j ≠ 5 → j ≠ 8 → j ≠ 9 → j ≠ 10 → e' j = e j

private theorem keyEntry_ok {s : State} {base : Addr} (hs : Scr s base) {o k t i : Nat}
    (ho : 2048 ≤ o) (hbnd : o + 456 ≤ 8192) (ht : t + 4 ≤ 456) (hi : i < 16)
    (hb : s.gpr .rbx = BitVec.ofNat 64 t) (bs : Bits base o k s) :
    WP isa (.block (keyEntry o i)) s fun u => Keep base s u ∧
      pt (E u.mem base) 8 9 10 = (if Proof.Ed448.Window.digit k t = i then tablePoint s.mem base i
        else pt (E s.mem base) 8 9 10) ∧ KeyKeeps (E s.mem base) (E u.mem base) := by
  rw [keyEntry, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadEntry_ok hs i hi) fun s1 ⟨k1, e1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mask_bits_ok (k1.scr hs) hbnd ht hi (by rw [k1.gpr _ (by decide), hb])
    (bs.keep ho hbnd k1)) fun s2 ⟨c2, k2, m2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cswapE (k2.scr (k1.scr hs)) 8 3 (by decide) c2) fun s3 ⟨k3, c3, e3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cswapE (k3.scr (k2.scr (k1.scr hs))) 9 4 (by decide) (c3.trans c2)) fun s4 ⟨k4, c4, e4⟩ => ?_
  refine WP.mono (cswapE (k4.scr (k3.scr (k2.scr (k1.scr hs)))) 10 5 (by decide) (c4.trans (c3.trans c2)))
    fun u ⟨ku, _, eu⟩ => ?_
  refine ⟨(((k1.trans k2).trans k3).trans k4).trans ku, ?_, ?_⟩
  · rw [eu, e4, e3, m2, e1]
    by_cases he : Proof.Ed448.Window.digit k t = i <;> simp [pt, opSwap, he]
  · intro j h3 h4 h5 h8 h9 h10
    rw [eu, e4, e3, m2, e1]
    simp only [opSwap, Function.update_of_ne h3, Function.update_of_ne h4,
      Function.update_of_ne h5, Function.update_of_ne h8, Function.update_of_ne h9, Function.update_of_ne h10]

private def picked (f : Nat → Spec.Ed448.Point) (xs : List Nat) (d : Nat) (q : Spec.Ed448.Point) :=
  xs.foldl (fun q i => if d = i then f i else q) q

private theorem picked_eq (f : Nat → Spec.Ed448.Point) (xs : List Nat) (d : Nat) (q : Spec.Ed448.Point) :
    picked f xs d q = if d ∈ xs then f d else q := by
  induction xs generalizing q with
  | nil => simp [picked]
  | cons i xs ih =>
    change picked f xs d (if d = i then f i else q) = _
    rw [ih]
    by_cases hi : d = i
    · subst i; simp
    · by_cases hx : d ∈ xs <;> simp [hi, hx]

private theorem entries_ok (xs : List Nat) (hx : ∀ i ∈ xs, i < 16)
    {s : State} {base : Addr} (hs : Scr s base) {o k t : Nat}
    (ho : 2048 ≤ o) (hbnd : o + 456 ≤ 8192) (ht : t + 4 ≤ 456)
    (hb : s.gpr .rbx = BitVec.ofNat 64 t) (bs : Bits base o k s)
    (f : Nat → Spec.Ed448.Point) (hf : ∀ i < 16, tablePoint s.mem base i = f i) :
    WP isa (.block (xs.flatMap (keyEntry o))) s fun u => Keep base s u ∧
      pt (E u.mem base) 8 9 10 = picked f xs (Proof.Ed448.Window.digit k t) (pt (E s.mem base) 8 9 10) ∧
      KeyKeeps (E s.mem base) (E u.mem base) := by
  induction xs generalizing s with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, rfl, fun _ _ _ _ _ _ _ => rfl⟩
  | cons i xs ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (keyEntry_ok hs ho hbnd ht (hx i List.mem_cons_self) hb bs) fun v ⟨kv, ev, fv⟩ => ?_
    refine WP.mono (ih (fun j hj => hx j (List.mem_cons_of_mem _ hj)) (kv.scr hs)
      (by rw [kv.gpr _ (by decide), hb]) (bs.keep ho hbnd kv)
      (fun j hj => (tablePoint_keep kv j hj).trans (hf j hj))) fun u ⟨ku, eu, fu⟩ => ?_
    refine ⟨kv.trans ku, ?_, fun j h3 h4 h5 h8 h9 h10 =>
      (fu j h3 h4 h5 h8 h9 h10).trans (fv j h3 h4 h5 h8 h9 h10)⟩
    rw [eu, ev, hf i (hx i List.mem_cons_self)]; rfl

/-- Every entry is read, with a mask deciding which one is retained. -/
theorem selectKey_ok {s : State} {base : Addr} (hs : Scr s base) {o k t : Nat}
    (ho : 2048 ≤ o) (hbnd : o + 456 ≤ 8192) (ht : t + 4 ≤ 456)
    (hb : s.gpr .rbx = BitVec.ofNat 64 t) (bs : Bits base o k s) :
    WP isa (.block (selectKey o)) s fun u => Keep base s u ∧
      pt (E u.mem base) 8 9 10 = tablePoint s.mem base (Proof.Ed448.Window.digit k t) ∧
      KeyKeeps (E s.mem base) (E u.mem base) := by
  refine WP.mono (entries_ok (List.range 16) (fun i hi => List.mem_range.mp hi) hs ho hbnd ht hb bs
    (tablePoint s.mem base) (fun _ _ => rfl)) fun u ⟨ku, eu, fu⟩ => ⟨ku, ?_, fu⟩
  rw [eu, picked_eq]
  simp only [List.mem_range, Proof.Ed448.Window.digit_lt k t, ite_true]

end VG.Proof.Ed448.X86_64.Window
