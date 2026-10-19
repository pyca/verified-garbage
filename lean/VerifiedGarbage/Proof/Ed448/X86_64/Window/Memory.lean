module

public import VerifiedGarbage.Proof.Ed448.X86_64.Window.Mask
public import VerifiedGarbage.Impl.Ed448.X86_64.Window
public import VerifiedGarbage.Proof.Ed448.Formulas
import VerifiedGarbage.Proof.X448.X86_64.Chain
import VerifiedGarbage.Proof.Framework.Block

/-! The projective table occupies a separate range of the existing scratch space. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Window

open VG VG.X86_64 VG.Impl.Ed448.X86_64 VG.Impl.Ed448.X86_64.Window VG.Proof.Ed448.X86_64
open VG.Proof.X448.X86_64 (Scr Index Env E F Keep Outside Outside2 off ofs clob copyOut_ok E_outside)
open VG.Impl.X448.X86_64 (slot copyOut W)

def Frame (base : Addr) (m u : Mem) := Outside2 base 64 1584 TAB 3264 m u

structure KeepW (base : Addr) (s u : State) : Prop where
  gpr : ∀ r, r ∉ clob → u.gpr r = s.gpr r
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  mem : Frame base s.mem u.mem

theorem KeepW.refl (base : Addr) (s : State) : KeepW base s s :=
  ⟨fun _ _ => rfl, rfl, rfl, Outside2.refl _ _ _ _ _ _⟩

theorem KeepW.of_keep {base : Addr} {s u : State} (h : Keep base s u) : KeepW base s u :=
  ⟨h.gpr, h.rd, h.wr, h.mem.left _ _⟩

theorem KeepW.trans {base : Addr} {s u v : State} (h : KeepW base s u) (g : KeepW base u v) :
    KeepW base s v :=
  ⟨fun r hr => (g.gpr r hr).trans (h.gpr r hr), g.rd.trans h.rd, g.wr.trans h.wr, h.mem.trans g.mem⟩

theorem KeepW.scr {base : Addr} {s u : State} (h : KeepW base s u) (hs : Scr s base) : Scr u base :=
  ⟨(h.gpr _ (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem Frame.wide {base : Addr} {m u : Mem} (h : Frame base m u) : Outside base 64 7296 m u :=
  h.outside (by decide) (by decide) (by decide) (by decide)

theorem Bits.keepW {base : Addr} {o k : Nat} (ho : 2048 ≤ o) (hb : o + 460 ≤ TAB)
    {s u : State} (h : Bits base o k s) (f : KeepW base s u) : Bits base o k u := by
  intro t ht
  have hn : o - 1 + t < 2 ^ 64 := by simp only [TAB] at hb; omega
  rw [f.mem _ (Or.inr (by rw [VG.Proof.X448.X86_64.ofs_off' base hn]; omega))
    (Or.inl (by rw [VG.Proof.X448.X86_64.ofs_off' base hn]; omega))]
  exact h t ht

def pointAt (m : Mem) (base : Addr) (o : Nat) : Spec.Ed448.Point :=
  ⟨F m base o, F m base (o + 64), F m base (o + 128)⟩

def tablePoint (m : Mem) (base : Addr) (i : Nat) : Spec.Ed448.Point :=
  pointAt m base (tabOffset i 0)

theorem pointAt_outside {base : Addr} {a n o : Nat} {m u : Mem} (h : Outside base a n m u)
    (ho : o + 184 ≤ 8192) (hs : o + 184 ≤ a ∨ a + n ≤ o) : pointAt u base o = pointAt m base o := by
  unfold pointAt F
  rw [h.fe (by omega) (by omega), h.fe (by omega) (by omega), h.fe (by omega) (by omega)]

theorem tablePoint_keep {base : Addr} {s u : State} (h : Keep base s u) (i : Nat) (hi : i < 17) :
    tablePoint u.mem base i = tablePoint s.mem base i := by
  apply pointAt_outside h.mem <;> simp only [tabOffset, TAB] <;> omega

/-- Copy a stored coordinate into a field slot. -/
theorem load_ok {s : State} {base : Addr} (hs : Scr s base) (i : Index) {a : Nat} (ha : a + 56 ≤ 8192) :
    WP isa (.block (copyOut (slot i.val) a)) s fun u => Keep base s u ∧
      E u.mem base = Function.update (E s.mem base) i (F s.mem base a) := by
  have hi := VG.Proof.X448.X86_64.slot_lt i
  have gi := VG.Proof.X448.X86_64.slot_ge i
  simp only [Impl.X448.X86_64.ACC] at hi
  refine WP.mono (copyOut_ok hs (by omega) ha) fun u ⟨fu, ou, gu, ru, wu⟩ => ⟨?_, ?_⟩
  · refine ⟨fun r hr => gu r (fun h => hr (?_)), ru, wu, ou.mono (by omega) (by omega)⟩
    exact (show ∀ r ∈ W, r ∈ clob from by decide) r h
  · funext j
    by_cases hj : j = i
    · subst j; rw [Function.update_self]; show F u.mem base (slot i.val) = _
      unfold F; rw [fu]
    · rw [Function.update_of_ne hj]
      exact E_outside ou j (VG.Proof.X448.X86_64.slot_sep hj)

/-- Store one field slot in the table, preserving all working slots. -/
theorem store_coord_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (ho : TAB ≤ o) (he : o + 56 ≤ TAB + 3264) (j : Index) :
    WP isa (.block (copyOut o (slot j.val))) s fun u =>
      KeepW base s u ∧ Outside base o 56 s.mem u.mem ∧ E u.mem base = E s.mem base ∧
      F u.mem base o = E s.mem base j := by
  have hj := VG.Proof.X448.X86_64.slot_lt j
  simp only [Impl.X448.X86_64.ACC] at hj
  refine WP.mono (copyOut_ok hs (by simp only [TAB] at *; omega) (by omega))
    fun u ⟨fu, ou, gu, ru, wu⟩ => ⟨?_, ou, ?_, ?_⟩
  · refine ⟨fun r hr => gu r (fun h => hr (?_)), ru, wu, (ou.mono ho he).right _ _⟩
    exact (show ∀ r ∈ W, r ∈ clob from by decide) r h
  · funext i
    apply E_outside ou i
    have hi := VG.Proof.X448.X86_64.slot_lt i
    simp only [Impl.X448.X86_64.ACC] at hi
    left; simp only [TAB] at ho; omega
  · unfold F E; rw [fu]

/-- Store the accumulator at a public, fixed table index. -/
theorem store_ok {s : State} {base : Addr} (hs : Scr s base) (i : Nat) (hi : i < 17) :
    WP isa (.block (store i)) s fun u => KeepW base s u ∧
      Outside base (tabOffset i 0) 184 s.mem u.mem ∧ E u.mem base = E s.mem base ∧
      tablePoint u.mem base i = Proof.Ed448.pt (E s.mem base) 0 1 2 := by
  rw [store, List.append_assoc, WP.block_append_iff]
  refine WP.mono (store_coord_ok hs (o := tabOffset i 0) (by simp only [tabOffset]; omega)
    (by simp only [tabOffset]; omega) 0) fun s1 ⟨k1, o1, e1, v1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (store_coord_ok (k1.scr hs) (o := tabOffset i 1) (by simp only [tabOffset]; omega)
    (by simp only [tabOffset]; omega) 1) fun s2 ⟨k2, o2, e2, v2⟩ => ?_
  refine WP.mono (store_coord_ok (k2.scr (k1.scr hs)) (o := tabOffset i 2) (by simp only [tabOffset]; omega)
    (by simp only [tabOffset]; omega) 2) fun u ⟨ku, ou, eu, vu⟩ => ?_
  refine ⟨(k1.trans k2).trans ku,
    ((o1.mono (by omega) (by omega)).trans (o2.mono (by simp only [tabOffset]; omega)
      (by simp only [tabOffset]; omega))).trans
      (ou.mono (by simp only [tabOffset]; omega) (by simp only [tabOffset]; omega)),
    eu.trans (e2.trans e1), ?_⟩
  have hx : F u.mem base (tabOffset i 0) = F s1.mem base (tabOffset i 0) := by
    unfold F
    rw [ou.fe (by simp only [tabOffset]; omega) (by simp only [tabOffset, TAB]; omega),
      o2.fe (by simp only [tabOffset]; omega) (by simp only [tabOffset, TAB]; omega)]
  have hy : F u.mem base (tabOffset i 1) = F s2.mem base (tabOffset i 1) := by
    unfold F
    rw [ou.fe (by simp only [tabOffset]; omega) (by simp only [tabOffset, TAB]; omega)]
  change (⟨F u.mem base (tabOffset i 0), F u.mem base (tabOffset i 1),
    F u.mem base (tabOffset i 2)⟩ : Spec.Ed448.Point) = _
  rw [hx, hy, v1, v2, vu, e2, e1]; rfl

end VG.Proof.Ed448.X86_64.Window
