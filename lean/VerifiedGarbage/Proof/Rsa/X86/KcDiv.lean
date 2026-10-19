module

public import VerifiedGarbage.Proof.Rsa.X86.KcOps

/-! # Division stages for i686 key validation

The fixed-offset division preserves the workspace base, tracked arrays,
and accumulated acceptance mask.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.KeyCheck
open VG.Proof.Rsa.X86.Keys

/-- The division from its set-up state. -/
theorem Stg.div_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s)
    (hfree : ∀ j ∈ live, j ∉ [aVQ, aVR, aVT]) :
    WP isa (division g.w) s fun t => ∃ Xq Xr,
      (0 < num s.mem g.B g.w aVD → Xr = num s.mem g.B g.w aVQ % num s.mem g.B g.w aVD ∧
        Xq = num s.mem g.B g.w aVQ / num s.mem g.B g.w aVD) ∧
      Stg g s0 (upd (upd A aVQ Xq) aVR Xr) (aVR :: aVQ :: live) c t := by
  let ids : Fin 4 → Nat := fun i => 12 + i.val
  refine WP.mono (Keys.div_ok (ids := ids) h.ws (by decide) (by decide) h.vdTop)
    fun t ⟨ht, k, r, v⟩ =>
      ⟨num t.mem g.B g.w aVQ, num t.mem g.B g.w aVR, fun pos => ⟨(v pos).2, (v pos).1⟩, ?_⟩
  change Keep g.B g.w [aVQ, aVR, aVT] [] s.mem t.mem at k
  have hw := h.ws
  refine h.next ht k (by decide) (by simp) r allRegs_body ?_ ?_
    (h.vd_keep k (by decide) (by simp)) (h.mask_keep k (by simp))
  · intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · rw [upd_self]
    rcases List.mem_cons.mp hj with rfl | hj
    · rw [upd_ne _ _ (by decide), upd_self]
    have hn := hfree j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    rw [upd_ne _ _ hn.2.1, upd_ne _ _ hn.1, k.num (by simp; omega) (by simp) (hw.fit64 (h.live_lt j hj)),
      h.arrs.get hj]
  · intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · decide
    rcases List.mem_cons.mp hj with rfl | hj
    · decide
    exact h.live_lt j hj

/-- `divSet a d`, then the division: `[a] / [d]` in `aVQ`, `[a] mod [d]` in `aVR`. -/
theorem Stg.divSet_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) {a d : Nat} (ha : a ∈ live) (hd : d ∈ live)
    (hfree : ∀ j ∈ live, j ∉ [aVQ, aVR, aVD, aVT]) :
    WP isa (seqs (divSet g.w a d)) s fun u => WP isa (division g.w) u fun t => ∃ Xq Xr, (0 < A d → Xr = A a % A d ∧ Xq = A a / A d) ∧
        Stg g s0 (upd (upd A aVQ Xq) aVR Xr) (aVR :: aVQ :: live) c t := by
  have aQ : a ≠ aVQ := fun e => hfree a ha (by simp [e])
  have aD : a ≠ aVD := fun e => hfree a ha (by simp [e])
  have dQ : d ≠ aVQ := fun e => hfree d hd (by simp [e])
  have dD : d ≠ aVD := fun e => hfree d hd (by simp [e])
  unfold divSet
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (h.copy_ok (o := aVQ) (a := a) (by decide) ha) fun t1 h1 => ?_
  refine WP.mono (h1.copy_ok (o := aVD) (a := d) (by decide) (List.mem_cons_of_mem _ hd))
    fun t2 h2 => ?_
  have h3 := h2
  have fq : num t2.mem g.B g.w aVQ = A a := by
    rw [h3.arrs.get (by simp), upd_ne (j := aVD) _ _ (by decide), upd_self]
  have fd : num t2.mem g.B g.w aVD = A d := by
    rw [h3.arrs.get (by simp), upd_self, upd_ne (j := aVQ) _ _ dQ]
  have h3' : Stg g s0 A live c t2 := (h3.sub (live' := live) fun j hj =>
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj)).congr' fun j hj => by
    have hn := hfree j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    rw [upd_ne _ _ hn.2.2.1, upd_ne _ _ hn.1]
  refine WP.mono (h3'.div_ok fun j hj => by
    have hn := hfree j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn ⊢
    exact ⟨hn.1, hn.2.1, hn.2.2.2⟩) fun t ⟨Xq, Xr, hv, ht⟩ => ⟨Xq, Xr, fun pos => ?_, ht⟩
  rw [fq, fd] at hv
  exact hv pos

end VG.Proof.Rsa.X86.KeyCheck
