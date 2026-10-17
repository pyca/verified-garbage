module

public import VerifiedGarbage.Proof.Rsa.Arm.KcOps
public import VerifiedGarbage.Proof.Rsa.Arm.CvDivN
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The checks of an RSA key on ARMv7: the divisions

`divSet_ok`: `divSet a d` sets up the division of `[a]` by `[d]`, after which
`Div.code` leaves the quotient in `aVQ` and the remainder in `aVR` (`StgD`);
`ctxDiv_ok`: `r7` and `r9` again, from `w` in the division's header.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyCheck
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.KeyCheck
open VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm

/-- The geometry of the divisions. -/
abbrev gDiv (g : Geo) : VG.Proof.Rsa.Arm.Div.Geometry := divGeom g.B g.Z g.w aVQ aVR aVD aVT

theorem clobbers_body : ∀ x ∈ (.r6 :: VG.Proof.Rsa.Arm.Div.clobbers), x ∈ bodyRegs := by decide

/-- The division from its set-up state. -/
theorem Stg.div_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g s0 A live c s) (hh : DivHdr s.mem g.B g.w aVQ aVR aVD aVT)
    (hfree : ∀ j ∈ live, j ∉ [aVQ, aVR, aVT]) :
    WP isa VG.Impl.Rsa.Arm.Div.code s fun t => ∃ Xq Xr,
      (0 < num s.mem g.B g.w aVD → Xr = num s.mem g.B g.w aVQ % num s.mem g.B g.w aVD ∧
        Xq = num s.mem g.B g.w aVQ / num s.mem g.B g.w aVD) ∧
      StgD g s0 (upd (upd A aVQ Xq) aVR Xr) (aVR :: aVQ :: live) c t := by
  refine WP.mono (Keys.div_ok h.ws (q := aVQ) (r := aVR) (d := aVD) (t := aVT) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hh h.vdTop)
    fun t ⟨k, r, v⟩ => ⟨num t.mem g.B g.w aVQ, num t.mem g.B g.w aVR, fun pos => ⟨(v pos).1, (v pos).2⟩, ?_⟩
  have hw := h.ws
  refine ⟨⟨hw.nowrap, by rw [r.wr]; exact hw.writable, hw.fits, hw.wpos, hw.wle,
      by rw [r.gpr _ (by decide)]; exact hw.r8⟩,
    h.keep.trans (k.mono (by decide) (by simp)), h.rest.trans (r.mono clobbers_body), ?_, ?_, ?_,
    h.vd_keep k (by decide) (by simp), h.mask_keep k (by simp)⟩
  · rw [slot_eq_of_keep k (by decide) (by simp), h.cnt]
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
    WP isa (seqs (divSet a d)) s fun u => VG.Proof.Rsa.Arm.Div.Context (gDiv g) u ∧
      WP isa VG.Impl.Rsa.Arm.Div.code u fun t => ∃ Xq Xr, (0 < A d → Xr = A a % A d ∧ Xq = A a / A d) ∧
        StgD g s0 (upd (upd A aVQ Xq) aVR Xr) (aVR :: aVQ :: live) c t := by
  have aQ : a ≠ aVQ := fun e => hfree a ha (by simp [e])
  have aD : a ≠ aVD := fun e => hfree a ha (by simp [e])
  have dQ : d ≠ aVQ := fun e => hfree d hd (by simp [e])
  have dD : d ≠ aVD := fun e => hfree d hd (by simp [e])
  unfold divSet
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (h.copy_ok (o := aVQ) (a := a) (by decide) ha (Ne.symm aQ)) fun t1 h1 => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (h1.copy_ok (o := aVD) (a := d) (by decide) (List.mem_cons_of_mem _ hd) (Ne.symm dD))
    fun t2 h2 => ?_
  show WP isa (.block (VG.Impl.Rsa.Arm.CrtValues.divHdr aVQ aVR aVD aVT)) t2 _
  rw [← List.append_nil (VG.Impl.Rsa.Arm.CrtValues.divHdr _ _ _ _)]
  refine VG.Proof.Rsa.Arm.CrtValues.divHdr_ok h2.ws (by decide) (by decide) (by decide) (by decide) h2.cnt
    fun u hu ku du ru => WP.block_nil ?_
  have h3 := h2.next hu ku (by simp) (by decide) ru opRegs_body (h2.arrs_keep ku (by simp) (by decide))
    h2.live_lt (h2.vd_keep ku (by simp) (by decide)) (h2.mask_keep ku (by decide))
  refine ⟨divGeom_ctx hu (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) du, ?_⟩
  have fq : num u.mem g.B g.w aVQ = A a := by
    rw [h3.arrs.get (by simp), upd_ne (j := aVD) _ _ (by decide), upd_self]
  have fd : num u.mem g.B g.w aVD = A d := by
    rw [h3.arrs.get (by simp), upd_self, upd_ne (j := aVQ) _ _ dQ]
  have h3' : Stg g s0 A live c u := (h3.sub (live' := live) fun j hj =>
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj)).congr' fun j hj => by
    have hn := hfree j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    rw [upd_ne _ _ hn.2.2.1, upd_ne _ _ hn.1]
  refine WP.mono (h3'.div_ok du fun j hj => by
    have hn := hfree j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn ⊢
    exact ⟨hn.1, hn.2.1, hn.2.2.2⟩) fun t ⟨Xq, Xr, hv, ht⟩ => ⟨Xq, Xr, fun pos => ?_, ht⟩
  rw [fq, fd] at hv
  exact hv pos

end VG.Proof.Rsa.Arm.KeyCheck
