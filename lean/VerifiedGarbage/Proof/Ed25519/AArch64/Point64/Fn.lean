import VerifiedGarbage.Impl.Ed25519.AArch64.Point64
import VerifiedGarbage.Proof.Ed25519.AArch64.Points
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved

/-!
# Ed25519's point functions on AArch64: their bodies

Untrusted: everything here is checked by Lean. A field program writes only its
results' slots (`fieldCode_frame`, from each operation's `Op`); a function
running one (`fn_ok`) also restores the callee-saved registers it keeps in
lanes. The doubling's program computes RFC 8032's doubling
(`doubleRfcOps_eval`), the affine addition's `pointAdd` of an entry with
`Z = 1` (`addAffineOps_eval`).
-/

namespace VG.Proof.Ed25519.AArch64.Point64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Impl.Ed25519.AArch64.Point64 VG.Proof.Ed25519.AArch64

/-! ## Frames -/

theorem fieldOp_frame {s : State} {base : Addr} (hs : Scr s base) (op : FieldOp) :
    WP isa (.block op.code) s fun t => Keep base s t ∧ env t.mem base = evalOp op (env s.mem base) ∧
      Outside base (offset (fieldDest op)) 32 s.mem t.mem := by
  cases op with
  | copy o a =>
    exact WP.mono (copyField_op hs o a) fun t ⟨h, e⟩ =>
      ⟨op_keep h, by rw [env_update o h.mem, e]; rfl, h.mem⟩
  | const o v =>
    exact WP.mono (constField_op hs o v) fun t ⟨h, e⟩ =>
      ⟨op_keep h, by rw [env_update o h.mem, e]; rfl, h.mem⟩
  | mul o a b =>
    exact WP.mono (mul_ok hs (slot_range o) (slot_range a) (slot_range b)) fun t ⟨h, e⟩ =>
      ⟨op_keep h, by rw [env_update o h.mem, e]; rfl, h.mem⟩
  | sqr o a =>
    exact WP.mono (sqr_ok hs (slot_range o) (slot_range a)) fun t ⟨h, e⟩ =>
      ⟨op_keep h, by rw [env_update o h.mem, e]; rfl, h.mem⟩
  | add o a b =>
    exact WP.mono (add_ok hs (slot_range o) (slot_range a) (slot_range b)) fun t ⟨h, e⟩ =>
      ⟨op_keep h, by rw [env_update o h.mem, e]; rfl, h.mem⟩
  | sub o a b =>
    exact WP.mono (sub_ok hs (slot_range o) (slot_range a) (slot_range b)) fun t ⟨h, e⟩ =>
      ⟨op_keep h, by rw [env_update o h.mem, e]; rfl, h.mem⟩

/-- The address `x` is in no result's slot of `ops`. -/
def Unwritten (ops : List FieldOp) (base x : Addr) : Prop :=
  ∀ op ∈ ops, ofs base x < offset (fieldDest op) ∨ offset (fieldDest op) + 32 ≤ ofs base x

theorem fieldCode_frame (ops : List FieldOp) {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block (fieldCode ops)) s fun t => Keep base s t ∧
      env t.mem base = evalOps ops (env s.mem base) ∧ ∀ x, Unwritten ops base x → t.mem x = s.mem x := by
  induction ops generalizing s with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, rfl, fun _ _ => rfl⟩
  | cons op ops ih =>
    rw [fieldCode, List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (fieldOp_frame hs op) fun t ⟨ht, et, mt⟩ => ?_
    refine WP.mono (ih (ht.scr hs)) fun u ⟨hu, eu, mu⟩ => ?_
    exact ⟨ht.trans hu, by rw [eu, et]; rfl, fun x hx =>
      (mu x fun o ho => hx o (List.mem_cons_of_mem _ ho)).trans (mt x (hx op List.mem_cons_self))⟩

/-! ## The functions -/

theorem kept_lanes : ∀ k ∈ kept, k.2.2 < 2 := by decide
theorem kept_nodup_lanes : (kept.map fun k => (k.2.1, k.2.2)).Nodup := by decide
theorem kept_nodup : (kept.map Prod.fst).Nodup := by decide

/-- A function running `ops`, which writes no vector register: the slots as after `ops`, which
writes only its results' slots, and every register outside `clob`, or kept in a lane,
restored. -/
theorem fn_ok {s : State} {base : Addr} (hs : Scr s base) (ops : List FieldOp)
    (hv : ∀ r, ∀ i ∈ fieldCode ops, vdstOf i ≠ some r) :
    WP isa (fn ops) s fun u =>
      (∀ r, (r ∉ clob ∨ r ∈ kept.map Prod.fst) → u.gpr r = s.gpr r) ∧ u.rd = s.rd ∧
        u.wr = s.wr ∧ u.sp = s.sp ∧ (∀ x, Unwritten ops base x → u.mem x = s.mem x) ∧
        env u.mem base = evalOps ops (env s.mem base) := by
  unfold fn
  rw [WP.seq_iff]
  refine WP.mono (insOf_ok kept s kept_lanes kept_nodup_lanes)
    fun s₁ ⟨hg, hm, hr, hw, hsp, hls, _⟩ => ?_
  have hs₁ : Scr s₁ base := ⟨by rw [hg]; exact hs.x0, by rw [hw]; exact hs.wr, hs.nowrap⟩
  rw [WP.seq_iff]
  obtain ⟨tb, t, he, hk, hev, hmt⟩ := fieldCode_frame ops hs₁
  refine ⟨tb, t, he, ?_⟩
  have tl : ∀ k ∈ kept, laneOf t k.2.1 k.2.2 = s.gpr k.1 := fun k hk' => by
    rw [laneOf, Exec.vec (c := .block (fieldCode ops)) (hv _) he, ← laneOf, hls k hk']
  refine WP.mono (umovOf_ok kept t kept_lanes kept_nodup)
    fun u ⟨um, ur, uw, usp, uls, uoth⟩ => ?_
  refine ⟨fun r hr' => ?_, by rw [ur, hk.rd, hr], by rw [uw, hk.wr, hw], by rw [usp, hk.sp, hsp],
    fun x hx => by rw [um, hmt x hx, hm], by rw [um, hev, hm]⟩
  by_cases hm' : r ∈ kept.map Prod.fst
  · obtain ⟨k, hk', rfl⟩ := List.mem_map.mp hm'
    rw [uls k hk', tl k hk']
  · rw [uoth r hm', hk.gpr r (hr'.resolve_right hm'), hg]

/-! ## The programs' values -/

/-- What `doubleRfcOps` leaves in slots 0–3. -/
def dblResult (e : Env) : Spec.Ed25519.Point :=
  let a := e 0 * e 0
  let b := e 1 * e 1
  let c := e 2 * e 2 + e 2 * e 2
  let h := a + b
  let ee := h - (e 0 + e 1) * (e 0 + e 1)
  let g := a - b
  let f := c + g
  ⟨ee * f, g * h, f * g, ee * h⟩

theorem doubleRfcOps_formula (e : Env) : point (evalOps doubleRfcOps e) 0 1 2 3 = dblResult e := rfl

/-- `doubleRfcOps` computes RFC 8032's doubling. -/
theorem doubleRfcOps_eval (e : Env) :
    point (evalOps doubleRfcOps e) 0 1 2 3 = Spec.Ed25519.Point64.pointDouble (point e 0 1 2 3) := by
  rw [doubleRfcOps_formula]
  simp only [dblResult, Spec.Ed25519.Point64.pointDouble, point]
  congr 1 <;> grind

/-- What `addAffineOps` computes, from the point's coordinates and the cached entry's. -/
def mixedResult (x y z t q₀ q₁ q₂ : Spec.X25519.Fe) : Spec.Ed25519.Point :=
  let a := (y - x) * q₀
  let b := (y + x) * q₁
  let c := t * q₂
  let dd := z + z
  ⟨(b - a) * (dd - c), (dd + c) * (b + a), (dd - c) * (dd + c), (b - a) * (b + a)⟩

theorem mixedResult_eq (p q : Spec.Ed25519.Point) (hz : q.Z = 1) :
    mixedResult p.X p.Y p.Z p.T (q.Y - q.X) (q.Y + q.X) (q.T * 2 * Spec.Ed25519.d) =
      Spec.Ed25519.pointAdd p q := by
  simp only [mixedResult, Spec.Ed25519.pointAdd, hz]
  congr 1 <;> grind

theorem addAffineOps_formula (e : Env) :
    point (evalOps addAffineOps e) 0 1 2 3 = mixedResult (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) (e 6) :=
  rfl

/-- `addAffineOps` computes `pointAdd` of the point in slots 0–3 and `q`, with `Z = 1`, whose
cached form's first three coordinates are in slots 4–6. -/
theorem addAffineOps_eval (e : Env) (q : Spec.Ed25519.Point) (hz : q.Z = 1) (h4 : e 4 = q.Y - q.X)
    (h5 : e 5 = q.Y + q.X) (h6 : e 6 = q.T * 2 * Spec.Ed25519.d) :
    point (evalOps addAffineOps e) 0 1 2 3 = Spec.Ed25519.pointAdd (point e 0 1 2 3) q := by
  rw [addAffineOps_formula, h4, h5, h6]
  exact mixedResult_eq (point e 0 1 2 3) q hz

end VG.Proof.Ed25519.AArch64.Point64
