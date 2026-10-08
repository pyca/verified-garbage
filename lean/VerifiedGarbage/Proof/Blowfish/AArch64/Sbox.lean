import VerifiedGarbage.Proof.Blowfish.AArch64.Planes

/-!
# One S-box

`lookup_run`: `lookup j` leaves in `outReg b` byte plane `b` of S-box `j` at
the indices in `idxReg j`. `combine_run`: `combine j` accumulates the words
into `fReg`.
-/

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Blowfish.AArch64
open VG.AArch64.Tbl (VOnly)

/-- 64 and 128 in every byte of `c64` and `c128`. -/
def Consts (s : State) : Prop :=
  (∀ e < 16, vbyte (s.v c64) e = 64) ∧ ∀ e < 16, vbyte (s.v c128) e = 128

/-- The registers `lookup` writes. -/
def lookupRegs : List VReg :=
  [.v24, .v25, .v26, .v28, .v29, .v30, .v31, .v20, .v21, .v22, .v23]

theorem VOnly.mono {ds ds' : List VReg} {a b : State} (h : VOnly ds a b) (hs : ∀ r ∈ ds, r ∈ ds') :
    VOnly ds' a b := ⟨h.1, fun r hr => h.2 r fun h' => hr (hs r h')⟩

theorem q_notin : ∀ q < 4, 0 < q → ∀ b < 4, qReg q ∉ [VReg.v28, .v29, .v30, .v31, outReg b] := by
  decide
theorem idx_notin : ∀ j < 4, ∀ b < 4, idxReg j ∉ [VReg.v28, .v29, .v30, .v31, outReg b] := by decide
theorem out_notin : ∀ b < 4, ∀ b' < 4, b ≠ b' → outReg b ∉ [VReg.v28, .v29, .v30, .v31, outReg b'] := by
  decide
theorem idx_ne_q123 : ∀ j < 4, idxReg j ≠ .v24 ∧ idxReg j ≠ .v25 ∧ idxReg j ≠ .v26 := by decide
theorem plane_sub : ∀ b < 4, ∀ r ∈ [VReg.v28, .v29, .v30, .v31, outReg b], r ∈ lookupRegs := by decide

theorem lookup_run {s : State} {sch : Reg} (hR : Readable s sch) (hc : Consts s) {j : Nat}
    (hj : j < 4) :
    ∃ s', runBlock isa (lookup sch j) s = some s' ∧
      (∀ b < 4, ∀ e < 16, vbyte (s'.v (outReg b)) e =
        s.mem (s.gpr sch + BitVec.ofNat 64 (planeOff j b + (vbyte (s.v (idxReg j)) e).toNat))) ∧
      VOnly lookupRegs s s' := by
  have hidx := idx_ne_q123 j hj
  let s₁ := s.setV (qReg 1) (s.v (idxReg j) ^^^ s.v c64)
  let s₂ := s₁.setV (qReg 2) (s₁.v (idxReg j) ^^^ s₁.v c128)
  let s₃ := s₂.setV (qReg 3) (s₂.v (qReg 1) ^^^ s₂.v c128)
  have X : s₃.v (idxReg j) = s.v (idxReg j) := by
    simp only [s₃, s₂, s₁, qReg, List.getD_cons_zero, List.getD_cons_succ, v_setV_of_ne _ _ hidx.1,
      v_setV_of_ne _ _ hidx.2.1, v_setV_of_ne _ _ hidx.2.2]
  have q1 : s₃.v (qReg 1) = s.v (idxReg j) ^^^ s.v c64 := by
    simp only [s₃, s₂, s₁, qReg, List.getD_cons_zero, List.getD_cons_succ, v_setV, reduceCtorEq,
      ite_true, ite_false]
  have q2 : s₃.v (qReg 2) = s.v (idxReg j) ^^^ s.v c128 := by
    simp only [s₃, s₂, s₁, qReg, List.getD_cons_zero, List.getD_cons_succ, v_setV, reduceCtorEq,
      ite_true, ite_false, c128, c64, hidx.1]
  have q3 : s₃.v (qReg 3) = s.v (idxReg j) ^^^ s.v c64 ^^^ s.v c128 := by
    simp only [s₃, s₂, s₁, qReg, List.getD_cons_zero, List.getD_cons_succ, v_setV, reduceCtorEq,
      ite_true, ite_false, c128, c64, hidx.1]
  have hq : ∀ q < 4, 0 < q → ∀ e < 16,
      vbyte (s₃.v (qReg q)) e = vbyte (s₃.v (idxReg j)) e ^^^ BitVec.ofNat 8 (64 * q) := by
    intro q hq0 hq1 e he
    rw [X]
    rcases (by omega : q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl
    · rw [q1, vbyte_xor, hc.1 e he]; rfl
    · rw [q2, vbyte_xor, hc.2 e he]; rfl
    · rw [q3, vbyte_xor, vbyte_xor, hc.1 e he, hc.2 e he, BitVec.xor_assoc]; rfl
  have o₃ : VOnly lookupRegs s s₃ :=
    (((VOnly.setV s (by simp [lookupRegs, qReg]) _).trans (VOnly.setV _ (by simp [lookupRegs, qReg]) _)).trans
      (VOnly.setV _ (by simp [lookupRegs, qReg]) _))
  have hR₃ : ∀ {t : State}, VOnly lookupRegs s t → Readable t sch := by
    intro t ht off hoff
    rw [ht.rd, ht.wr, ht.gpr]; exact hR off hoff
  -- each plane keeps what the others read and wrote
  have step : ∀ {t : State} (b : Nat), b < 4 → VOnly lookupRegs s t →
      (∀ q < 4, 0 < q → ∀ e < 16,
        vbyte (t.v (qReg q)) e = vbyte (t.v (idxReg j)) e ^^^ BitVec.ofNat 8 (64 * q)) →
      ∃ t', runBlock isa (lookupPlane sch j b) t = some t' ∧
        (∀ e < 16, vbyte (t'.v (outReg b)) e =
          s.mem (s.gpr sch + BitVec.ofNat 64 (planeOff j b + (vbyte (t.v (idxReg j)) e).toNat))) ∧
        VOnly [.v28, .v29, .v30, .v31, outReg b] t t' := by
    intro t b hb ht hqt
    obtain ⟨t', r, v, o⟩ := lookupPlane_run (hR₃ ht) hj hb hqt
    refine ⟨t', r, fun e he => ?_, o⟩
    rw [v e he, ht.mem, ht.gpr]
  have ob := plane_sub
  have hqk : ∀ {t t' : State} (b : Nat), b < 4 → VOnly [.v28, .v29, .v30, .v31, outReg b] t t' →
      (∀ q < 4, 0 < q → ∀ e < 16,
        vbyte (t.v (qReg q)) e = vbyte (t.v (idxReg j)) e ^^^ BitVec.ofNat 8 (64 * q)) →
      (∀ q < 4, 0 < q → ∀ e < 16,
        vbyte (t'.v (qReg q)) e = vbyte (t'.v (idxReg j)) e ^^^ BitVec.ofNat 8 (64 * q)) := by
    intro t t' b hb o h q hq0 hq1 e he
    rw [o.2 _ (q_notin q hq0 hq1 b hb), o.2 _ (idx_notin j hj b hb)]; exact h q hq0 hq1 e he
  have ni := idx_notin j hj
  obtain ⟨t₀, r₀, v₀, o₀⟩ := step 0 (by decide) o₃ hq
  have p₀ := o₃.trans (VOnly.mono o₀ (ob 0 (by decide)))
  obtain ⟨t₁, r₁, v₁, o₁⟩ := step 1 (by decide) p₀ (hqk 0 (by decide) o₀ hq)
  have p₁ := p₀.trans (VOnly.mono o₁ (ob 1 (by decide)))
  obtain ⟨t₂, r₂, v₂, o₂⟩ := step 2 (by decide) p₁ (hqk 1 (by decide) o₁ (hqk 0 (by decide) o₀ hq))
  have p₂ := p₁.trans (VOnly.mono o₂ (ob 2 (by decide)))
  obtain ⟨t₃, r₃, v₃, o₃'⟩ := step 3 (by decide) p₂
    (hqk 2 (by decide) o₂ (hqk 1 (by decide) o₁ (hqk 0 (by decide) o₀ hq)))
  have p₃ := p₂.trans (VOnly.mono o₃' (ob 3 (by decide)))
  refine ⟨t₃, ?_, ?_, p₃⟩
  · have e₁ : exec (veor (qReg 1) (idxReg j) c64) s = some s₁ := rfl
    have e₂ : exec (veor (qReg 2) (idxReg j) c128) s₁ = some s₂ := rfl
    have e₃ : exec (veor (qReg 3) (qReg 1) c128) s₂ = some s₃ := rfl
    have l : lookup sch j = [veor (qReg 1) (idxReg j) c64, veor (qReg 2) (idxReg j) c128,
        veor (qReg 3) (qReg 1) c128] ++ (lookupPlane sch j 0 ++ (lookupPlane sch j 1 ++
        (lookupPlane sch j 2 ++ (lookupPlane sch j 3 ++ [])))) := rfl
    rw [l, List.cons_append, List.cons_append, List.cons_append, List.nil_append, runBlock_cons, e₁,
      runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃, runStep_some]
    exact VG.AArch64.Tbl.runBlock_cat_some r₀ (VG.AArch64.Tbl.runBlock_cat_some r₁
      (VG.AArch64.Tbl.runBlock_cat_some r₂ (VG.AArch64.Tbl.runBlock_cat_some r₃ runBlock_nil)))
  · -- the index register is never written
    have i₀ : t₀.v (idxReg j) = s.v (idxReg j) := (o₀.2 _ (ni 0 (by decide))).trans X
    have i₁ : t₁.v (idxReg j) = s.v (idxReg j) := (o₁.2 _ (ni 1 (by decide))).trans i₀
    have i₂ : t₂.v (idxReg j) = s.v (idxReg j) := (o₂.2 _ (ni 2 (by decide))).trans i₁
    intro b hb e he
    have nob := out_notin
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl
    · rw [o₃'.2 _ (nob 0 (by decide) 3 (by decide) (by decide)), o₂.2 _ (nob 0 (by decide) 2 (by decide) (by decide)),
        o₁.2 _ (nob 0 (by decide) 1 (by decide) (by decide)), v₀ e he, X]
    · rw [o₃'.2 _ (nob 1 (by decide) 3 (by decide) (by decide)), o₂.2 _ (nob 1 (by decide) 2 (by decide) (by decide)),
        v₁ e he, i₀]
    · rw [o₃'.2 _ (nob 2 (by decide) 3 (by decide) (by decide)), v₂ e he, i₁]
    · rw [v₃ e he, i₂]

end VG.Proof.Blowfish.AArch64
