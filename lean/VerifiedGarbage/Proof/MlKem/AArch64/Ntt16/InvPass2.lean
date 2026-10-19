module

public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.InvRows

/-!
# ML-KEM's 16-bit inverse NTT on AArch64: pass 2

Pass 2 of the inverse (`invPass2Body`, chunks `c < 4`): the rows of chunk `c`
from `scratch`, layers 5, 6 (`gsRows`), a reduction, 7, and each lane times
`3303 = 128⁻¹ mod q`, reduced to `[0, q)` and widened into `f` (`scale_lane`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem VG.Spec.MlKem
open Impl.MlKem.AArch64.Ntt16

/-- A lane times 3303, reduced to `[0, q)`. -/
theorem scale_lane {a : BitVec 16} {X : Zq} {B : Nat} (ha : LRep a X B) (hB : B ≤ 32768) :
    ∃ T, sqdmulhHLane true a (BitVec.ofNat 16 (tw 3303)) = some T ∧
      ((a * BitVec.ofNat 16 3303 - T * BitVec.ofNat 16 3329) +
        ((a * BitVec.ofNat 16 3303 - T * BitVec.ofNat 16 3329).sshiftRight 15 &&&
          BitVec.ofNat 16 3329)).toNat = (X * 3303).val := by
  obtain ⟨a1, a2, a3⟩ := ha
  obtain ⟨T, hT, b1, b2, b3⟩ := mm_ok a (z := 3303) (by omega) (by decide)
  refine ⟨T, hT, ?_⟩
  have nn := nonneg_lane b1 b2
  generalize a * BitVec.ofNat 16 3303 - T * BitVec.ofNat 16 3329 = r at b1 b2 b3 nn ⊢
  generalize r + (r.sshiftRight 15 &&& BitVec.ofNat 16 3329) = w at nn ⊢
  have e1 : (X * 3303).val = X.val * 3303 % 3329 := by
    rw [val_mul]; rfl
  have hX := val_lt X
  rw [e1]
  have hw : (w.toNat : Int) = w.toInt := by
    have := w.isLt
    rw [BitVec.toInt_eq_toNat_cond] at nn ⊢; split <;> split at nn <;> omega
  generalize X.val = xv at *
  generalize a.toInt = ai at *
  generalize r.toInt = ri at *
  generalize w.toInt = wi at *
  generalize w.toNat = wn at *
  split at nn <;> omega

/-! ## The output -/

/-- The coefficients `i ∈ S` of the polynomial at `p` are `G i`, the others `old i`. -/
def CoeffsIn (m : Mem) (p : Addr) (S : Nat → Prop) [DecidablePred S] (G old : Nat → BitVec 32) :
    Prop :=
  ∀ i < 256, coeffAt m p i = if S i then G i else old i

theorem CoeffsIn.congr {m : Mem} {p : Addr} {S S' : Nat → Prop} [DecidablePred S] [DecidablePred S']
    {G old : Nat → BitVec 32} (h : CoeffsIn m p S G old) (hS : ∀ i < 256, (S' i ↔ S i)) :
    CoeffsIn m p S' G old := fun i hi => by
  rw [h i hi]
  by_cases c : S i
  · rw [ite_eq_left c, ite_eq_left ((hS i hi).2 c)]
  · rw [ite_eq_right c, ite_eq_right (fun h' => c ((hS i hi).1 h'))]

/-- Storing four coefficients `t, …, t + 3`. -/
theorem CoeffsIn.write16 {m : Mem} {p : Addr} {S S' : Nat → Prop} [DecidablePred S]
    [DecidablePred S'] {G old : Nat → BitVec 32} (h : CoeffsIn m p S G old) {t : Nat} (ht : t + 4 ≤ 256)
    {x : BitVec 128} (hx : ∀ e < 4, vword x e = G (t + e))
    (hS : ∀ i < 256, (S' i ↔ S i ∨ (t ≤ i ∧ i < t + 4))) :
    CoeffsIn (m.write (coeffAddr p t) 16 x) p S' G old := fun i hi => by
  rw [coeffAt_write16 _ _ ht _ hi, h i hi]
  by_cases c : t ≤ i ∧ i < t + 4
  · rw [ite_eq_left c, ite_eq_left ((hS i hi).2 (Or.inr c)), hx _ (by omega),
      show t + (i - t) = i by omega]
  · rw [ite_eq_right c]
    by_cases c' : S i
    · rw [ite_eq_left c', ite_eq_left ((hS i hi).2 (Or.inl c'))]
    · rw [ite_eq_right c', ite_eq_right (fun h' => ((hS i hi).1 h').elim c' c)]

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

/-- The lanes of `x` times 3303, reduced to `[0, q)`, in `v16`. -/
theorem scale_ok {x : VReg} (h16 : x ≠ .v16 := by decide)
    {X : Nat → Zq} {B : Nat} (hx : Rep (s.v x) X B) (hB : B ≤ 32768)
    (hz : Cst (s.v .v22) fun _ => 3303) (ht : Cst (s.v .v23) fun _ => tw 3303)
    (hq : Cst (s.v .v31) fun _ => 3329)
    (k : ∀ s', VChg [.v16, .v17, .v16, .v17, .v17, .v16] s s' →
      (∀ e < 8, (vhalf (s'.v .v16) e).toNat = (X e * 3303).val) → WP isa (.block rest) s' Q) :
    WP isa (.block ([.vop (.mulH .mul .v16 x .v22), .vop (.mulH .sqrdmulh .v17 x .v23),
      .vop (.mulH .mls .v16 .v17 .v31), .vop (.shift .sshr .h8 .v17 .v16 15),
      .vop (.logic .and .v17 .v17 .v31), .vop (.add .h8 .v16 .v16 .v17)] ++ rest)) s Q := by
  simp only [List.cons_append, List.nil_append]
  have L : ∀ e < 8, ∃ T, sqdmulhHLane true (vhalf (s.v x) e) (BitVec.ofNat 16 (tw 3303)) = some T ∧
      ((vhalf (s.v x) e * BitVec.ofNat 16 3303 - T * BitVec.ofNat 16 3329) +
        ((vhalf (s.v x) e * BitVec.ofNat 16 3303 - T * BitVec.ofNat 16 3329).sshiftRight 15 &&&
          BitVec.ofNat 16 3329)).toNat = (X e * 3303).val := fun e he => scale_lane (hx e he) hB
  refine wp_vop (eval_mulH fun _ _ => rfl) fun s₁ h₁ => ?_
  refine wp_vop (eval_mulH fun e he => by
    obtain ⟨T, hT, -⟩ := L e he
    simp only [VMulHOp.lane, h₁.get x h16, h₁.get .v23, ht e he, hT, Option.isSome_some])
    fun s₂ h₂ => ?_
  refine wp_vop (eval_mulH fun _ _ => rfl) fun s₃ h₃ => ?_
  refine wp_vop rfl fun s₄ h₄ => wp_vop rfl fun s₅ h₅ => wp_vop rfl fun s₆ h₆ => ?_
  refine k s₆ (((((h₁.chg.trans h₂.chg).trans h₃.chg).trans h₄.chg).trans h₅.chg).trans h₆.chg)
    fun e he => ?_
  obtain ⟨T, hT, l⟩ := L e he
  have r3 : vhalf (s₃.v .v16) e = vhalf (s.v x) e * BitVec.ofNat 16 3303 - T * BitVec.ofNat 16 3329 := by
    rw [h₃.v, vhalf_ofVHalves _ he]
    simp only [VMulHOp.lane, h₂.get .v16, h₁.v, vhalf_ofVHalves _ he, h₂.v, h₁.get x h16,
      h₁.get .v23, ht e he, hT, Option.getD_some, hz e he, h₂.get .v31, h₁.get .v31, hq e he]
  generalize vhalf (s.v x) e * BitVec.ofNat 16 3303 - T * BitVec.ofNat 16 3329 = r at r3 l
  rw [← l, h₆.v, vhalf_map2 _ _ _ he, h₅.get .v16, h₅.v, vhalf_and, h₄.v, vhalf_map2 _ _ _ he,
    h₄.get .v31, h₄.get .v16, h₃.get .v31, h₂.get .v31, h₁.get .v31, hq e he, r3]
  rfl

end

section
variable {rest : List Instr} {Q : State → Prop}

/-- The rows of chunk `c` (lanes `X (32r + 8c + e)`) times 3303, reduced to `[0, q)` and
stored into `f` as `u32`s. -/
theorem scale_rows {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c < 4) {s : State} (st : St s₀ s)
    (hx3 : s.gpr .x3 = coeffAddr (fP s₀) (8 * c)) {X : Nat → Zq}
    (hrows : ∀ r < 8, Rep (s.v (row r)) (fun e => X (32 * r + 8 * c + e)) (2 * 3329))
    (hz : Cst (s.v .v22) fun _ => 3303) (ht : Cst (s.v .v23) fun _ => tw 3303)
    (hq : Cst (s.v .v31) fun _ => 3329) (h0 : Cst (s.v .v29) fun _ => 0) {old : Nat → BitVec 32}
    (hout : CoeffsIn s.mem (fP s₀) (fun i => i % 32 < 8 * c)
      (fun i => BitVec.ofNat 32 (X i * 3303).val) old)
    (k : ∀ s', s'.gpr = s.gpr → St s₀ s' → (∀ r, r ≠ .v16 → r ≠ .v17 → r ≠ .v24 → r ≠ .v25 →
      s'.v r = s.v r) → Frame [polyRegion (fP s₀)] s.mem s'.mem →
      CoeffsIn s'.mem (fP s₀) (fun i => i % 32 < 8 * (c + 1))
        (fun i => BitVec.ofNat 32 (X i * 3303).val) old → WP isa (.block rest) s' Q) :
    WP isa (.block (((List.range 8).flatMap fun r =>
      [.vop (.mulH .mul .v16 (row r) .v22), .vop (.mulH .sqrdmulh .v17 (row r) .v23),
       .vop (.mulH .mls .v16 .v17 .v31), .vop (.shift .sshr .h8 .v17 .v16 15),
       .vop (.logic .and .v17 .v17 .v31), .vop (.add .h8 .v16 .v16 .v17),
       .vop (.perm .zip1 .h8 .v24 .v16 .v29), .vop (.perm .zip2 .h8 .v25 .v16 .v29),
       .strq .v24 .x3 (128 * r), .strq .v25 .x3 (128 * r + 16)]) ++ rest)) s Q := by
  rw [WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (fun n w => w.gpr = s.gpr ∧ w.rd = s.rd ∧
      w.wr = s.wr ∧ w.sp = s.sp ∧
      (∀ r, r ≠ .v16 → r ≠ .v17 → r ≠ .v24 → r ≠ .v25 → w.v r = s.v r) ∧
      Frame [polyRegion (fP s₀)] s.mem w.mem ∧
      CoeffsIn w.mem (fP s₀) (fun i => i % 32 < 8 * c ∨ (i / 32 < n ∧ i % 32 < 8 * c + 8))
        (fun i => BitVec.ofNat 32 (X i * 3303).val) old)
    (fun r w hr ⟨g, rd, wr, sp, v, fr, co⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨rfl, rfl, rfl, rfl, fun _ _ _ _ _ => rfl, Frame.refl _ _,
      hout.congr fun i _ => by omega⟩)
    fun w ⟨g, rd, wr, sp, v, fr, co⟩ =>
      k w g ⟨by rw [rd, st.rd], by rw [wr, st.wr], by rw [sp, st.sp], by rw [g, st.x0],
        by rw [g, st.x1]⟩ v fr (co.congr fun i hi => by omega)
  have st' : St s₀ w := ⟨by rw [rd, st.rd], by rw [wr, st.wr], by rw [sp, st.sp],
    by rw [g, st.x0], by rw [g, st.x1]⟩
  have nr := row_ne hr
  have rn := row_ne2425 r hr
  have vv : ∀ x, x ≠ .v16 → x ≠ .v17 → x ≠ .v24 → x ≠ .v25 → w.v x = s.v x := v
  refine scale_ok (x := row r) nr.1 (by rw [vv _ nr.1 nr.2.1 rn.1 rn.2]; exact hrows r hr) (by decide)
    (by rw [vv .v22 (by decide) (by decide) (by decide) (by decide)]; exact hz)
    (by rw [vv .v23 (by decide) (by decide) (by decide) (by decide)]; exact ht)
    (by rw [vv .v31 (by decide) (by decide) (by decide) (by decide)]; exact hq) fun w₀ c₀ hv => ?_
  have hi8 : 32 * r + 8 * c + 8 ≤ 256 := by omega
  have x3 : w₀.gpr .x3 = coeffAddr (fP s₀) (8 * c) := by rw [c₀.gpr, g, hx3]
  have st₀ : St s₀ w₀ := st'.vchg c₀
  refine wp_vop rfl fun w₁ h₁ => wp_vop rfl fun w₂ h₂ => ?_
  refine wp_strq (a := coeffAddr (fP s₀) (32 * r + 8 * c)) (by omega)
    (by rw [h₂.gpr, h₁.gpr, x3, coeffAddr, coeffAddr, ptr_add]; congr 2; omega)
    (by rw [h₂.wr, h₁.wr]; exact inF' hp st₀ (by omega)) fun w₃ h₃ => ?_
  refine wp_strq (a := coeffAddr (fP s₀) (32 * r + 8 * c + 4)) (by omega)
    (by rw [h₃.gpr, h₂.gpr, h₁.gpr, x3, coeffAddr, coeffAddr, ptr_add]; congr 2; omega)
    (by rw [h₃.wr, h₂.wr, h₁.wr]; exact inF' hp st₀ (by omega)) fun w₄ h₄ => wp_nil ?_
  have z29 : ∀ e < 8, vhalf (w₀.v .v29) e = 0 := fun e he => by
    rw [c₀.v _ (by decide), vv .v29 (by decide) (by decide) (by decide) (by decide)]; exact h0 e he
  have zz := fun k (hk : k < 4) => vword_zip_zero (x := w₀.v .v16) (z := w₀.v .v29) z29 hk
  have hvl : ∀ e < 8, (X (32 * r + 8 * c + e) * 3303).val < 2 ^ 32 := fun e _ => by
    have := val_lt (X (32 * r + 8 * c + e) * 3303); omega
  refine ⟨by rw [h₄.gpr, h₃.gpr, h₂.gpr, h₁.gpr, c₀.gpr, g], by rw [h₄.rd, h₃.rd, h₂.rd, h₁.rd, c₀.rd, rd],
    by rw [h₄.wr, h₃.wr, h₂.wr, h₁.wr, c₀.wr, wr], by rw [h₄.sp, h₃.sp, h₂.sp, h₁.sp, c₀.sp, sp],
    fun x a1 a2 a3 a4 => by
      rw [h₄.v, h₃.v, h₂.get x a4, h₁.get x a3, c₀.v x (by simp [a1, a2]), v x a1 a2 a3 a4], ?_, ?_⟩
  · rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem, c₀.mem]
    exact (fr.write (List.mem_singleton_self _) _ (contains_off (by omega) (by decide))).write
      (List.mem_singleton_self _) _ (contains_off (by omega) (by decide))
  · rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem, c₀.mem, h₃.v]
    refine (co.write16 (S' := fun i => i % 32 < 8 * c ∨ (i / 32 < r ∧ i % 32 < 8 * c + 8) ∨
      (32 * r + 8 * c ≤ i ∧ i < 32 * r + 8 * c + 4)) (by omega) (fun e he => ?_)
      (fun i hi => by omega)).write16 (by omega)
      (fun e he => ?_) (fun i hi => by omega)
    · rw [h₂.get .v24, h₁.v]
      apply BitVec.eq_of_toNat_eq
      rw [(zz e he).1, BitVec.toNat_ofNat, hv e (by omega), Nat.mod_eq_of_lt (hvl e (by omega))]
    · rw [h₂.v, h₁.get .v16, h₁.get .v29]
      apply BitVec.eq_of_toNat_eq
      rw [(zz e he).2, BitVec.toNat_ofNat, hv (4 + e) (by omega),
        show 32 * r + 8 * c + 4 + e = 32 * r + 8 * c + (4 + e) by omega,
        Nat.mod_eq_of_lt (hvl (4 + e) (by omega))]

end

/-! ## A chunk -/

/-- Lane `k` of `v18` (`invConsts`). -/
def izc (k : Nat) : Nat := if k < 7 then Impl.MlKem.AArch64.Ntt16.zeta (7 - k) else 3303

/-- After `c` chunks of pass 2 of the inverse, from the memory `mB` that pass 1 left. -/
structure LI2 (s₀ : State) (mB : Mem) (c : Nat) (s : State) : Prop where
  st : St s₀ s
  x2 : s.gpr .x2 = sP s₀ + BitVec.ofNat 64 (16 * c)
  x3 : s.gpr .x3 = coeffAddr (fP s₀) (8 * c)
  x5 : (s.gpr .x5).toNat = 4 - c
  frame : Frame [polyRegion (fP s₀)] mB s.mem
  scr : ∀ r < 8, ∀ i < 4, Rep (mB.read (sP s₀ + BitVec.ofNat 64 (64 * r + 16 * i)) 16)
    (fun e => (nttInvL 4 (P₀ s₀))[32 * r + 8 * i + e]!) (2 * 3329)
  out : CoeffsIn s.mem (fP s₀) (fun i => i % 32 < 8 * c)
    (fun i => BitVec.ofNat 32 ((nttInvL 7 (P₀ s₀))[i]! * 3303).val) fun i => coeffAt mB (fP s₀) i
  z : ∀ k < 8, vhalf (s.v .v18) k = BitVec.ofNat 16 (izc k)
  t : ∀ k < 8, vhalf (s.v .v19) k = BitVec.ofNat 16 (tw (izc k))
  q : Cst (s.v .v31) fun _ => 3329
  c10 : Cst (s.v .v30) fun _ => 10
  c0 : Cst (s.v .v29) fun _ => 0

/-- `scratch` as pass 1 left it. -/
theorem LI2.read {s₀ : State} (hp : Pre s₀) {mB : Mem} {c : Nat} {s : State} (h : LI2 s₀ mB c s)
    {o : Nat} (ho : o + 16 ≤ 1024) :
    s.mem.read (sP s₀ + BitVec.ofNat 64 o) 16 = mB.read (sP s₀ + BitVec.ofNat 64 o) 16 :=
  h.frame.read (r := polyRegion (sP s₀)) (contains_off ho (by decide))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.disj.symm) (by decide)

section
variable {rest : List Instr} {Q : State → Prop}

/-- The eight rows of chunk `c` of the polynomial `P` after pass 1, in a buffer at `sP`. -/
theorem i2_loadsOf {P : Poly} {sP : Addr} {c : Nat} {s : State}
    (hx2 : s.gpr .x2 = sP + BitVec.ofNat 64 (16 * c))
    (hin : ∀ r < 8, InRegions (s.rd ++ s.wr) (sP + BitVec.ofNat 64 (64 * r + 16 * c)) 16)
    (hscr : ∀ r < 8, Rep (s.mem.read (sP + BitVec.ofNat 64 (64 * r + 16 * c)) 16)
      (fun e => (nttInvL 4 P)[32 * r + 8 * c + e]!) (2 * 3329))
    (k : ∀ s', VChg bfRegs s s' →
      RowsI P c (List.replicate 8 4) (List.replicate 8 (2 * 3329)) 8 s' →
      WP isa (.block rest) s' Q) :
    WP isa (.block (((List.range 8).map fun r => .ldrq (row r) .x2 (64 * r)) ++ rest)) s Q := by
  rw [List.map_eq_flatMap, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n w => VChg bfRegs s w ∧ ∀ r < n, Rep (w.v (row r))
      (fun e => (nttInvL 4 P)[32 * r + 8 * c + e]!) (2 * 3329))
    (fun r w hr ⟨cw, hw⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨VChg.refl _ _, fun r hr => absurd hr (Nat.not_lt_zero r)⟩)
    fun s' ⟨c', h'⟩ => k s' c' fun r hr => by
      rw [getD_rep_lt hr, getD_rep_lt hr]; exact h' r hr
  refine wp_ldrq (a := sP + BitVec.ofNat 64 (64 * r + 16 * c)) (by omega)
    (by rw [cw.gpr, hx2, ptr_add]; congr 2; omega) (by rw [cw.rd, cw.wr]; exact hin r hr)
    fun w₁ h₁ => wp_nil ⟨(cw.trans h₁.chg).mono fun x hx => ?_, fun r' hr' => ?_⟩
  · simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hx
    · exact row_mem hr
  · by_cases e : r' = r
    · subst e
      rw [h₁.v, cw.mem]; exact hscr r' hr
    · rw [h₁.get _ (fun h => e (row_inj r' (by omega) r hr h))]
      exact hw r' (by omega)

/-- The eight rows of chunk `c` from `scratch`. -/
theorem i2_loads {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c < 4) {s : State} (st : St s₀ s)
    (hx2 : s.gpr .x2 = sP s₀ + BitVec.ofNat 64 (16 * c))
    (hscr : ∀ r < 8, Rep (s.mem.read (sP s₀ + BitVec.ofNat 64 (64 * r + 16 * c)) 16)
      (fun e => (nttInvL 4 (P₀ s₀))[32 * r + 8 * c + e]!) (2 * 3329))
    (k : ∀ s', VChg bfRegs s s' →
      RowsI (P₀ s₀) c (List.replicate 8 4) (List.replicate 8 (2 * 3329)) 8 s' →
      WP isa (.block rest) s' Q) :
    WP isa (.block (((List.range 8).map fun r => .ldrq (row r) .x2 (64 * r)) ++ rest)) s Q := by
  exact i2_loadsOf hx2 (fun r _ => inS' hp st (by omega)) hscr k

/-- Each row reduced to less than `q` in absolute value. -/
theorem rowsI_reduce {P : Poly} {c : Nat} {lay bnd : List Nat} {s : State} (h : RowsI P c lay bnd 8 s)
    (hb : ∀ r < 8, bnd.getD r 0 ≤ 32768) (h10 : Cst (s.v .v30) fun _ => 10)
    (hq : Cst (s.v .v31) fun _ => 3329)
    (k : ∀ s', VChg bfRegs s s' → RowsI P c lay (List.replicate 8 3329) 8 s' →
      WP isa (.block rest) s' Q) :
    WP isa (.block (((List.range 8).flatMap fun r => reduce (row r)) ++ rest)) s Q := by
  rw [WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n w => VChg bfRegs s w ∧ ∀ r < 8, Rep (w.v (row r))
      (fun e => (nttInvL (lay.getD r 0) P)[32 * r + 8 * c + e]!) (if r < n then 3329 else bnd.getD r 0))
    (fun r w hr ⟨cw, hw⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨VChg.refl _ _, fun r hr => by rw [ite_eq_right (Nat.not_lt_zero r)]; exact h r hr⟩)
    fun s' ⟨c', h'⟩ => k s' c' fun r hr => by
      rw [getD_rep_lt hr]; have := h' r hr; rw [ite_eq_left hr] at this; exact this
  have nr := row_ne hr
  have hx := hw r hr
  rw [ite_eq_right (Nat.lt_irrefl r)] at hx
  refine reduce_ok (x := row r) nr.1 hx (hb r hr) (by rw [cw.v _ (by decide)]; exact h10)
    (by rw [cw.v _ (by decide)]; exact hq) fun w₁ c₁ hx' => wp_nil ⟨(cw.trans c₁).mono fun x hx => ?_,
      fun r' hr' => ?_⟩
  · rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · decide
    · exact row_mem hr
  · by_cases e : r' = r
    · subst e
      rw [ite_eq_left (Nat.lt_succ_self r')]; exact hx'
    · rw [c₁.v _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨(row_ne hr').1, fun h => e (row_inj r' hr' r hr h)⟩)]
      have := hw r' hr'
      by_cases l : r' < r
      · rw [ite_eq_left l] at this; rw [ite_eq_left (by omega)]; exact this
      · rw [ite_eq_right l] at this; rw [ite_eq_right (by omega)]; exact this

end

/-- The registers pass 2's arithmetic changes. -/
abbrev p2Regs : List VReg := [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v22, .v23]

/-- The last three layers of the inverse on the rows of chunk `c` (`invPass2Arith`). -/
theorem ip2_arith {rest : List Instr} {Q : State → Prop} {P : Poly} {c : Nat} (hc : c < 4) {s₁ : State}
    (R₁ : RowsI P c (List.replicate 8 4) (List.replicate 8 (2 * 3329)) 8 s₁)
    (hz : ∀ k < 8, vhalf (s₁.v .v18) k = BitVec.ofNat 16 (izc k))
    (ht : ∀ k < 8, vhalf (s₁.v .v19) k = BitVec.ofNat 16 (tw (izc k)))
    (hq : Cst (s₁.v .v31) fun _ => 3329) (h10 : Cst (s₁.v .v30) fun _ => 10)
    (kk : ∀ s₁₁, VChg p2Regs s₁ s₁₁ →
      (∀ r < 8, Rep (s₁₁.v (row r)) (fun e => (nttInvL 7 P)[32 * r + 8 * c + e]!) (2 * 3329)) →
      Cst (s₁₁.v .v22) (fun _ => 3303) → Cst (s₁₁.v .v23) (fun _ => tw 3303) →
      WP isa (.block rest) s₁₁ Q) :
    WP isa (.block (invPass2Arith ++ rest)) s₁ Q := by
  simp only [invPass2Arith, List.append_assoc]
  have C₁ : VChg p2Regs s₁ s₁ := VChg.refl _ _
  refine rowsI_gsRows hc (k := 0) (K := 7) (by decide) [(0, 1)] (lay' := [5, 5, 4, 4, 4, 4, 4, 4])
    (bnd' := [13316, 3329, 6658, 6658, 6658, 6658, 6658, 6658]) (by decide) rfl R₁
    (by rw [C₁.v .v18 (by decide), hz 0 (by decide)]; rfl)
    (by rw [C₁.v .v19 (by decide), ht 0 (by decide)]; rfl)
    (by rw [C₁.v .v31 (by decide)]; exact hq) fun s₂ c₂ R₂ => ?_
  have C₂ : VChg p2Regs s₁ s₂ := (C₁.trans c₂).mono (by decide)
  refine rowsI_gsRows hc (k := 1) (K := 6) (by decide) [(2, 3)] (lay' := [5, 5, 5, 5, 4, 4, 4, 4])
    (bnd' := [13316, 3329, 13316, 3329, 6658, 6658, 6658, 6658]) (by decide) rfl R₂
    (by rw [C₂.v .v18 (by decide), hz 1 (by decide)]; rfl)
    (by rw [C₂.v .v19 (by decide), ht 1 (by decide)]; rfl)
    (by rw [C₂.v .v31 (by decide)]; exact hq) fun s₃ c₃ R₃ => ?_
  have C₃ : VChg p2Regs s₁ s₃ := (C₂.trans c₃).mono (by decide)
  refine rowsI_gsRows hc (k := 2) (K := 5) (by decide) [(4, 5)] (lay' := [5, 5, 5, 5, 5, 5, 4, 4])
    (bnd' := [13316, 3329, 13316, 3329, 13316, 3329, 6658, 6658]) (by decide) rfl R₃
    (by rw [C₃.v .v18 (by decide), hz 2 (by decide)]; rfl)
    (by rw [C₃.v .v19 (by decide), ht 2 (by decide)]; rfl)
    (by rw [C₃.v .v31 (by decide)]; exact hq) fun s₄ c₄ R₄ => ?_
  have C₄ : VChg p2Regs s₁ s₄ := (C₃.trans c₄).mono (by decide)
  refine rowsI_gsRows hc (k := 3) (K := 4) (by decide) [(6, 7)] (lay' := [5, 5, 5, 5, 5, 5, 5, 5])
    (bnd' := [13316, 3329, 13316, 3329, 13316, 3329, 13316, 3329]) (by decide) rfl R₄
    (by rw [C₄.v .v18 (by decide), hz 3 (by decide)]; rfl)
    (by rw [C₄.v .v19 (by decide), ht 3 (by decide)]; rfl)
    (by rw [C₄.v .v31 (by decide)]; exact hq) fun s₅ c₅ R₅ => ?_
  have C₅ : VChg p2Regs s₁ s₅ := (C₄.trans c₅).mono (by decide)
  refine rowsI_gsRows hc (k := 4) (K := 3) (by decide) [(0, 2), (1, 3)]
    (lay' := [6, 6, 6, 6, 5, 5, 5, 5])
    (bnd' := [26632, 6658, 3329, 3329, 13316, 3329, 13316, 3329]) (by decide) rfl R₅
    (by rw [C₅.v .v18 (by decide), hz 4 (by decide)]; rfl)
    (by rw [C₅.v .v19 (by decide), ht 4 (by decide)]; rfl)
    (by rw [C₅.v .v31 (by decide)]; exact hq) fun s₆ c₆ R₆ => ?_
  have C₆ : VChg p2Regs s₁ s₆ := (C₅.trans c₆).mono (by decide)
  refine rowsI_gsRows hc (k := 5) (K := 2) (by decide) [(4, 6), (5, 7)]
    (lay' := [6, 6, 6, 6, 6, 6, 6, 6])
    (bnd' := [26632, 6658, 3329, 3329, 26632, 6658, 3329, 3329]) (by decide) rfl R₆
    (by rw [C₆.v .v18 (by decide), hz 5 (by decide)]; rfl)
    (by rw [C₆.v .v19 (by decide), ht 5 (by decide)]; rfl)
    (by rw [C₆.v .v31 (by decide)]; exact hq) fun s₇ c₇ R₇ => ?_
  have C₇ : VChg p2Regs s₁ s₇ := (C₆.trans c₇).mono (by decide)
  refine rowsI_reduce R₇ (by decide) (by rw [C₇.v .v30 (by decide)]; exact h10)
    (by rw [C₇.v .v31 (by decide)]; exact hq) fun s₈ c₈ R₈ => ?_
  have C₈ : VChg p2Regs s₁ s₈ := (C₇.trans c₈).mono (by decide)
  refine rowsI_gsRows hc (k := 6) (K := 1) (by decide) [(0, 4), (1, 5), (2, 6), (3, 7)]
    (lay' := [7, 7, 7, 7, 7, 7, 7, 7])
    (bnd' := [6658, 6658, 6658, 6658, 3329, 3329, 3329, 3329]) (by decide) rfl R₈
    (by rw [C₈.v .v18 (by decide), hz 6 (by decide)]; rfl)
    (by rw [C₈.v .v19 (by decide), ht 6 (by decide)]; rfl)
    (by rw [C₈.v .v31 (by decide)]; exact hq) fun s₉ c₉ R₉ => ?_
  have C₉ : VChg p2Regs s₁ s₉ := (C₈.trans c₉).mono (by decide)
  refine wp_vop (eval_dupE (by decide)) fun s₁₀ h₁₀ => wp_vop (eval_dupE (by decide)) fun s₁₁ h₁₁ => ?_
  have C₁₁ : VChg p2Regs s₁ s₁₁ := ((C₉.trans h₁₀.chg).trans h₁₁.chg).mono (by decide)
  have hL : ∀ r < 8, [7, 7, 7, 7, 7, 7, 7, 7].getD r 0 = 7 ∧
      [6658, 6658, 6658, 6658, 3329, 3329, 3329, 3329].getD r 0 ≤ 2 * 3329 := by decide
  refine kk s₁₁ C₁₁ (fun r hr => ?_)
    (fun e he => by rw [h₁₁.get .v22, h₁₀.v, vhalf_ofVHalves _ he, C₉.v .v18 (by decide), hz 7 (by decide)]; rfl)
    (fun e he => by rw [h₁₁.v, vhalf_ofVHalves _ he, h₁₀.get .v19, C₉.v .v19 (by decide), ht 7 (by decide)]; rfl)
  have nr := row_ne hr
  rw [h₁₁.get _ nr.2.2.2.1, h₁₀.get _ nr.2.2.1]
  have := R₉ r hr
  rw [(hL r hr).1] at this
  exact this.mono (hL r hr).2

theorem ip2_body {s₀ : State} (hp : Pre s₀) {mB : Mem} {c : Nat} (hc : c < 4) {sb : State}
    (h : LI2 s₀ mB c sb) :
    WP isa (.block invPass2Body) sb fun s' => LI2 s₀ mB (c + 1) s' ∧ ((s'.gpr .x5).toNat ≠ 0 ↔ c + 1 ≠ 4) := by
  simp only [invPass2Body, List.append_assoc]
  refine i2_loads hp hc h.st h.x2 (fun r hr => by rw [h.read hp (by omega)]; exact h.scr r hr c hc)
    fun s₁ c₁ R₁ => ?_
  refine ip2_arith hc R₁ (fun k hk => by rw [c₁.get .v18]; exact h.z k hk)
    (fun k hk => by rw [c₁.get .v19]; exact h.t k hk) (by rw [c₁.get .v31]; exact h.q)
    (by rw [c₁.get .v30]; exact h.c10) fun s₁₁ C' rows z22 t23 => ?_
  have C₁₁ : VChg p2Regs sb s₁₁ := ((c₁.mono (rs' := p2Regs) (by decide)).trans C').mono (by decide)
  have st₁₁ : St s₀ s₁₁ := h.st.vchg C₁₁
  refine scale_rows hp hc st₁₁ (by rw [C₁₁.gpr]; exact h.x3)
    (X := fun i => (nttInvL 7 (P₀ s₀))[i]!) rows z22 t23
    (by rw [C₁₁.v .v31 (by decide)]; exact h.q) (by rw [C₁₁.v .v29 (by decide)]; exact h.c0)
    (by rw [C₁₁.mem]; exact h.out) fun w g₁ stw vw fr co => ?_
  refine WP.mono (WP.keepV (Q := fun w' => Keep [.x2, .x3, .x5] w w' ∧ w'.mem = w.mem ∧
      w'.gpr .x2 = w.gpr .x2 + BitVec.ofNat 64 16 ∧ w'.gpr .x3 = w.gpr .x3 + BitVec.ofNat 64 32 ∧
      w'.gpr .x5 = w.gpr .x5 - BitVec.ofNat 64 1)
    (by decide)
    (wp_addImm (by decide) fun w₁ k₁ e₁ => wp_addImm (by decide) fun w₂ k₂ e₂ =>
      wp_subImm (by decide) fun w₃ k₃ e₃ =>
        wp_nil ⟨((k₁.keep.trans k₂.keep).trans k₃.keep).mono,
          by rw [k₃.mem, k₂.mem, k₁.mem],
          by rw [k₃.gpr .x2 (by decide), k₂.gpr .x2 (by decide), e₁],
          by rw [k₃.gpr .x3 (by decide), e₂, k₁.gpr .x3 (by decide)],
          by rw [e₃, k₂.gpr .x5 (by decide), k₁.gpr .x5 (by decide)]⟩))
    fun w' ⟨⟨kw, mw, e2, e3, e5⟩, hv⟩ => ?_
  have gw : w.gpr = sb.gpr := by rw [g₁, C₁₁.gpr]
  have x5' : (w'.gpr .x5).toNat = 4 - (c + 1) := by
    rw [e5, gw, toNat_sub_n (by rw [h.x5]; simp; omega), h.x5]; simp; omega
  have vv : ∀ r ∈ [VReg.v18, .v19, .v29, .v30, .v31], w'.v r = sb.v r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      rw [hv, vw _ (by decide) (by decide) (by decide) (by decide), C₁₁.v _ (by decide)]
  refine ⟨⟨stw.keep kw, by rw [e2, gw, h.x2, ptr_add]; congr 2,
    by rw [e3, gw, h.x3, coeffAddr, coeffAddr, ptr_add]; congr 2, x5',
    by rw [mw]; exact h.frame.trans (by rw [← C₁₁.mem]; exact fr), h.scr, by rw [mw]; exact co,
    fun k hk => by rw [vv .v18 (by decide)]; exact h.z k hk,
    fun k hk => by rw [vv .v19 (by decide)]; exact h.t k hk,
    by rw [vv .v31 (by decide)]; exact h.q, by rw [vv .v30 (by decide)]; exact h.c10,
    by rw [vv .v29 (by decide)]; exact h.c0⟩, by rw [x5']; omega⟩

end VG.Proof.MlKem.AArch64.Ntt16
