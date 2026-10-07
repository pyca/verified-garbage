import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacOps
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacLay
import VerifiedGarbage.Proof.Weierstrass.JacCoZ

/-!
# The Jacobian window method on x86-64: its field programs

The table's co-Z formulas, DBLU and ZADDU, as numbered programs (`dbluN`,
`zadduN`: `dbluN_run`, `zadduN_run`) renamed to the table's slots (`tblσ`,
`tblProg_ok`); and the loop's addition `D = R + T` with `T`'s powers
(`cadd_ok`, from `CachedJac`'s numbering).
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open Spec.Weierstrass

variable {K : JacWinCfg} {size : Nat} {C : Curve}

section
variable (hL : JacWinLay K size)
include hL

theorem jw_T_ne :
    K.E.x ≠ K.E.y ∧ K.E.x ≠ K.E.z ∧ K.E.y ≠ K.E.z ∧ K.z2 ≠ K.E.z ∧ K.z2 + 8 * K.M.n ≠ K.E.z ∧
      K.z2 + 8 * K.M.n ≠ K.z2 := by
  have := hL.n0
  rw [hL.Tz3, hL.Tx, hL.Ty, hL.Tz, hL.Tz2]
  unfold jg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> have := Nat.eq_of_mul_eq_mul_left
    (show 0 < 8 * K.M.n by omega) (Nat.add_left_cancel h) <;> omega

end

/-! ## The table's co-Z formulas -/

/-- The slots the table's formulas write: `D`'s `x` and `y`, the temporaries
and `T`'s five. -/
def tblW (K : JacWinCfg) : List Nat :=
  [K.D.x, K.D.y, K.S.t0, K.S.t1, K.S.t2, K.S.t3, K.S.t4, K.S.t5, K.E.x, K.E.y, K.E.z, K.z2,
    K.z2 + 8 * K.M.n]

/-- The table's slot `i`: `tblW`'s `0 … 12`, then `P`'s `13 … 15`. -/
def tblσ (K : JacWinCfg) (i : Nat) : Nat := (tblW K ++ [K.P.x, K.P.y, K.P.z]).getD i K.P.x

/-- DBLU on numbered slots (`tblσ`). -/
def dbluN : List FOp :=
  [.mul 2 13 13, .mul 3 14 14, .mul 4 3 3, .mul 5 13 3, .add 5 5 5, .add 5 5 5, .sub 6 2 15,
   .add 7 6 6, .add 6 7 6, .mul 8 6 6, .sub 8 8 5, .sub 8 8 5, .sub 7 5 8, .mul 9 6 7,
   .add 4 4 4, .add 4 4 4, .add 4 4 4, .sub 9 9 4, .add 10 14 14, .mul 11 10 10, .mul 12 11 10]

/-- ZADDU on numbered slots (`tblσ`). -/
def zadduN : List FOp :=
  [.sub 2 0 8, .mul 3 2 2, .mul 10 10 2, .mul 0 0 3, .mul 5 8 3, .sub 6 1 9, .mul 7 6 6,
   .sub 4 0 5, .mul 1 1 4, .sub 8 7 0, .sub 8 8 5, .sub 9 0 8, .mul 9 6 9, .sub 9 9 1,
   .mul 11 11 3, .mul 12 11 10]

theorem dblu_eq (K : JacWinCfg) : K.dbluOps = dbluN.map (FOp.rename (tblσ K)) := rfl

theorem zaddu_eq (K : JacWinCfg) : K.zadduOps = zadduN.map (FOp.rename (tblσ K)) := rfl

theorem map_out_rename (σ : Nat → Nat) (N : List FOp) :
    (N.map (FOp.rename σ)).map FOp.out = (N.map FOp.out).map σ := by
  simp only [List.map_map]
  exact List.map_congr_left fun op _ => FOp.out_rename σ op

theorem dbluN_out : ∀ op ∈ dbluN, op.out < 13 := by decide

theorem zadduN_out : ∀ op ∈ zadduN, op.out < 13 := by decide

theorem dbluN_reads : readsOk dbluN [13, 14, 15] = true := by decide

theorem zadduN_reads : readsOk zadduN [0, 1, 8, 9, 10, 11] = true := by decide

/-- DBLU from `P = (x, y, 1)`: `T = 2 P` with its powers, and `(t3, t2)` is
`P` scaled by `T`'s `Z`. -/
theorem dbluN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) (h15 : e 15 = 1) :
    (runOps dbluN e 8, runOps dbluN e 9, runOps dbluN e 10) = dblJF (e 13) (e 14) 1 ∧
      runOps dbluN e 11 = runOps dbluN e 10 * runOps dbluN e 10 ∧
      runOps dbluN e 12 = runOps dbluN e 11 * runOps dbluN e 10 ∧
      runOps dbluN e 5 * (1 * 1) = e 13 * (runOps dbluN e 10 * runOps dbluN e 10) ∧
      runOps dbluN e 4 * (1 * 1 * 1) =
        e 14 * (runOps dbluN e 10 * runOps dbluN e 10 * runOps dbluN e 10) := by
  simp only [dbluN, runOps, List.foldl_cons, List.foldl_nil, FOp.run, Function.update_apply]
  simp only [Nat.reduceEqDiff, ite_true, ite_false, h15, dblJF, Prod.mk.injEq]
  refine ⟨⟨?_, ?_, ?_⟩, trivial, trivial, ?_, ?_⟩ <;> grind

/-- ZADDU of `D = (X1, Y1)` and `T = (X2, Y2)` sharing `Z`, with `T`'s powers. -/
theorem zadduN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    ((runOps zadduN e 8, runOps zadduN e 9, runOps zadduN e 10), (runOps zadduN e 0, runOps zadduN e 1)) =
        zadduF (e 0) (e 1) (e 8) (e 9) (e 10) ∧
      (e 11 = e 10 * e 10 → runOps zadduN e 11 = runOps zadduN e 10 * runOps zadduN e 10) ∧
      runOps zadduN e 12 = runOps zadduN e 11 * runOps zadduN e 10 := by
  simp only [zadduN, runOps, List.foldl_cons, List.foldl_nil, FOp.run, Function.update_apply]
  simp only [Nat.reduceEqDiff, ite_true, ite_false, zadduF]
  refine ⟨?_, fun h => ?_, ?_⟩ <;> first | trivial | grind

/-- `D`'s `x`, `y` and the temporaries are other slots. -/
theorem tblW_other : ∀ x ∈ [K.D.x, K.D.y, K.S.t0, K.S.t1, K.S.t2, K.S.t3, K.S.t4, K.S.t5],
    x ∈ jwOther K := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> jw_mem

section
variable (hL : JacWinLay K size)
include hL

theorem tblW_eq : tblW K = [K.D.x, K.D.y, K.S.t0, K.S.t1, K.S.t2, K.S.t3, K.S.t4, K.S.t5] ++
    (List.range 5).map (fun c => jg K (80 + c)) := by
  rw [tblW, hL.Tz3, hL.Tx, hL.Ty, hL.Tz, hL.Tz2]; rfl

theorem tblW_nodup : (tblW K).Nodup := by
  have hn0 := hL.n0
  have inj : ∀ a b : Nat, jg K (80 + a) = jg K (80 + b) → a = b := fun a b e => by
    unfold jg at e
    have := Nat.eq_of_mul_eq_mul_left (show 0 < 8 * K.M.n by omega) (Nat.add_left_cancel e); omega
  rw [tblW_eq hL, List.nodup_append]
  refine ⟨hL.nodup.sublist (.cons _ (.cons _ (.cons _ (.cons_cons _ (.cons_cons _ (.cons _ (.cons _
    (.refl _)))))))), List.Pairwise.map _ (fun a b hab e => hab (inj a b e)) List.nodup_range,
    fun a ha b hb e => ?_⟩
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
  exact hL.jg_ne (List.mem_append_right _ (tblW_other a ha)) (by have := List.mem_range.mp hc; omega) e

theorem tblW_P : ∀ x ∈ [K.P.x, K.P.y, K.P.z], x ∉ tblW K := by
  intro x hx hw
  have hro : x ∈ jwRo K := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> jw_mem
  rw [tblW_eq hL] at hw
  rcases List.mem_append.mp hw with hw | hw
  · exact hL.ro x hro (tblW_other x hw)
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw
    exact hL.jg_ne (List.mem_append_left _ hro) (by have := List.mem_range.mp hc; omega) rfl

theorem tblW_slots : ∀ x ∈ tblW K ++ [K.P.x, K.P.y, K.P.z], x ∈ jwSlots K := by
  intro x hx
  rw [tblW_eq hL] at hx
  rcases List.mem_append.mp hx with hx | hx
  · rcases List.mem_append.mp hx with hx | hx
    · exact other_mem (tblW_other x hx)
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
      exact jg_mem (by have := List.mem_range.mp hc; omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact ro_mem (by jw_mem)

/-- A numbered program of the table's on its slots: it writes `tblW`, and its
values are the numbered program's. -/
theorem tblProg_ok (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {N : List FOp} (hout : ∀ op ∈ N, op.out < 13)
    {Rd : List Nat} (hR : readsOk N Rd = true) {base : Addr} {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p (· ∈ jwSlots K) V E s) (hV : ∀ i ∈ Rd, tblσ K i ∈ V) :
    WP isa (ForwardField.programB K.M (N.map (FOp.rename (tblσ K)))) s fun t =>
      ProgKeep K.M base (tblW K) s t ∧
      Inv K.M base size C.p (· ∈ jwSlots K) (validAfter (N.map (FOp.rename (tblσ K))) V)
        (runOps (N.map (FOp.rename (tblσ K))) E) t ∧
      ∀ i, runOps (N.map (FOp.rename (tblσ K))) E (tblσ K i) = runOps N (fun y => E (tblσ K y)) i := by
  have hd := tblW_P hL
  have hinj : ∀ op ∈ N, ∀ y, tblσ K y = tblσ K op.out → y = op.out := fun op hop y =>
    getD_append_inj (tblW_nodup hL) hd (hd _ (List.mem_cons_self ..)) (by
      simpa [tblW] using hout op hop) y
  have hmem : ∀ i, tblσ K i ∈ jwSlots K := fun i =>
    tblW_slots hL _ (getD_append_mem (List.mem_cons_self (a := K.P.x) (l := [K.P.y, K.P.z])) i)
  have hS : ∀ op ∈ N.map (FOp.rename (tblσ K)), ∀ x ∈ op.out :: op.ins, x ∈ jwSlots K := by
    intro op hop
    obtain ⟨op', _, rfl⟩ := List.mem_map.mp hop
    cases op' <;> simp only [FOp.rename, FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil,
      or_false] <;> rintro x (rfl | rfl | rfl) <;> exact hmem _
  have hR' : readsOk (N.map (FOp.rename (tblσ K))) V = true :=
    readsOk_mono (readsOk_rename (tblσ K) hR) fun x hx => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact hV i hi
  refine WP.mono (ForwardField.programB_ok hL.lay hp _ hI hS hR') fun t ⟨kt, it⟩ =>
    ⟨kt.mono ?_, it, fun i => congrFun (runOps_rename (tblσ K) N E hinj) i⟩
  intro x hx
  rw [map_out_rename] at hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hi
  have hlt := hout op hop
  unfold tblσ
  rw [getD_append_left (by simpa [tblW] using hlt)]
  exact List.getElem_mem _

omit hL in
/-- A slot a numbered program of the table's writes holds a value after it. -/
theorem tbl_valid {N : List FOp} {V : List Nat} {i : Nat} (h : i ∈ N.map FOp.out) :
    tblσ K i ∈ validAfter (N.map (FOp.rename (tblσ K))) V := by
  rw [mem_validAfter, map_out_rename]
  exact Or.inr (List.mem_map_of_mem h)

end

/-! ## The loop's addition -/

/-- `D = R + T` with `T`'s cached `Z²` and `Z³`. -/
theorem cadd_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {base : Addr}
    {V : List Nat} {E : Nat → Fe C} {s : State} (hI : Inv K.M base size C.p (· ∈ jwSlots K) V E s)
    (hV : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.z2, K.z2 + 8 * K.M.n], x ∈ V)
    (h2 : E K.z2 = E K.E.z * E K.E.z) (h3 : E (K.z2 + 8 * K.M.n) = E K.z2 * E K.E.z) :
    WP isa (ForwardField.programB K.M K.addOps) s fun t =>
      ProgKeep K.M base (rcbW K.S K.D) s t ∧ ∃ E' : Nat → Fe C,
        Inv K.M base size C.p (· ∈ jwSlots K) ([K.D.x, K.D.y, K.D.z] ++ V) E' t ∧
        (E' K.D.x, E' K.D.y, E' K.D.z) =
          jacAddF (E K.R.x) (E K.R.y) (E K.R.z) (E K.E.x) (E K.E.y) (E K.E.z) := by
  have hn0 := hL.n0
  have o := fun i j hi hj h => hL.oth_ne (K := K) (i := i) (j := j) hi hj h
  have hroW : ∀ x ∈ jwRo K ++ [K.R.x, K.R.y, K.R.z], x ∉ rcbW K.S K.D := by
    intro x hx hw
    simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases List.mem_append.mp hx with hx | hx
    · exact hL.ro x hx (by rcases hw with h | h | h | h | h | h | h | h | h <;> rw [h] <;> jw_mem)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;>
        rcases hw with h | h | h | h | h | h | h | h | h
      all_goals first
        | exact o 0 7 (by decide) (by decide) (by decide) h | exact o 0 8 (by decide) (by decide) (by decide) h
        | exact o 0 9 (by decide) (by decide) (by decide) h | exact o 0 10 (by decide) (by decide) (by decide) h
        | exact o 0 11 (by decide) (by decide) (by decide) h | exact o 0 12 (by decide) (by decide) (by decide) h
        | exact o 0 3 (by decide) (by decide) (by decide) h | exact o 0 4 (by decide) (by decide) (by decide) h
        | exact o 0 5 (by decide) (by decide) (by decide) h
        | exact o 1 7 (by decide) (by decide) (by decide) h | exact o 1 8 (by decide) (by decide) (by decide) h
        | exact o 1 9 (by decide) (by decide) (by decide) h | exact o 1 10 (by decide) (by decide) (by decide) h
        | exact o 1 11 (by decide) (by decide) (by decide) h | exact o 1 12 (by decide) (by decide) (by decide) h
        | exact o 1 3 (by decide) (by decide) (by decide) h | exact o 1 4 (by decide) (by decide) (by decide) h
        | exact o 1 5 (by decide) (by decide) (by decide) h
        | exact o 2 7 (by decide) (by decide) (by decide) h | exact o 2 8 (by decide) (by decide) (by decide) h
        | exact o 2 9 (by decide) (by decide) (by decide) h | exact o 2 10 (by decide) (by decide) (by decide) h
        | exact o 2 11 (by decide) (by decide) (by decide) h | exact o 2 12 (by decide) (by decide) (by decide) h
        | exact o 2 3 (by decide) (by decide) (by decide) h | exact o 2 4 (by decide) (by decide) (by decide) h
        | exact o 2 5 (by decide) (by decide) (by decide) h
  have hgW : ∀ c < 5, jg K (80 + c) ∉ rcbW K.S K.D := by
    intro c hc hw
    simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] at hw
    have g := fun x (hx : x ∈ jwOther K) => hL.jg_ne (List.mem_append_right _ hx) (i := 80 + c) (by omega)
    rcases hw with h | h | h | h | h | h | h | h | h <;> exact g _ (by jw_mem) h.symm
  have hA : RcbApart K.S K.R K.E K.D := by
    refine ⟨?_, fun x hx => ?_⟩
    · simp only [rcbW, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
        and_true]
      refine ⟨⟨o 7 8 (by decide) (by decide) (by decide), o 7 9 (by decide) (by decide) (by decide),
        o 7 10 (by decide) (by decide) (by decide), o 7 11 (by decide) (by decide) (by decide),
        o 7 12 (by decide) (by decide) (by decide), o 7 3 (by decide) (by decide) (by decide),
        o 7 4 (by decide) (by decide) (by decide), o 7 5 (by decide) (by decide) (by decide)⟩,
        ⟨o 8 9 (by decide) (by decide) (by decide), o 8 10 (by decide) (by decide) (by decide),
        o 8 11 (by decide) (by decide) (by decide), o 8 12 (by decide) (by decide) (by decide),
        o 8 3 (by decide) (by decide) (by decide), o 8 4 (by decide) (by decide) (by decide),
        o 8 5 (by decide) (by decide) (by decide)⟩,
        ⟨o 9 10 (by decide) (by decide) (by decide), o 9 11 (by decide) (by decide) (by decide),
        o 9 12 (by decide) (by decide) (by decide), o 9 3 (by decide) (by decide) (by decide),
        o 9 4 (by decide) (by decide) (by decide), o 9 5 (by decide) (by decide) (by decide)⟩,
        ⟨o 10 11 (by decide) (by decide) (by decide), o 10 12 (by decide) (by decide) (by decide),
        o 10 3 (by decide) (by decide) (by decide), o 10 4 (by decide) (by decide) (by decide),
        o 10 5 (by decide) (by decide) (by decide)⟩,
        ⟨o 11 12 (by decide) (by decide) (by decide), o 11 3 (by decide) (by decide) (by decide),
        o 11 4 (by decide) (by decide) (by decide), o 11 5 (by decide) (by decide) (by decide)⟩,
        ⟨o 12 3 (by decide) (by decide) (by decide), o 12 4 (by decide) (by decide) (by decide),
        o 12 5 (by decide) (by decide) (by decide)⟩,
        ⟨o 3 4 (by decide) (by decide) (by decide), o 3 5 (by decide) (by decide) (by decide)⟩,
        o 4 5 (by decide) (by decide) (by decide), not_false⟩
    · simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hroW _ (by jw_mem)
      · exact hroW _ (by jw_mem)
      · exact hroW _ (by simp)
      · exact hroW _ (by simp)
      · exact hroW _ (by simp)
      · rw [hL.Tx]; exact hgW 0 (by decide)
      · rw [hL.Ty]; exact hgW 1 (by decide)
      · rw [hL.Tz]; exact hgW 2 (by decide)
  have h2a : K.z2 ∉ rcbW K.S K.D := by rw [hL.Tz2]; exact hgW 3 (by decide)
  have h3a : K.z2 + 8 * K.M.n ∉ rcbW K.S K.D := by rw [hL.Tz3]; exact hgW 4 (by decide)
  have hSl : ∀ x ∈ (rcbW K.S K.D ++ rcbR K.S K.R K.E) ++ [K.z2, K.z2 + 8 * K.M.n], x ∈ jwSlots K := by
    intro x hx
    simp only [rcbW, rcbR, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rw [hL.Tz3, hL.Tx, hL.Ty, hL.Tz, hL.Tz2] at hx
    rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h]
    all_goals first
      | exact jg_mem (by decide) | jw_mem
  have hr : readsOk K.addOps V = true := by
    rw [JacWinCfg.addOps, CachedJac.head_eq K.M.n K.S K.R K.E K.D K.z2,
      CachedJac.tail_eq K.M.n K.S K.R K.E K.D K.z2, ← List.map_append]
    refine readsOk_mono (readsOk_rename (CachedJac.rename K.M.n K.S K.R K.E K.D K.z2)
      (show readsOk (CachedJac.headN ++ jacTailN) [11, 12, 13, 14, 15, 16, 17, 18] = true by decide))
      fun x hx => hV x ?_
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with h | h | h | h | h | h | h | h <;> rw [h] <;> simp [CachedJac.rename, rcbσ, rcbW, rcbR]
  have hs : ∀ op ∈ K.addOps, ∀ x ∈ op.out :: op.ins, x ∈ jwSlots K := by
    rw [JacWinCfg.addOps, CachedJac.head_eq K.M.n K.S K.R K.E K.D K.z2,
      CachedJac.tail_eq K.M.n K.S K.R K.E K.D K.z2, ← List.map_append]
    exact fun op hop x hx => hSl x (CachedJac.slots op hop x hx)
  refine WP.mono (ForwardField.programB_ok hL.lay hp _ hI hs hr) fun t ⟨kt, it⟩ =>
    ⟨kt.mono ?_, _, it.sub fun x hx => ?_, CachedJac.full_run hA h2a h3a E h2 h3⟩
  · intro x hx
    obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hx
    rw [JacWinCfg.addOps, CachedJac.head_eq K.M.n K.S K.R K.E K.D K.z2,
      CachedJac.tail_eq K.M.n K.S K.R K.E K.D K.z2, ← List.map_append] at hop
    exact CachedJac.out (show ∀ op ∈ CachedJac.headN ++ jacTailN, op.out < 9 by decide) hop
  · rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · right
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [JacWinCfg.addOps, jacTail, FOp.out]
    · exact Or.inl hx

end VG.Proof.Weierstrass.X86_64
