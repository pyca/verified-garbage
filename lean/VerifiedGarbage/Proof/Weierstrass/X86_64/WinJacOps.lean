import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacOps
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacLay

/-!
# The Jacobian window method on x86-64: its field programs

`T`'s cached powers `Z²`, `Z³` (`cacheOps_ok`); the table's step
`T = T + P` by the mixed addition, in place, and the powers (`maddCache_ok`,
from the numbered program `maddN`, renamed); and the loop's addition
`D = R + T` with `T`'s powers (`cadd_ok`, from `CachedJac`'s numbering).
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

/-- `T`'s `Z²` and `Z³`. -/
theorem cacheOps_ok (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {base : Addr} {V : List Nat}
    {E : Nat → Fe C} {s : State} (hI : Inv K.M base size C.p (· ∈ jwSlots K) V E s) (hV : K.E.z ∈ V) :
    WP isa (ForwardField.programB K.M K.cacheOps) s fun t =>
      ProgKeep K.M base [K.z2, K.z2 + 8 * K.M.n] s t ∧ ∃ E' : Nat → Fe C,
        Inv K.M base size C.p (· ∈ jwSlots K) ([K.z2, K.z2 + 8 * K.M.n] ++ V) E' t ∧
        E' K.E.z = E K.E.z ∧ E' K.z2 = E K.E.z * E K.E.z ∧ E' (K.z2 + 8 * K.M.n) = E' K.z2 * E K.E.z := by
  obtain ⟨-, -, -, h2, h3, h23⟩ := jw_T_ne hL
  have mz : K.E.z ∈ jwSlots K := by rw [hL.Tz]; exact jg_mem (by decide)
  have m2 : K.z2 ∈ jwSlots K := by rw [hL.Tz2]; exact jg_mem (by decide)
  have m3 : K.z2 + 8 * K.M.n ∈ jwSlots K := by rw [hL.Tz3]; exact jg_mem (by decide)
  have hS : ∀ op ∈ K.cacheOps, ∀ x ∈ op.out :: op.ins, x ∈ jwSlots K := by
    intro op hop x hx
    simp only [JacWinCfg.cacheOps, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl <;>
      simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false] at hx <;>
      rcases hx with rfl | rfl | rfl <;> assumption
  have hR : readsOk K.cacheOps V = true := by
    simp [JacWinCfg.cacheOps, readsOk, FOp.ins, FOp.out, hV]
  refine WP.mono (ForwardField.programB_ok hL.lay hp _ hI hS hR) fun t ⟨kt, it⟩ =>
    ⟨kt.mono fun w hw => by simpa [JacWinCfg.cacheOps, FOp.out] using hw, _, it.sub fun x hx => ?_, ?_, ?_, ?_⟩
  · rw [mem_validAfter]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl) | hx
    · exact Or.inr (by simp [JacWinCfg.cacheOps, FOp.out])
    · exact Or.inr (by simp [JacWinCfg.cacheOps, FOp.out])
    · exact Or.inl hx
  · simp only [JacWinCfg.cacheOps, runOps, List.foldl_cons, List.foldl_nil, FOp.run, Function.update_apply,
      Ne.symm h2, Ne.symm h3, ite_false]
  · simp only [JacWinCfg.cacheOps, runOps, List.foldl_cons, List.foldl_nil, FOp.run, Function.update_apply,
      Ne.symm h2, Ne.symm h23, ite_false, ite_true]
  · simp only [JacWinCfg.cacheOps, runOps, List.foldl_cons, List.foldl_nil, FOp.run, Function.update_apply,
      Ne.symm h23, Ne.symm h2, ite_false, ite_true]

end

/-! ## The table's step -/

/-- The table's step on numbered slots: `t0 … t5` are `0 … 5`, `T`'s five
coordinates `6 … 10`, `P` `11 … 13`. -/
def maddN : List FOp :=
  jacMixedHead ⟨14, 15, 0, 1, 2, 3, 4, 5⟩ ⟨6, 7, 8⟩ ⟨11, 12, 13⟩ ++
    jacMixedTail ⟨14, 15, 0, 1, 2, 3, 4, 5⟩ ⟨6, 7, 8⟩ ⟨11, 12, 13⟩ ⟨6, 7, 8⟩ ++ [.mul 9 8 8, .mul 10 9 8]

/-- The table step's slot `i`. -/
def maddσ (K : JacWinCfg) (i : Nat) : Nat :=
  ([K.S.t0, K.S.t1, K.S.t2, K.S.t3, K.S.t4, K.S.t5, K.E.x, K.E.y, K.E.z, K.z2, K.z2 + 8 * K.M.n] ++
    [K.P.x, K.P.y, K.P.z]).getD i K.P.x

theorem madd_eq (K : JacWinCfg) : K.maddOps ++ K.cacheOps = maddN.map (FOp.rename (maddσ K)) := rfl

theorem map_out_rename (σ : Nat → Nat) (N : List FOp) :
    (N.map (FOp.rename σ)).map FOp.out = (N.map FOp.out).map σ := by
  simp only [List.map_map]
  exact List.map_congr_left fun op _ => FOp.out_rename σ op

theorem maddN_out : ∀ op ∈ maddN, op.out < 11 := by decide

theorem maddN_reads : readsOk maddN [2, 4, 6, 7, 8, 11, 12] = true := by decide

theorem maddN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) (h2 : e 2 = e 6) (h4 : e 4 = e 7) :
    (runOps maddN e 6, runOps maddN e 7, runOps maddN e 8) = jacAddF (e 6) (e 7) (e 8) (e 11) (e 12) 1 ∧
      runOps maddN e 9 = runOps maddN e 8 * runOps maddN e 8 ∧
      runOps maddN e 10 = runOps maddN e 9 * runOps maddN e 8 := by
  simp only [maddN, jacMixedHead, jacMixedTail, jacTail, List.take, List.cons_append, List.nil_append,
    runOps, List.foldl_cons, List.foldl_nil, FOp.run, Function.update_apply]
  simp only [Nat.reduceEqDiff, ite_true, ite_false, h2, h4, jacAddF, Prod.mk.injEq]
  refine ⟨⟨?_, ?_, ?_⟩, trivial, trivial⟩ <;> grind

/-- `T = T + P` by the mixed addition, in place, and `T`'s powers, from
`t2 = X` and `t4 = Y`. -/
theorem maddCache_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {base : Addr}
    {V : List Nat} {E : Nat → Fe C} {s : State} (hI : Inv K.M base size C.p (· ∈ jwSlots K) V E s)
    (hV : ∀ x ∈ [K.S.t2, K.S.t4, K.E.x, K.E.y, K.E.z, K.P.x, K.P.y], x ∈ V)
    (h2 : E K.S.t2 = E K.E.x) (h4 : E K.S.t4 = E K.E.y) :
    WP isa (ForwardField.programB K.M (K.maddOps ++ K.cacheOps)) s fun t =>
      ProgKeep K.M base (rcbW K.S K.E ++ [K.z2, K.z2 + 8 * K.M.n]) s t ∧ ∃ E' : Nat → Fe C,
        Inv K.M base size C.p (· ∈ jwSlots K) ([K.E.x, K.E.y, K.E.z, K.z2, K.z2 + 8 * K.M.n] ++ V) E' t ∧
        (E' K.E.x, E' K.E.y, E' K.E.z) = jacAddF (E K.E.x) (E K.E.y) (E K.E.z) (E K.P.x) (E K.P.y) 1 ∧
        E' K.z2 = E' K.E.z * E' K.E.z ∧ E' (K.z2 + 8 * K.M.n) = E' K.z2 * E' K.E.z := by
  have hn0 := hL.n0
  have T5 : ∀ c < 5, jg K (80 + c) ∈ jwSlots K := fun c hc => jg_mem (by omega)
  -- The written slots are distinct, and none is `P`'s.
  have hW : ([K.S.t0, K.S.t1, K.S.t2, K.S.t3, K.S.t4, K.S.t5, K.E.x, K.E.y, K.E.z, K.z2,
      K.z2 + 8 * K.M.n] : List Nat).Nodup := by
    rw [hL.Tz3, hL.Tx, hL.Ty, hL.Tz, hL.Tz2]
    have ht : ∀ i, 7 ≤ i → (hi : i < 13) → ∀ c < 5, (jwOther K)[i]'hi ≠ jg K (80 + c) := fun i h7 hi c hc =>
      hL.jg_ne (List.mem_append_right _ (List.getElem_mem hi)) (by omega)
    have hg : ∀ c < 5, ∀ d < 5, c ≠ d → jg K (80 + c) ≠ jg K (80 + d) := fun c _ d _ h e => by
      unfold jg at e; have := Nat.eq_of_mul_eq_mul_left (show 0 < 8 * K.M.n by omega) (Nat.add_left_cancel e)
      omega
    have o := fun i j hi hj h => hL.oth_ne (K := K) (i := i) (j := j) hi hj h
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
    refine ⟨⟨o 7 8 (by decide) (by decide) (by decide), o 7 9 (by decide) (by decide) (by decide),
      o 7 10 (by decide) (by decide) (by decide), o 7 11 (by decide) (by decide) (by decide),
      o 7 12 (by decide) (by decide) (by decide), ht 7 (by decide) (by decide) 0 (by decide),
      ht 7 (by decide) (by decide) 1 (by decide), ht 7 (by decide) (by decide) 2 (by decide),
      ht 7 (by decide) (by decide) 3 (by decide), ht 7 (by decide) (by decide) 4 (by decide)⟩,
      ⟨o 8 9 (by decide) (by decide) (by decide), o 8 10 (by decide) (by decide) (by decide),
      o 8 11 (by decide) (by decide) (by decide), o 8 12 (by decide) (by decide) (by decide),
      ht 8 (by decide) (by decide) 0 (by decide), ht 8 (by decide) (by decide) 1 (by decide),
      ht 8 (by decide) (by decide) 2 (by decide), ht 8 (by decide) (by decide) 3 (by decide),
      ht 8 (by decide) (by decide) 4 (by decide)⟩,
      ⟨o 9 10 (by decide) (by decide) (by decide), o 9 11 (by decide) (by decide) (by decide),
      o 9 12 (by decide) (by decide) (by decide), ht 9 (by decide) (by decide) 0 (by decide),
      ht 9 (by decide) (by decide) 1 (by decide), ht 9 (by decide) (by decide) 2 (by decide),
      ht 9 (by decide) (by decide) 3 (by decide), ht 9 (by decide) (by decide) 4 (by decide)⟩,
      ⟨o 10 11 (by decide) (by decide) (by decide), o 10 12 (by decide) (by decide) (by decide),
      ht 10 (by decide) (by decide) 0 (by decide), ht 10 (by decide) (by decide) 1 (by decide),
      ht 10 (by decide) (by decide) 2 (by decide), ht 10 (by decide) (by decide) 3 (by decide),
      ht 10 (by decide) (by decide) 4 (by decide)⟩,
      ⟨o 11 12 (by decide) (by decide) (by decide), ht 11 (by decide) (by decide) 0 (by decide),
      ht 11 (by decide) (by decide) 1 (by decide), ht 11 (by decide) (by decide) 2 (by decide),
      ht 11 (by decide) (by decide) 3 (by decide), ht 11 (by decide) (by decide) 4 (by decide)⟩,
      ⟨ht 12 (by decide) (by decide) 0 (by decide), ht 12 (by decide) (by decide) 1 (by decide),
      ht 12 (by decide) (by decide) 2 (by decide), ht 12 (by decide) (by decide) 3 (by decide),
      ht 12 (by decide) (by decide) 4 (by decide)⟩,
      ⟨hg 0 (by decide) 1 (by decide) (by decide), hg 0 (by decide) 2 (by decide) (by decide),
      hg 0 (by decide) 3 (by decide) (by decide), hg 0 (by decide) 4 (by decide) (by decide)⟩,
      ⟨hg 1 (by decide) 2 (by decide) (by decide), hg 1 (by decide) 3 (by decide) (by decide),
      hg 1 (by decide) 4 (by decide) (by decide)⟩,
      ⟨hg 2 (by decide) 3 (by decide) (by decide), hg 2 (by decide) 4 (by decide) (by decide)⟩,
      hg 3 (by decide) 4 (by decide) (by decide), not_false⟩
  have hP : ∀ x ∈ [K.P.x, K.P.y, K.P.z], x ∉ ([K.S.t0, K.S.t1, K.S.t2, K.S.t3, K.S.t4, K.S.t5, K.E.x,
      K.E.y, K.E.z, K.z2, K.z2 + 8 * K.M.n] : List Nat) := by
    intro x hx hw
    have hro : x ∈ jwRo K := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> jw_mem
    rw [hL.Tz3, hL.Tx, hL.Ty, hL.Tz, hL.Tz2] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    have r := hL.ro x hro
    have g := fun c (hc : c < 5) => hL.jg_ne (List.mem_append_left _ hro) (i := 80 + c) (by omega)
    rcases hw with h | h | h | h | h | h | h | h | h | h | h
    · exact r (by rw [h]; jw_mem)
    · exact r (by rw [h]; jw_mem)
    · exact r (by rw [h]; jw_mem)
    · exact r (by rw [h]; jw_mem)
    · exact r (by rw [h]; jw_mem)
    · exact r (by rw [h]; jw_mem)
    · exact g 0 (by decide) h
    · exact g 1 (by decide) h
    · exact g 2 (by decide) h
    · exact g 3 (by decide) h
    · exact g 4 (by decide) h
  have hinj : ∀ op ∈ maddN, ∀ y, maddσ K y = maddσ K op.out → y = op.out := fun op hop y =>
    getD_append_inj hW hP (hP _ (List.mem_cons_self ..)) (maddN_out op hop) y
  have hall : ∀ x ∈ ([K.S.t0, K.S.t1, K.S.t2, K.S.t3, K.S.t4, K.S.t5, K.E.x, K.E.y, K.E.z, K.z2,
      K.z2 + 8 * K.M.n] ++ [K.P.x, K.P.y, K.P.z] : List Nat), x ∈ jwSlots K := by
    intro x hx
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h
    all_goals first
      | (jw_mem; done)
      | (rw [hL.Tx]; exact jg_mem (by decide)) | (rw [hL.Ty]; exact jg_mem (by decide))
      | (rw [hL.Tz]; exact jg_mem (by decide)) | (rw [hL.Tz3]; exact jg_mem (by decide))
      | (rw [hL.Tz2]; exact jg_mem (by decide))
  have hmem : ∀ i, maddσ K i ∈ jwSlots K := fun i =>
    hall _ (getD_append_mem (List.mem_cons_self (a := K.P.x) (l := [K.P.y, K.P.z])) i)
  have hS : ∀ op ∈ maddN.map (FOp.rename (maddσ K)), ∀ x ∈ op.out :: op.ins, x ∈ jwSlots K := by
    intro op hop
    obtain ⟨op', _, rfl⟩ := List.mem_map.mp hop
    cases op' <;> simp only [FOp.rename, FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil,
      or_false] <;> rintro x (rfl | rfl | rfl) <;> exact hmem _
  have hR : readsOk (maddN.map (FOp.rename (maddσ K))) V = true :=
    readsOk_mono (readsOk_rename (maddσ K) maddN_reads) fun x hx => hV x (by
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with h | h | h | h | h | h | h <;> rw [h] <;> simp [maddσ])
  rw [madd_eq]
  refine WP.mono (ForwardField.programB_ok hL.lay hp _ hI hS hR) fun t ⟨kt, it⟩ =>
    ⟨kt.mono ?_, runOps (maddN.map (FOp.rename (maddσ K))) E, ?_, ?_⟩
  · intro x hx
    obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hx
    obtain ⟨op', hop', rfl⟩ := List.mem_map.mp hop
    rw [FOp.out_rename]
    have hlt := maddN_out op' hop'
    unfold maddσ
    rw [getD_append_left (by simpa using hlt)]
    have := List.getElem_mem (l := [K.S.t0, K.S.t1, K.S.t2, K.S.t3, K.S.t4, K.S.t5, K.E.x, K.E.y, K.E.z, K.z2,
      K.z2 + 8 * K.M.n]) (by simpa using hlt)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    simp only [rcbW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rcases this with h | h | h | h | h | h | h | h | h | h | h <;> simp [h]
  · refine it.sub fun x hx => ?_
    rw [mem_validAfter]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (h | h | h | h | h) | h
    all_goals first
      | exact Or.inl h
      | (refine Or.inr ?_; subst h; rw [map_out_rename])
    · exact List.mem_map.mpr ⟨6, by decide, rfl⟩
    · exact List.mem_map.mpr ⟨7, by decide, rfl⟩
    · exact List.mem_map.mpr ⟨8, by decide, rfl⟩
    · exact List.mem_map.mpr ⟨9, by decide, rfl⟩
    · exact List.mem_map.mpr ⟨10, by decide, rfl⟩
  · have hren := runOps_rename (maddσ K) maddN E hinj
    have hv := maddN_run (fun y => E (maddσ K y)) h2 h4
    have e : ∀ i, runOps (maddN.map (FOp.rename (maddσ K))) E (maddσ K i) =
        runOps maddN (fun y => E (maddσ K y)) i := fun i => congrFun hren i
    refine ⟨?_, ?_, ?_⟩
    · exact (congrArg₂ Prod.mk (e 6) (congrArg₂ Prod.mk (e 7) (e 8))).trans hv.1
    · exact (e 9).trans (hv.2.1.trans (by rw [← e 8]; rfl))
    · exact (e 10).trans (hv.2.2.trans (by rw [← e 9, ← e 8]; rfl))

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
