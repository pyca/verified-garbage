import VerifiedGarbage.Proof.Weierstrass.X86_64.PointOpsVal
import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacOps
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacState

/-!
# Point operations as functions on x86-64: what the cached addition computes

`addCachedBody`'s value: `R` becomes `jacAddCached` of the values of `R`,
`E` and `E`'s cached `Z²` and `Z³` at `sel`, whatever they are, through
its branches (`CachedJac.add`): `E` copied for `R`'s `Z = 0`, `R` for
`E`'s, else the header's `H` and `r`, then the doubling or the point at
infinity for `H = 0`, else the tail.
-/

namespace VG.Proof.Weierstrass.X86_64.PointOps

open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Weierstrass.X86_64.CachedJac (headN rename rename_inj head_eq tail_eq slots out)

/-- The specification's names for the values a branch writes to `o`: `o`'s
coordinates hold `r`, and the rest of `V` keeps its values, but for the
writes `W`. -/
def Val (M : Mod) (base : Addr) (size m : Nat) [NeZero m] (Sl : Nat → Prop) (W V : List Nat)
    (o : Pt) (r : Fin m × Fin m × Fin m) (s t : State) : Prop :=
  ProgKeep M base W s t ∧ ∃ E', Inv M base size m Sl (jacCoords o ++ V) E' t ∧ (E' o.x, E' o.y, E' o.z) = r

theorem headN_spec {m : Nat} [NeZero m] (e : Nat → Fin m) :
    runOps headN e 3 = e 14 * (e 13 * e 13) - e 11 * e 17 ∧
    runOps headN e 5 = e 15 * e 13 * (e 13 * e 13) - e 12 * e 18 := by
  simp only [headN, runOps, List.foldl_cons, List.foldl_nil, FOp.run, Function.update_apply]
  exact ⟨rfl, rfl⟩

theorem cachedN_spec {m : Nat} [NeZero m] (e : Nat → Fin m) :
    (runOps (headN ++ jacTailN) e 6, runOps (headN ++ jacTailN) e 7, runOps (headN ++ jacTailN) e 8) =
      Spec.Weierstrass.PointOps.jacTail (e 11 * e 17) (e 12 * e 18)
        (e 14 * (e 13 * e 13) - e 11 * e 17) (e 15 * e 13 * (e 13 * e 13) - e 12 * e 18)
        (e 13 * e 16) := by
  simp only [headN, jacTailN, jacTail, List.cons_append, List.nil_append, runOps, List.foldl_cons,
    List.foldl_nil, FOp.run, Function.update_apply]
  rfl

/-- What the cached addition's body needs of the slots: those of
`CachedJac.add`'s proofs, and that its programs read only `V` (`R`, `E`
and the cached powers) or what they wrote. -/
structure CachedLay (K : WinCfg) (sel size : Nat) (Sl : Nat → Prop) : Prop where
  lay : Lay K.M size Sl
  apart : RcbApart K.S K.R K.E K.D
  c2 : sel ∉ rcbW K.S K.D
  c3 : sel + 8 * K.M.n ∉ rcbW K.S K.D
  sl : ∀ x ∈ (rcbW K.S K.D ++ rcbR K.S K.R K.E) ++ [sel, sel + 8 * K.M.n], Sl x
  head : readsOk (Impl.Weierstrass.X86_64.CachedJac.head K.M.n K.S K.R K.E sel)
    (jacCoords K.R ++ jacCoords K.E ++ [sel, sel + 8 * K.M.n]) = true
  tail : readsOk (jacTail K.S K.R K.E K.D) (validAfter
    (Impl.Weierstrass.X86_64.CachedJac.head K.M.n K.S K.R K.E sel)
    (jacCoords K.R ++ jacCoords K.E ++ [sel, sel + 8 * K.M.n])) = true
  dbl : readsOk (dblJMul K.S K.R K.D) (jacCoords K.R) = true
  accum : (jacCoords K.R).Nodup
  copy : ∀ x ∈ jacCoords K.D, ∀ y ∈ jacCoords K.R, x ≠ y


section
variable {K : WinCfg} {sel : Nat} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}

/-- The values the cached addition reads. -/
abbrev cV (K : WinCfg) (sel : Nat) : List Nat := jacCoords K.R ++ jacCoords K.E ++ [sel, sel + 8 * K.M.n]

theorem cV_rcbR {x : Nat} (hx : x ∈ jacCoords K.R ++ jacCoords K.E) : x ∈ cV K sel :=
  List.mem_append_left _ hx

/-- The header: `H` in `t3`, `r` in `t5`. -/
theorem cachedHead_val (hC : CachedLay K sel size Sl) (hm : UnitMod m (2 ^ (64 * K.M.n)))
    {E : Nat → Fin m} {s : State} (hI : Inv K.M base size m Sl (cV K sel) E s) :
    WP isa (ForwardField.programB K.M (Impl.Weierstrass.X86_64.CachedJac.head K.M.n K.S K.R K.E sel)).inline s
      fun t => ProgKeep K.M base (rcbW K.S K.D) s t ∧
      Inv K.M base size m Sl (validAfter (Impl.Weierstrass.X86_64.CachedJac.head K.M.n K.S K.R K.E sel) (cV K sel))
        (runOps (Impl.Weierstrass.X86_64.CachedJac.head K.M.n K.S K.R K.E sel) E) t ∧
      runOps (Impl.Weierstrass.X86_64.CachedJac.head K.M.n K.S K.R K.E sel) E K.S.t3 =
        E K.E.x * (E K.R.z * E K.R.z) - E K.R.x * E sel ∧
      runOps (Impl.Weierstrass.X86_64.CachedJac.head K.M.n K.S K.R K.E sel) E K.S.t5 =
        E K.E.y * E K.R.z * (E K.R.z * E K.R.z) - E K.R.y * E (sel + 8 * K.M.n) := by
  have hs : ∀ op ∈ Impl.Weierstrass.X86_64.CachedJac.head K.M.n K.S K.R K.E sel, ∀ x ∈ op.out :: op.ins, Sl x := by
    rw [head_eq K.M.n K.S K.R K.E K.D sel]
    exact fun op hop x hx => hC.sl x (slots op hop x hx)
  refine WP.mono (ForwardField.programB_ok hC.lay hm _ hI hs hC.head) fun t ⟨kt, it⟩ =>
    ⟨kt.mono ?_, it, ?_⟩
  · intro x hx
    obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hx
    rw [head_eq K.M.n K.S K.R K.E K.D sel] at hop
    exact out (show ∀ op ∈ headN, op.out < 9 by decide) hop
  · rw [head_eq K.M.n K.S K.R K.E K.D sel]
    have he := runOps_rename (rename K.M.n K.S K.R K.E K.D sel) headN E
      (fun op hop => rename_inj hC.apart hC.c2 hC.c3 ((show ∀ op ∈ headN, op.out < 9 by decide) op hop))
    have hv := headN_spec (fun i => E (rename K.M.n K.S K.R K.E K.D sel i))
    exact ⟨(congrFun he 3).trans hv.1, (congrFun he 5).trans hv.2⟩

/-- The tail, for `H ≠ 0`: `D` is the specification's `jacTail`. -/
theorem cachedTail_val (hC : CachedLay K sel size Sl) (hm : UnitMod m (2 ^ (64 * K.M.n)))
    {E : Nat → Fin m} {s : State}
    (hI : Inv K.M base size m Sl (validAfter (Impl.Weierstrass.X86_64.CachedJac.head K.M.n K.S K.R K.E sel) (cV K sel))
      (runOps (Impl.Weierstrass.X86_64.CachedJac.head K.M.n K.S K.R K.E sel) E) s) :
    WP isa (ForwardField.programB K.M (jacTail K.S K.R K.E K.D)).inline s
      (Val K.M base size m Sl (rcbW K.S K.D) (cV K sel) K.D
        (Spec.Weierstrass.PointOps.jacTail (E K.R.x * E sel) (E K.R.y * E (sel + 8 * K.M.n))
          (E K.E.x * (E K.R.z * E K.R.z) - E K.R.x * E sel)
          (E K.E.y * E K.R.z * (E K.R.z * E K.R.z) - E K.R.y * E (sel + 8 * K.M.n))
          (E K.R.z * E K.E.z)) s) := by
  have hs : ∀ op ∈ jacTail K.S K.R K.E K.D, ∀ x ∈ op.out :: op.ins, Sl x := by
    rw [tail_eq K.M.n K.S K.R K.E K.D sel]
    exact fun op hop x hx => hC.sl x (slots op hop x hx)
  refine WP.mono (ForwardField.programB_ok hC.lay hm _ hI hs hC.tail) fun t ⟨kt, it⟩ =>
    ⟨kt.mono ?_, _, it.sub ?_, ?_⟩
  · intro x hx
    obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hx
    rw [tail_eq K.M.n K.S K.R K.E K.D sel] at hop
    exact out (show ∀ op ∈ jacTailN, op.out < 9 by decide) hop
  · intro x hx
    rw [mem_validAfter, mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · right
      simp only [jacCoords, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [jacTail, FOp.out]
    · exact Or.inl (Or.inl hx)
  · rw [← runOps_append, head_eq K.M.n K.S K.R K.E K.D sel, tail_eq K.M.n K.S K.R K.E K.D sel,
      ← List.map_append]
    have he := runOps_rename (rename K.M.n K.S K.R K.E K.D sel) (headN ++ jacTailN) E
      (fun op hop => rename_inj hC.apart hC.c2 hC.c3
        ((show ∀ op ∈ headN ++ jacTailN, op.out < 9 by decide) op hop))
    exact (congrArg₂ Prod.mk (congrFun he 6) (congrArg₂ Prod.mk (congrFun he 7) (congrFun he 8))).trans
      (cachedN_spec (fun i => E (rename K.M.n K.S K.R K.E K.D sel i)))

end

/-- The doubling of `p` into `o` by `programB`: `o` is `jacDouble` of `p`'s
values. -/
theorem dblB_val {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}
    (hL : Lay M size Sl) (hm : UnitMod m (2 ^ (64 * M.n))) {S : RcbSlots} {p o : Pt}
    (hA : RcbApart S p p o) (hSl : ∀ x ∈ rcbW S o ++ rcbR S p p, Sl x)
    {V : List Nat} (hR : readsOk (dblJMul S p o) V = true)
    {E : Nat → Fin m} {s : State} (hI : Inv M base size m Sl V E s) :
    WP isa (ForwardField.programB M (dblJMul S p o)).inline s
      (Val M base size m Sl (rcbW S o) V o (Spec.Weierstrass.PointOps.jacDouble (E p.x) (E p.y) (E p.z)) s) := by
  have he : dblJMul S p o = ofN dblJMulN S p p o := rfl
  have hN : NumOk dblJMulN := dblJChoiceN_ok true
  refine WP.mono (ForwardField.programB_ok hL hm _ hI (fun op hop x hx => hSl x (by
    rw [he] at hop; exact ofN_slots op hop x hx)) hR) fun t ⟨kt, it⟩ => ⟨kt.mono ?_, _, it.sub ?_, ?_⟩
  · intro w hw
    obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw
    rw [he] at hop
    exact ofN_out hN op hop
  · intro x hx
    rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · right; rw [he]; exact ofN_out_mem hN (by simpa [jacCoords] using hx)
    · exact Or.inl hx
  · rw [he]
    exact (congrArg₂ Prod.mk (ofN_run hN hA E 6) (congrArg₂ Prod.mk (ofN_run hN hA E 7)
      (ofN_run hN hA E 8))).trans (dblJMulN_spec (fun y => E (rcbσ S p p o y)))

/-- The point at infinity `(0 : 1 : 0)` into `o`, for `one` standing for 1. -/
theorem infinity_val {K : WinCfg} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}
    (hL : Lay K.M size Sl) {o : Pt} (hSl : ∀ x ∈ jacCoords o, Sl x) (hW : ∀ x ∈ jacCoords o, x ∈ rcbW K.S o)
    (hn : (jacCoords o).Nodup)
    {V : List Nat} {E : Nat → Fin m} {s : State} (hI : Inv K.M base size m Sl V E s) (hOne : K.one < m)
    (hOneVal : toM m (2 ^ (64 * K.M.n)) K.one = 1) :
    WP isa (.block (Jacobian.infinity K o)) s (Val K.M base size m Sl (rcbW K.S o) V o (0, 1, 0) s) := by
  have hR := wordsVal_lt s.mem base K.M.mo K.M.n
  rw [hI.mod.val] at hR
  have h0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  simp only [jacCoords, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hn
  rw [Jacobian.infinity, List.append_assoc, WP.block_append_iff]
  refine WP.mono (setField_ok hL hI (hSl o.x (by simp [jacCoords])) h0 hR) fun a ⟨ka, ia⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (setField_ok hL ia (hSl o.y (by simp [jacCoords])) hOne hR) fun b ⟨kb, ib⟩ => ?_
  refine WP.mono (setField_ok hL ib (hSl o.z (by simp [jacCoords])) h0 hR) fun t ⟨kt, it⟩ => ?_
  refine ⟨(progKeep_of_op ka (hW _ (by simp [jacCoords]))).trans
    ((progKeep_of_op kb (hW _ (by simp [jacCoords]))).trans (progKeep_of_op kt (hW _ (by simp [jacCoords])))),
    _, it.sub ?_, ?_⟩
  · intro x hx
    simp only [jacCoords, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    grind
  · have z : toM m (2 ^ (64 * K.M.n)) 0 = 0 := by
      simp only [toM, Fin.ofNat_zero, Lean.Grind.Semiring.zero_mul]
    simp only [Function.update_self, Function.update_of_ne hn.1.1, Function.update_of_ne hn.1.2,
      Function.update_of_ne hn.2.1, z, hOneVal]

theorem Val.prefix {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} {W V : List Nat}
    {o : Pt} {r : Fin m × Fin m × Fin m} {s t u : State} {W' : List Nat} (hk : ProgKeep M base W' s t)
    (hW : ∀ w ∈ W', w ∈ W) (h : Val M base size m Sl W V o r t u) : Val M base size m Sl W V o r s u :=
  ⟨(hk.mono hW).trans h.1, h.2⟩

theorem Val.sub {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} {W V V' : List Nat}
    {o : Pt} {r : Fin m × Fin m × Fin m} {s t : State} (h : Val M base size m Sl W V o r s t)
    (hV : ∀ x ∈ V', x ∈ V) : Val M base size m Sl W V' o r s t :=
  ⟨h.1, h.2.elim fun E' ⟨i, e⟩ => ⟨E', i.sub fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ hx
    · exact List.mem_append_right _ (hV x hx), e⟩⟩

theorem Val.mono {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} {W W' V : List Nat}
    {o : Pt} {r : Fin m × Fin m × Fin m} {s t : State} (h : Val M base size m Sl W V o r s t)
    (hW : ∀ w ∈ W, w ∈ W') : Val M base size m Sl W' V o r s t :=
  ⟨h.1.mono hW, h.2⟩

/-- A copy of `q` into `o`. -/
theorem copy_val {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}
    (hL : Lay M size Sl) {q o : Pt} (hN : (jacCoords o).Nodup) (hqa : ∀ x ∈ jacCoords q, ∀ y ∈ jacCoords o, x ≠ y)
    (hO : ∀ x ∈ jacCoords o, Sl x) {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) (hV : ∀ x ∈ jacCoords q, x ∈ V) :
    WP isa (.block (copyPt M.n o q)) s (Val M base size m Sl (jacCoords o) V o (E q.x, E q.y, E q.z) s) :=
  WP.mono (copyPointFields_ok hL hN hqa hO hI hV) fun _ ⟨E', k, i, e⟩ => ⟨k, E', i, e⟩

section
variable {K : WinCfg} {sel : Nat} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}

/-- `D` coordinates, distinct slots written by the cached addition's
programs, apart from `R`'s and `E`'s. -/
structure CachedPts (K : WinCfg) (sel size : Nat) (Sl : Nat → Prop) : Prop where
  lay : CachedLay K sel size Sl
  dN : (jacCoords K.D).Nodup
  eD : ∀ x ∈ jacCoords K.E, ∀ y ∈ jacCoords K.D, x ≠ y
  rD : ∀ x ∈ jacCoords K.R, ∀ y ∈ jacCoords K.D, x ≠ y
  one : K.one < m
  oneVal : toM m (2 ^ (64 * K.M.n)) K.one = 1

/-- `CachedJac.add` into `D`: `jacAddCached` of the values it reads. -/
theorem cachedAdd_val (hC : CachedPts (m := m) K sel size Sl) (hm : UnitMod m (2 ^ (64 * K.M.n)))
    {E : Nat → Fin m} {s : State} (hI : Inv K.M base size m Sl (cV K sel) E s) :
    WP isa (Impl.Weierstrass.X86_64.CachedJac.add K K.R K.E K.D sel).inline s
      (Val K.M base size m Sl (rcbW K.S K.D) (cV K sel) K.D
        (Spec.Weierstrass.PointOps.jacAddCached (E K.R.x) (E K.R.y) (E K.R.z) (E K.E.x) (E K.E.y)
          (E K.E.z) (E sel) (E (sel + 8 * K.M.n))) s) := by
  have hL := hC.lay
  have dW : ∀ w ∈ jacCoords K.D, w ∈ rcbW K.S K.D := by
    intro w hw; simp only [jacCoords, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> simp [rcbW]
  have dSl : ∀ x ∈ jacCoords K.D, Sl x := fun x hx => hL.sl x (List.mem_append_left _
    (List.mem_append_left _ (dW x hx)))
  have rV : ∀ x ∈ jacCoords K.R, x ∈ cV K sel := fun x hx => by simp [cV, hx]
  have eV : ∀ x ∈ jacCoords K.E, x ∈ cV K sel := fun x hx => by simp [cV, hx]
  rw [Impl.Weierstrass.X86_64.CachedJac.add]
  simp only [Code.inline]
  apply fieldBranch_ok hL.lay hm hI (rV _ (by simp [jacCoords]))
  · intro a ia ka hz
    refine WP.mono (copy_val hL.lay hC.dN hC.eD dSl ia eV) fun t ht => ?_
    simp only [Spec.Weierstrass.PointOps.jacAddCached, hz, ↓reduceIte]
    exact (ht.mono dW).prefix ka (by simp)
  intro a ia ka hpz
  apply fieldBranch_ok hL.lay hm ia (eV _ (by simp [jacCoords]))
  · intro b ib kb hz
    refine WP.mono (copy_val hL.lay hC.dN hC.rD dSl ib rV) fun t ht => ?_
    simp only [Spec.Weierstrass.PointOps.jacAddCached, hpz, hz, ↓reduceIte]
    exact ((ht.mono dW).prefix kb (by simp)).prefix ka (by simp)
  intro b ib kb hqz
  apply WP.seq
  refine WP.mono (cachedHead_val hL hm ib) fun c ⟨kc, ic, eh, er⟩ => ?_
  have pre : ProgKeep K.M base (rcbW K.S K.D) s c :=
    ((ka.mono (by simp)).trans (kb.mono (by simp))).trans kc
  let EH := runOps (Impl.Weierstrass.X86_64.CachedJac.head K.M.n K.S K.R K.E sel) E
  have hro : ∀ x ∈ jacCoords K.R, EH x = E x := fun x hx =>
    CachedJac.head_readonly hL.apart E (by
      simp only [jacCoords, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [rcbR])
  have oldV : ∀ x ∈ cV K sel, x ∈ validAfter (Impl.Weierstrass.X86_64.CachedJac.head K.M.n K.S K.R K.E sel) (cV K sel) :=
    fun x hx => (mem_validAfter _ _).mpr (Or.inl hx)
  apply fieldBranch_ok hL.lay hm ic (a := K.S.t3) (by
    rw [mem_validAfter]; right; simp [Impl.Weierstrass.X86_64.CachedJac.head, FOp.out])
  · intro d id kd hH
    apply fieldBranch_ok hL.lay hm id (a := K.S.t5) (by
      rw [mem_validAfter]; right; simp [Impl.Weierstrass.X86_64.CachedJac.head, FOp.out])
    · intro e ie ke hr
      have hdA : RcbApart K.S K.R K.R K.D :=
        ⟨hL.apart.nodup, fun x hx => hL.apart.apart x (rcbR_self_mem _ _ _ hx)⟩
      have hdSl : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.R K.R, Sl x := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hL.sl x (List.mem_append_left _ (List.mem_append_left _ hx))
        · exact hL.sl x (List.mem_append_left _ (List.mem_append_right _ (rcbR_self_mem _ _ _ hx)))
      have hR' := readsOk_mono hL.dbl fun x hx => oldV x (rV x hx)
      refine WP.mono (dblB_val hL.lay hm hdA hdSl hR' ie) fun t ht => ?_
      have hs : Spec.Weierstrass.PointOps.jacAddCached (E K.R.x) (E K.R.y) (E K.R.z) (E K.E.x) (E K.E.y)
          (E K.E.z) (E sel) (E (sel + 8 * K.M.n)) =
          Spec.Weierstrass.PointOps.jacDouble (EH K.R.x) (EH K.R.y) (EH K.R.z) := by
        rw [eh] at hH
        rw [er] at hr
        rw [hro _ (by simp [jacCoords]), hro _ (by simp [jacCoords]), hro _ (by simp [jacCoords])]
        simp only [Spec.Weierstrass.PointOps.jacAddCached, Spec.Weierstrass.PointOps.jacEqual, hpz, hqz,
          ↓reduceIte]
        simp only [hH, hr, ↓reduceIte]
      rw [hs]
      exact (((ht.sub oldV).prefix ke (by simp)).prefix kd (by simp)).prefix pre (fun _ h => h)
    · intro e ie ke hr
      refine WP.mono (infinity_val hL.lay dSl dW hC.dN ie hC.one hC.oneVal) fun t ht => ?_
      have hs : Spec.Weierstrass.PointOps.jacAddCached (E K.R.x) (E K.R.y) (E K.R.z) (E K.E.x) (E K.E.y)
          (E K.E.z) (E sel) (E (sel + 8 * K.M.n)) = (0, 1, 0) := by
        rw [eh] at hH
        rw [er] at hr
        simp only [Spec.Weierstrass.PointOps.jacAddCached, Spec.Weierstrass.PointOps.jacEqual,
          Spec.Weierstrass.PointOps.infinity, hpz, hqz, ↓reduceIte]
        simp only [hH, hr, ↓reduceIte]
      rw [hs]
      exact (((ht.sub oldV).prefix ke (by simp)).prefix kd (by simp)).prefix pre (fun _ h => h)
  · intro d id kd hH
    refine WP.mono (cachedTail_val hL hm id) fun t ht => ?_
    have hs : Spec.Weierstrass.PointOps.jacAddCached (E K.R.x) (E K.R.y) (E K.R.z) (E K.E.x) (E K.E.y)
        (E K.E.z) (E sel) (E (sel + 8 * K.M.n)) =
        Spec.Weierstrass.PointOps.jacTail (E K.R.x * E sel) (E K.R.y * E (sel + 8 * K.M.n))
          (E K.E.x * (E K.R.z * E K.R.z) - E K.R.x * E sel)
          (E K.E.y * E K.R.z * (E K.R.z * E K.R.z) - E K.R.y * E (sel + 8 * K.M.n))
          (E K.R.z * E K.E.z) := by
      rw [eh] at hH
      simp only [Spec.Weierstrass.PointOps.jacAddCached, hpz, hqz, hH, ↓reduceIte]
    rw [hs]
    exact (ht.prefix kd (by simp)).prefix pre (fun _ h => h)

/-- The cached addition's body: `R` becomes `jacAddCached` of what it reads. -/
theorem addCachedBody_val (hC : CachedPts (m := m) K sel size Sl) (hm : UnitMod m (2 ^ (64 * K.M.n)))
    {E : Nat → Fin m} {s : State} (hI : Inv K.M base size m Sl (cV K sel) E s) :
    WP isa (PointOps.addCachedBody K sel).inline s fun t =>
      ProgKeep K.M base (rcbW K.S K.D ++ jacCoords K.R) s t ∧ ∃ E',
        Inv K.M base size m Sl (jacCoords K.R) E' t ∧ (E' K.R.x, E' K.R.y, E' K.R.z) =
          Spec.Weierstrass.PointOps.jacAddCached (E K.R.x) (E K.R.y) (E K.R.z) (E K.E.x) (E K.E.y)
            (E K.E.z) (E sel) (E (sel + 8 * K.M.n)) := by
  have hL := hC.lay
  rw [PointOps.addCachedBody]
  simp only [Code.inline]
  apply WP.seq
  refine WP.mono (cachedAdd_val hC hm hI) fun d ⟨kd, E', id, ed⟩ => ?_
  have rSl : ∀ x ∈ jacCoords K.R, Sl x := fun x hx => hL.sl x (List.mem_append_left _
    (List.mem_append_right _ (by
      simp only [jacCoords, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [rcbR])))
  refine WP.mono (copyPointFields_ok hL.lay hL.accum hL.copy rSl id (fun x hx => List.mem_append_left _ hx))
    fun t ⟨E'', kt, it, et⟩ => ⟨(kd.mono fun w hw => List.mem_append_left _ hw).trans
      (kt.mono fun w hw => List.mem_append_right _ hw), E'', it.sub fun x hx => List.mem_append_left _ hx,
      et.trans ed⟩

end
end VG.Proof.Weierstrass.X86_64.PointOps