module

public import VerifiedGarbage.Proof.Ecdsa.Arm.Window
public import VerifiedGarbage.Proof.Weierstrass.JacAdd
public import VerifiedGarbage.Proof.Ed25519.SlidingDigits
import VerifiedGarbage.Proof.Ecdsa.Arm.Lays
import VerifiedGarbage.Proof.Ecdsa.Arm.Flags
import VerifiedGarbage.Proof.Weierstrass.Arm.Window
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombCorrect
import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
import VerifiedGarbage.Proof.Weierstrass.Arm.Copy
import VerifiedGarbage.Proof.Weierstrass.Arm.Loop
import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
import VerifiedGarbage.Proof.Weierstrass.JacMadd
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# `[k]Q` for a public `k` on 32-bit ARM: correctness

`Cfg.pubBody` (`Impl/Ecdsa/Arm.lean`) leaves in `R` a representative of
`[k]Q`, as `Cfg.mulBody` does (`pubBody_ok`, with `mulBody_ok`'s statement),
for any curve the code supports (`CfgOk`) whose group law the proofs support
(`Law`):

* `ptRun_ok`: a field program of numbered operations that reads what an
  earlier one left in the temporaries, as the Jacobian addition's second
  half does (`jacTail`, after `jacHead` and the tests of its `H`);
* `pubAdd_ok`: the sum of two Jacobian points, by the Jacobian addition
  where neither is the point at infinity and their `x` differ
  (`InvJ.add_ne'`), else by the complete addition on their projective
  coordinates (`pubSlow_ok`);
* `pubTable_ok`: the table holds `[2e + 1]Q` for `e < 8` (`OddOk`);
* `pubStep_ok`: a digit takes a Jacobian triple of `[m]Q` to one of
  `[2m + d]Q`, so the digits from the top one down give `[k]Q`
  (`Slide.digits_sum`).

Each proof is split where the code branches on the number or the point: a
lemma for the code up to the branch states what holds there (`AddMid`,
`TblMid`, `TopMid`, `StepMid`, and the stages of `pubBody`, `PubS1` to
`PubS5`), which the constant-time proof (`PublicCT.lean`) takes for both of
two runs.
-/

-- separate module: the public multiplication's proofs cost more than their imports, and changes to
-- the stages of `Main.lean` and to the windows need not check them again

@[expose] public section

namespace VG.Proof.Ecdsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm
open VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.X25519.Arm (Rest Upd wp_mov wp_dp wp_cmp op2_imm op2_reg dpVal)
open VG.Proof.Ed25519

variable {c : Cfg}

/-! ## Field programs that read the temporaries -/

/-- Numbered slot `i` of a formula on the points `p`, `q` and `o` (`rcbσ`). -/
abbrev pσ (c : Cfg) (p q o : Nat × Nat × Nat) (i : Nat) : Nat :=
  rcbσ c.rcbSlots (c.pt p.1 p.2.1 p.2.2) (c.pt q.1 q.2.1 q.2.2) (c.pt o.1 o.2.1 o.2.2) i

/-- A field program of the numbered operations `N` (`ofN`) on the slots of
the points `p`, `q` and `o`, which reads only the numbered slots `V`, each
holding a number below `p`, and what it wrote: each of `V` and of the slots
it wrote holds, below `p`, what `N` computes. -/
theorem ptRun_ok (hc : CfgOk c) {N : List FOp} {V : List Nat} (hout : ∀ op ∈ N, op.out < 9)
    (hreads : readsOk N V = true) {p q o : Nat × Nat × Nat}
    (hnd : [T0, T1, T2, T3, T4, T5, o.1, o.2.1, o.2.2].Nodup)
    (hap : ∀ i ∈ [AP, B3P, p.1, p.2.1, p.2.2, q.1, q.2.1, q.2.2],
      i ∉ [T0, T1, T2, T3, T4, T5, o.1, o.2.1, o.2.2])
    (hin : ∀ i ∈ [p.1, p.2.1, p.2.2, q.1, q.2.1, q.2.2, o.1, o.2.1, o.2.2], i ∈ winIds)
    {s : State} {base : Addr} (hs : Scr s base size) (hf : Far s base 8192) (hM : sv c base s MP = c.C.p)
    (hlt : ∀ i ∈ V, wordsVal s.mem base (pσ c p q o i) c.n < c.C.p) :
    WP isa (fprog c.SP (ofN N c.rcbSlots (c.pt p.1 p.2.1 p.2.2) (c.pt q.1 q.2.1 q.2.2)
        (c.pt o.1 o.2.1 o.2.2)) c.umaal) s fun s' =>
      Rest Mont.callClob s s' ∧
      Unch base (pW c [T0, T1, T2, T3, T4, T5, o.1, o.2.1, o.2.2, TMP]) s.mem s'.mem ∧
      ∀ i, i ∈ V ∨ i ∈ N.map FOp.out →
        wordsVal s'.mem base (pσ c p q o i) c.n < c.C.p ∧
        tmv c.C c.n base s' (pσ c p q o i) = runOps N (fun y => tmv c.C c.n base s (pσ c p q o y)) i := by
  have hn := hc.n0
  obtain hA : RcbApart c.rcbSlots (c.pt p.1 p.2.1 p.2.2) (c.pt q.1 q.2.1 q.2.2) (c.pt o.1 o.2.1 o.2.2) :=
    rcbApart_of hn (lw := [T0, T1, T2, T3, T4, T5, o.1, o.2.1, o.2.2])
      (lr := [AP, B3P, p.1, p.2.1, p.2.2, q.1, q.2.1, q.2.2]) rfl rfl hnd hap
  obtain hids : ∀ i ∈ [T0, T1, T2, T3, T4, T5, o.1, o.2.1, o.2.2] ++
      [AP, B3P, p.1, p.2.1, p.2.2, q.1, q.2.1, q.2.2], i ∈ winIds := by
    intro i hi
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hi hin
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | h | h | h | rfl | rfl | h | h | h | h | h | h
    all_goals first | decide | exact hin i (by simp only [h, true_or, or_true])
  obtain hSl : ∀ x ∈ rcbW c.rcbSlots (c.pt o.1 o.2.1 o.2.2) ++
      rcbR c.rcbSlots (c.pt p.1 p.2.1 p.2.2) (c.pt q.1 q.2.1 q.2.2), winSl c x := by
    intro x hx
    have hx' : x ∈ ([T0, T1, T2, T3, T4, T5, o.1, o.2.1, o.2.2] ++
        [AP, B3P, p.1, p.2.1, p.2.2, q.1, q.2.1, q.2.2]).map c.sl := hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    exact List.mem_map_of_mem (hids i hi)
  obtain I : Inv c.MP' base size c.C.p (winSl c) (V.map (pσ c p q o)) (tmv c.C c.n base s) s :=
    ⟨hs, modP_of hc hM, fun x hx => by
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
        exact hSl _ (rcbσ_mem ..),
      fun x hx => by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
        exact hlt i hi, fun _ _ => rfl, hf⟩
  refine WP.mono (fprog_ok (winLay hc) (winWk hc) hc.fp (unitMod_pow_two hc.p_odd (64 * c.n)) _ I
    (fun op hop x hx => hSl x (ofN_slots op hop x hx)) (readsOk_rename _ hreads)) fun s' ⟨hk, I'⟩ => ?_
  have houtW : ∀ op ∈ ofN N c.rcbSlots (c.pt p.1 p.2.1 p.2.2) (c.pt q.1 q.2.1 q.2.2) (c.pt o.1 o.2.1 o.2.2),
      op.out ∈ rcbW c.rcbSlots (c.pt o.1 o.2.1 o.2.2) := by
    intro op hop
    rw [ofN, List.mem_map] at hop
    obtain ⟨op', h', rfl⟩ := hop
    rw [FOp.out_rename]
    exact rcbσ_out _ _ _ _ (hout op' h')
  refine ⟨hk.rest, ?_, fun i hi => ?_⟩
  · obtain hk' : ProgKeep c.MP' base c.wk (rcbW c.rcbSlots (c.pt o.1 o.2.1 o.2.2)) s s' :=
      hk.mono fun w hw => by
        obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw
        exact houtW op hop
    refine hk'.unch.mono fun w hw => ?_
    have hw' : w ∈ ([T0, T1, T2, T3, T4, T5, o.1, o.2.1, o.2.2].map c.sl).map (·, 8 * c.n) ++
        [(c.sl TMP, 8 * c.n), (c.wk, 64 * c.n)] := hw
    simp only [pW, slW, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hw' ⊢
    rcases hw' with h | h | h | h | h | h | h | h | h | h | h <;> simp only [h, true_or, or_true]
  · have hval : pσ c p q o i ∈ validAfter (ofN N c.rcbSlots (c.pt p.1 p.2.1 p.2.2) (c.pt q.1 q.2.1 q.2.2)
        (c.pt o.1 o.2.1 o.2.2)) (V.map (pσ c p q o)) := by
      rw [mem_validAfter]
      rcases hi with h | h
      · exact Or.inl (List.mem_map_of_mem h)
      · refine Or.inr ?_
        rw [ofN, List.map_map]
        obtain ⟨op, hop, rfl⟩ := List.mem_map.mp h
        exact List.mem_map.mpr ⟨op, hop, by rw [Function.comp_apply, FOp.out_rename]⟩
    refine ⟨I'.lt _ hval, (I'.val _ hval).trans ?_⟩
    have key := runOps_rename (pσ c p q o) N (tmv c.C c.n base s) fun op hop => hA.inj (hout op hop)
    exact congrFun key i

/-! ## The Jacobian addition's second half -/

section
variable {F : Type _} [Lean.Grind.CommRing F]

/-- What `jacTail` computes of `jacHead`'s `U₁`, `H`, `S₁` and `r`, and of the
two `Z`. -/
def jacTailF (u1 h s1 r Z1 Z2 : F) : F × F × F :=
  let hh := h * h
  let hhh := hh * h
  let v := u1 * hh
  let x := r * r - hhh - v - v
  (x, r * (v - x) - s1 * hhh, Z1 * Z2 * h)

theorem jacTailN_run (e : Nat → F) :
    (runOps jacTailN e 6, runOps jacTailN e 7, runOps jacTailN e 8) =
      jacTailF (e 2) (e 3) (e 4) (e 5) (e 13) (e 16) := rfl

/-- The Jacobian addition is `jacTail` after `jacHead`. -/
theorem jacAddF_eq_tail (X1 Y1 Z1 X2 Y2 Z2 : F) : jacAddF X1 Y1 Z1 X2 Y2 Z2 =
    jacTailF (X1 * (Z2 * Z2)) (X2 * (Z1 * Z1) - X1 * (Z2 * Z2)) (Y1 * Z2 * (Z2 * Z2))
      (Y2 * Z1 * (Z1 * Z1) - Y1 * Z2 * (Z2 * Z2)) Z1 Z2 := rfl

end

/-! ## A Jacobian point in projective coordinates -/

/-- `pubFixY`: `Y` is one where `Z` is zero. -/
theorem pubFixY_ok (hc : CfgOk c) {s : State} {base : Addr} (hs : Scr s base size) {x y z : Nat}
    (hy : y < 45) (hz : z < 45) (hy1 : ONEP < y) :
    WP isa (.block (c.pubFixY (c.pt x y z))) s fun s' =>
      sv c base s' y = (if sv c base s z ≠ 0 then sv c base s y else sv c base s ONEP) ∧
      Rest [.r4, .r5, .r10] s s' ∧ Unch base (slW c [y]) s.mem s'.mem := by
  have h7 := hc.n10
  have hn := hs.nowrap
  rw [Cfg.pubFixY, List.append_assoc]
  refine VG.Proof.X25519.Arm.WP.append (nonzero_ok c hs hc.n0 (sl_le c h7 hz)) fun s₁ ⟨g₁, k₁, m₁⟩ => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_reg _ _) fun s₂ u₂ => ?_
  obtain k₂ : Rest [.r4, .r5, .r10] s s₂ := (k₁.mono (by simp)).trans (u₂.rest (by simp))
  obtain m₂ : s₂.mem = s.mem := by rw [u₂.mem, m₁]
  have hY := sl_le c h7 hy
  have hONE := sl_le c h7 (i := ONEP) (by decide)
  have h15 := sl_lt c (i := ONEP) (j := y) hy1
  refine WP.mono (sel_ok (decide (sv c base s z ≠ 0)) (2 * c.n) (hs.of_rest k₂ (by decide))
    (by rw [u₂.gpr, g₁]; simp only [mask32, decide_eq_true_eq]; rfl) (o := c.sl y) (a := c.sl ONEP)
    (b := c.sl y) (by omega_using [hY]) (by omega_using [hONE]) (by omega_using [hY])
    (Or.inr (by omega_using [h15])) (Or.inl (Nat.le_refl _))) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  rw [show 4 * (2 * c.n) = 8 * c.n by omega_using []] at O₃
  rw [← wordsVal_eq_val32, ← wordsVal_eq_val32, ← wordsVal_eq_val32, m₂] at e₃
  refine ⟨e₃.trans (by simp only [decide_eq_true_eq]), k₂.trans (k₃.mono (by simp)), ?_⟩
  rw [← m₂]
  exact O₃.unch.mono fun w hw => by rw [List.mem_singleton.mp hw]; exact List.mem_cons_self

/-- The numbers `fromJ` and `pubFixY` leave of a Jacobian triple of `Q`
represent `Q`. -/
theorem rep_fromJ_fix (hc : CfgOk c) (hC : Law c.C) {X Y Z : Fe c.C} {Q : Point c.C} (J : InvJ c.C X Y Z Q)
    {x y z one : Nat} (hz : z < c.C.p) (ex : toM c.C.p (2 ^ (64 * c.n)) x = X * Z)
    (ey : toM c.C.p (2 ^ (64 * c.n)) y = Y) (ez : toM c.C.p (2 ^ (64 * c.n)) z = Z * Z * Z)
    (e1 : toM c.C.p (2 ^ (64 * c.n)) one = 1) :
    Rep c.C (toM c.C.p (2 ^ (64 * c.n)) x) (toM c.C.p (2 ^ (64 * c.n)) (if z ≠ 0 then y else one))
      (toM c.C.p (2 ^ (64 * c.n)) z) Q := by
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  obtain hz0 : z = 0 ↔ Z = 0 := by
    rw [← toM_eq_zero_iff hpR hz, ez]
    constructor
    · intro h; by_contra hZ; exact cube_ne_zero hC hZ h
    · intro h; rw [h]; grind
  have hout := J.out hC
  rw [ex, ez]
  by_cases h : Z = 0
  · have hz' : ¬z ≠ 0 := by rw [ne_eq, not_not]; exact hz0.mpr h
    rw [ite_eq_right hz', e1]
    rw [ite_eq_left h] at hout
    exact hout
  · rw [ite_eq_left (fun e => h (hz0.mp e)), ey]
    rw [ite_eq_right h] at hout
    exact hout

/-- Code that keeps `r12` and the memory keeps the working space and the
constants. -/
theorem CoreCtx.same {base : Addr} {s s' : State} (h : CoreCtx c base s) (hc : CfgOk c)
    {rs : List Reg} (hr : Rest rs s s') (h12 : .r12 ∉ rs) (hm : s'.mem = s.mem) : CoreCtx c base s' :=
  h.next hc hr h12 (W := []) (by rw [hm]; exact Unch.refl _ _ _) (fun _ h => nomatch h)

/-- A store past the working space keeps the working space and the
constants. -/
theorem CoreCtx.far_store {base : Addr} {s s' : State} (h : CoreCtx c base s) (hc : CfgOk c)
    {rs : List Reg} (hr : Rest rs s s') (h12 : .r12 ∉ rs) {o n : Nat}
    (hu : Unch base [(o, n)] s.mem s'.mem) (ho : size ≤ o) : CoreCtx c base s' := by
  have h7 := hc.n10
  have hn := h.scr.nowrap
  have e : ∀ i, i < 12 → sv c base s' i = sv c base s i := fun i hi =>
    sv_unch hu h7 hn (by omega_using [hi]) fun w hw => by
      rw [List.mem_singleton.mp hw]
      exact Or.inl (Nat.le_trans (sl_le c h7 (by omega_using [hi])) ho)
  exact ⟨h.scr.of_rest hr h12, h.far.of_rest hr, (e MP (by decide)).trans h.mp,
    (e AP (by decide)).trans h.ap, (e B3P (by decide)).trans h.b3p,
    (e ZERO (by decide)).trans h.zero, (e ONEP (by decide)).trans h.onep⟩

/-! ## The sum of two Jacobian points -/

/-- The sum's two points: `R` and `D`. -/
def ppt : Bool → Nat × Nat × Nat
  | true => (RX, RY, RZ)
  | false => (DX, DY, DZ)

theorem mem3₁ {α : Type} {a b d : α} : a ∈ [a, b, d] := List.mem_cons_self
theorem mem3₂ {α : Type} {a b d : α} : b ∈ [a, b, d] := List.mem_cons_of_mem _ List.mem_cons_self
theorem mem3₃ {α : Type} {a b d : α} : d ∈ [a, b, d] :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- `pubSlow`: the sum of the Jacobian points in `R` or `D` (`b`) and in `T`,
in the other of `R` and `D`, by the complete addition, whatever the points. -/
theorem pubSlow_ok (hc : CfgOk c) (hC : Law c.C) {base : Addr} {s : State} (ctx : CoreCtx c base s) (b : Bool)
    {A B : Point c.C} (hA : onCurve c.C A = true) (hB : onCurve c.C B = true)
    (hp : ∀ i ∈ [(ppt b).1, (ppt b).2.1, (ppt b).2.2], sv c base s i < c.C.p)
    (hq : ∀ i ∈ [TX, TY, TZ], sv c base s i < c.C.p)
    (JA : InvJ c.C (fv c base s (ppt b).1) (fv c base s (ppt b).2.1) (fv c base s (ppt b).2.2) A)
    (JB : InvJ c.C (fv c base s TX) (fv c base s TY) (fv c base s TZ) B) :
    WP isa (c.pubSlow (c.pt (ppt b).1 (ppt b).2.1 (ppt b).2.2) (c.pt TX TY TZ)
        (c.pt (ppt !b).1 (ppt !b).2.1 (ppt !b).2.2)) s fun s' =>
      Rest Mont.callClob s s' ∧ Unch base (pW c winWr) s.mem s'.mem ∧
      (∀ i ∈ [(ppt !b).1, (ppt !b).2.1, (ppt !b).2.2], sv c base s' i < c.C.p) ∧
      InvJ c.C (fv c base s' (ppt !b).1) (fv c base s' (ppt !b).2.1) (fv c base s' (ppt !b).2.2)
        (Spec.Weierstrass.add A B) := by
  have h7 := hc.n10
  have hn := ctx.scr.nowrap
  have hO45 : ∀ i ∈ [(ppt !b).1, (ppt !b).2.1, (ppt !b).2.2], i < 45 := by cases b <;> decide
  have hP45 : ∀ i ∈ [(ppt b).1, (ppt b).2.1, (ppt b).2.2], i < 45 := by cases b <;> decide
  have hT45 : ∀ i ∈ [TX, TY, TZ], i < 45 := by decide
  rw [Cfg.pubSlow, fromJ_eq, fromJ_eq, toJ_eq]
  -- `p` in projective coordinates, in `o`.
  refine WP.seq (WP.mono (ptOp_ok hc fromJN_ok (q₁ := ZERO) (q₂ := ZERO) (q₃ := ZERO)
    (o₁ := (ppt !b).1) (o₂ := (ppt !b).2.1) (o₃ := (ppt !b).2.2) (by cases b <;> decide)
    (by cases b <;> decide) (by cases b <;> decide) ctx.scr ctx.far ctx.mp
    (ctx.lt8 hc hp (ctx.lt_zero hc))) fun s₁ ⟨K₁, U₁, L₁, V₁⟩ => ?_)
  obtain ctx₁ := ctx.next hc K₁ (by decide) U₁ (winW_pW h7 (by cases b <;> decide))
  obtain V₁' := V₁.trans (fromJN_run _)
  simp only [Prod.mk.injEq] at V₁'
  obtain ⟨vx₁, vy₁, vz₁⟩ := V₁'
  obtain vy₁ : fv c base s₁ (ppt !b).2.1 = fv c base s (ppt b).2.1 := vy₁.trans (by
    show fv c base s (ppt b).2.1 + fv c base s ZERO = _
    rw [ctx.fv_zero]; grind)
  have eT₁ : ∀ i ∈ [TX, TY, TZ], sv c base s₁ i = sv c base s i := fun i hi =>
    sv_pW U₁ h7 hn (hT45 i hi)
      ((by cases b <;> decide : ∀ i ∈ [TX, TY, TZ],
        i ∉ [T0, T1, T2, T3, T4, T5, (ppt !b).1, (ppt !b).2.1, (ppt !b).2.2, TMP]) i hi)
  -- `Y = 1` where `Z = 0`.
  refine WP.seq (WP.mono (pubFixY_ok hc ctx₁.scr (x := (ppt !b).1) (y := (ppt !b).2.1) (z := (ppt !b).2.2)
    (by cases b <;> decide) (by cases b <;> decide) (by cases b <;> decide)) fun s₂ ⟨ey₂, k₂, U₂⟩ => ?_)
  obtain ctx₂ := ctx₁.next hc k₂ (by decide) U₂ (winW_slW h7 (by cases b <;> decide))
  have o₂ : ∀ i, i < 45 → i ≠ (ppt !b).2.1 → sv c base s₂ i = sv c base s₁ i := fun i hi hne =>
    sv_unch (c := c) U₂ h7 hn hi (apart_slW (l := [(ppt !b).2.1]) (by simpa using hne))
  obtain repO₂ : Rep c.C (fv c base s₂ (ppt !b).1) (fv c base s₂ (ppt !b).2.1) (fv c base s₂ (ppt !b).2.2) A := by
    have := rep_fromJ_fix hc hC JA (x := sv c base s₁ (ppt !b).1) (y := sv c base s₁ (ppt !b).2.1)
      (z := sv c base s₁ (ppt !b).2.2) (one := sv c base s₁ ONEP) (L₁ _ mem3₃) vx₁ vy₁ vz₁ (ctx₁.fv_onep hc)
    show Rep _ (toM _ _ (sv c base s₂ _)) (toM _ _ (sv c base s₂ _)) (toM _ _ (sv c base s₂ _)) _
    rw [o₂ _ (hO45 _ mem3₁) (by cases b <;> decide), ey₂, o₂ _ (hO45 _ mem3₃) (by cases b <;> decide)]
    exact this
  have ltO₂ : ∀ i ∈ [(ppt !b).1, (ppt !b).2.1, (ppt !b).2.2], sv c base s₂ i < c.C.p := by
    intro i hi
    by_cases h : i = (ppt !b).2.1
    · subst h
      rw [ey₂]; split
      · exact L₁ _ mem3₂
      · exact ctx₁.lt hc _ (by decide)
    · rw [o₂ i (hO45 i hi) h]; exact L₁ i hi
  have eT₂ : ∀ i ∈ [TX, TY, TZ], sv c base s₂ i = sv c base s i := fun i hi => by
    rw [o₂ i (hT45 i hi) ((by cases b <;> decide : ∀ i ∈ [TX, TY, TZ], i ≠ (ppt !b).2.1) i hi), eT₁ i hi]
  -- `q` in projective coordinates, in `p`.
  refine WP.seq (WP.mono (ptOp_ok hc fromJN_ok (p₁ := TX) (p₂ := TY) (p₃ := TZ) (q₁ := ZERO) (q₂ := ZERO)
    (q₃ := ZERO) (o₁ := (ppt b).1) (o₂ := (ppt b).2.1) (o₃ := (ppt b).2.2) (by cases b <;> decide)
    (by cases b <;> decide) (by cases b <;> decide) ctx₂.scr ctx₂.far ctx₂.mp
    (ctx₂.lt8 hc (fun i hi => by rw [eT₂ i hi]; exact hq i hi) (ctx₂.lt_zero hc)))
    fun s₃ ⟨K₃, U₃, L₃, V₃⟩ => ?_)
  obtain ctx₃ := ctx₂.next hc K₃ (by decide) U₃ (winW_pW h7 (by cases b <;> decide))
  obtain V₃' := V₃.trans (fromJN_run _)
  simp only [Prod.mk.injEq] at V₃'
  obtain ⟨vx₃, vy₃, vz₃⟩ := V₃'
  obtain vy₃ : fv c base s₃ (ppt b).2.1 = fv c base s₂ TY := vy₃.trans (by
    show fv c base s₂ TY + fv c base s₂ ZERO = _
    rw [ctx₂.fv_zero]; grind)
  have eO₃ : ∀ i ∈ [(ppt !b).1, (ppt !b).2.1, (ppt !b).2.2], sv c base s₃ i = sv c base s₂ i := fun i hi =>
    sv_pW U₃ h7 hn (hO45 i hi)
      ((by cases b <;> decide : ∀ i ∈ [(ppt !b).1, (ppt !b).2.1, (ppt !b).2.2],
        i ∉ [T0, T1, T2, T3, T4, T5, (ppt b).1, (ppt b).2.1, (ppt b).2.2, TMP]) i hi)
  obtain JB₂ : InvJ c.C (fv c base s₂ TX) (fv c base s₂ TY) (fv c base s₂ TZ) B := by
    show InvJ _ (toM _ _ (sv c base s₂ TX)) (toM _ _ (sv c base s₂ TY)) (toM _ _ (sv c base s₂ TZ)) _
    rw [eT₂ _ mem3₁, eT₂ _ mem3₂, eT₂ _ mem3₃]; exact JB
  -- `Y = 1` where `Z = 0`.
  refine WP.seq (WP.mono (pubFixY_ok hc ctx₃.scr (x := (ppt b).1) (y := (ppt b).2.1) (z := (ppt b).2.2)
    (by cases b <;> decide) (by cases b <;> decide) (by cases b <;> decide)) fun s₄ ⟨ey₄, k₄, U₄⟩ => ?_)
  obtain ctx₄ := ctx₃.next hc k₄ (by decide) U₄ (winW_slW h7 (by cases b <;> decide))
  have o₄ : ∀ i, i < 45 → i ≠ (ppt b).2.1 → sv c base s₄ i = sv c base s₃ i := fun i hi hne =>
    sv_unch (c := c) U₄ h7 hn hi (apart_slW (l := [(ppt b).2.1]) (by simpa using hne))
  obtain repP₄ : Rep c.C (fv c base s₄ (ppt b).1) (fv c base s₄ (ppt b).2.1) (fv c base s₄ (ppt b).2.2) B := by
    have := rep_fromJ_fix hc hC JB₂ (x := sv c base s₃ (ppt b).1) (y := sv c base s₃ (ppt b).2.1)
      (z := sv c base s₃ (ppt b).2.2) (one := sv c base s₃ ONEP) (L₃ _ mem3₃) vx₃ vy₃ vz₃ (ctx₃.fv_onep hc)
    show Rep _ (toM _ _ (sv c base s₄ _)) (toM _ _ (sv c base s₄ _)) (toM _ _ (sv c base s₄ _)) _
    rw [o₄ _ (hP45 _ mem3₁) (by cases b <;> decide), ey₄, o₄ _ (hP45 _ mem3₃) (by cases b <;> decide)]
    exact this
  have ltP₄ : ∀ i ∈ [(ppt b).1, (ppt b).2.1, (ppt b).2.2], sv c base s₄ i < c.C.p := by
    intro i hi
    by_cases h : i = (ppt b).2.1
    · subst h
      rw [ey₄]; split
      · exact L₃ _ mem3₂
      · exact ctx₃.lt hc _ (by decide)
    · rw [o₄ i (hP45 i hi) h]; exact L₃ i hi
  have eO₄ : ∀ i ∈ [(ppt !b).1, (ppt !b).2.1, (ppt !b).2.2], sv c base s₄ i = sv c base s₂ i := fun i hi => by
    rw [o₄ i (hO45 i hi) ((by cases b <;> decide : ∀ i ∈ [(ppt !b).1, (ppt !b).2.1, (ppt !b).2.2],
      i ≠ (ppt b).2.1) i hi), eO₃ i hi]
  obtain repO₄ : Rep c.C (fv c base s₄ (ppt !b).1) (fv c base s₄ (ppt !b).2.1) (fv c base s₄ (ppt !b).2.2) A := by
    show Rep _ (toM _ _ (sv c base s₄ _)) (toM _ _ (sv c base s₄ _)) (toM _ _ (sv c base s₄ _)) _
    rw [eO₄ _ mem3₁, eO₄ _ mem3₂, eO₄ _ mem3₃]; exact repO₂
  -- Their sum, in `q`.
  obtain ⟨N, hN, eN, hadd⟩ := winAdd_ok (c := c) hC
  rw [eN]
  refine WP.seq (WP.mono (ptOp_ok hc hN (p₁ := (ppt !b).1) (p₂ := (ppt !b).2.1) (p₃ := (ppt !b).2.2)
    (q₁ := (ppt b).1) (q₂ := (ppt b).2.1) (q₃ := (ppt b).2.2) (o₁ := TX) (o₂ := TY) (o₃ := TZ)
    (by decide) (by cases b <;> decide) (by cases b <;> decide) ctx₄.scr ctx₄.far ctx₄.mp
    (ctx₄.lt8 hc (fun i hi => by rw [eO₄ i hi]; exact ltO₂ i hi) ltP₄)) fun s₅ ⟨K₅, U₅, L₅, V₅⟩ => ?_)
  obtain ctx₅ := ctx₄.next hc K₅ (by decide) U₅ (winW_pW h7 (by decide))
  obtain repT₅ : Rep c.C (fv c base s₅ TX) (fv c base s₅ TY) (fv c base s₅ TZ) (Spec.Weierstrass.add A B) := by
    have := hadd (fun y => tmv c.C c.n base s₄ (rcbσ c.rcbSlots (c.pt (ppt !b).1 (ppt !b).2.1 (ppt !b).2.2)
      (c.pt (ppt b).1 (ppt b).2.1 (ppt b).2.2) (c.pt TX TY TZ) y)) hA hB (ctx₄.fv_ap hc) (ctx₄.fv_b3p hc)
      nofun repO₄ repP₄
    simp only [Prod.mk.injEq] at V₅
    rw [V₅.1, V₅.2.1, V₅.2.2]; exact this
  -- In Jacobian coordinates, in `o`.
  refine WP.mono (ptOp_ok hc toJN_ok (p₁ := TX) (p₂ := TY) (p₃ := TZ) (q₁ := ZERO) (q₂ := ZERO) (q₃ := ZERO)
    (o₁ := (ppt !b).1) (o₂ := (ppt !b).2.1) (o₃ := (ppt !b).2.2) (by cases b <;> decide)
    (by cases b <;> decide) (by cases b <;> decide) ctx₅.scr ctx₅.far ctx₅.mp
    (ctx₅.lt8 hc L₅ (ctx₅.lt_zero hc))) fun s₆ ⟨K₆, U₆, L₆, V₆⟩ => ?_
  refine ⟨((((K₁.trans (k₂.mono (by decide))).trans K₃).trans (k₄.mono (by decide))).trans K₅).trans K₆, ?_, L₆,
    InvJ.of_toJ hC repT₅ ctx₅.fv_zero (V₆.trans (toJN_run _))⟩
  exact unch_winWr_trans (unch_winWr_pW (by cases b <;> decide) U₁) (unch_winWr_trans
    (unch_winWr_slW (by cases b <;> decide) U₂) (unch_winWr_trans (unch_winWr_pW (by cases b <;> decide) U₃)
    (unch_winWr_trans (unch_winWr_slW (by cases b <;> decide) U₄) (unch_winWr_trans
    (unch_winWr_pW (by decide) U₅) (unch_winWr_pW (by cases b <;> decide) U₆)))))

/-- A mask is zero unless its condition holds. -/
theorem mask32_sub_zero (p : Prop) [Decidable p] : (mask32 p - 0#32 == 0#32) = !decide p := by
  by_cases h : p <;> simp only [mask32, h, ite_true, ite_false] <;> decide

/-- After `pubAddHead` from `s`, on the points in `R` or `D` (`b`) and in `T`:
the working space and the two points kept, what `jacHead` computes below
`p`, and `Z` clear if `H` and the two `Z` are all nonzero. -/
structure AddMid (c : Cfg) (base : Addr) (b : Bool) (s s' : State) : Prop where
  ctx : CoreCtx c base s'
  keep : Rest Mont.callClob s s'
  unch : Unch base (pW c winWr) s.mem s'.mem
  vals : ∀ i, i ∈ [11, 12, 13, 14, 15, 16] ∨ i ∈ jacHeadN.map FOp.out →
    wordsVal s'.mem base (pσ c (ppt b) (TX, TY, TZ) (ppt !b) i) c.n < c.C.p ∧
    tmv c.C c.n base s' (pσ c (ppt b) (TX, TY, TZ) (ppt !b) i) =
      runOps jacHeadN (fun y => tmv c.C c.n base s (pσ c (ppt b) (TX, TY, TZ) (ppt !b) y)) i
  eP : ∀ i ∈ [(ppt b).1, (ppt b).2.1, (ppt b).2.2], sv c base s' i = sv c base s i
  eT : ∀ i ∈ [TX, TY, TZ], sv c base s' i = sv c base s i
  z : s'.z = !decide ((sv c base s' T3 ≠ 0 ∧ sv c base s' (ppt b).2.2 ≠ 0) ∧ sv c base s' TZ ≠ 0)

/-- `pubAddHead`: `jacHead`, and the test of its `H` and of the two `Z`. -/
theorem pubAddHead_ok (hc : CfgOk c) {base : Addr} {s : State} (ctx : CoreCtx c base s) (b : Bool)
    (hp : ∀ i ∈ [(ppt b).1, (ppt b).2.1, (ppt b).2.2], sv c base s i < c.C.p)
    (hq : ∀ i ∈ [TX, TY, TZ], sv c base s i < c.C.p) :
    WP isa (c.pubAddHead (c.pt (ppt b).1 (ppt b).2.1 (ppt b).2.2) (c.pt TX TY TZ)) s (AddMid c base b s) := by
  have h7 := hc.n10
  have hn := ctx.scr.nowrap
  have hP45 : ∀ i ∈ [(ppt b).1, (ppt b).2.1, (ppt b).2.2], i < 45 := by cases b <;> decide
  have hT45 : ∀ i ∈ [TX, TY, TZ], i < 45 := by decide
  rw [Cfg.pubAddHead, jacHead_eq c.rcbSlots _ _ (c.pt (ppt !b).1 (ppt !b).2.1 (ppt !b).2.2)]
  have hV : ∀ i ∈ [11, 12, 13, 14, 15, 16],
      wordsVal s.mem base (pσ c (ppt b) (TX, TY, TZ) (ppt !b) i) c.n < c.C.p := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hp _ mem3₁, hp _ mem3₂, hp _ mem3₃, hq _ mem3₁, hq _ mem3₂, hq _ mem3₃]
  -- `U₁`, `H`, `S₁` and `r`.
  refine WP.seq (WP.mono (ptRun_ok hc (N := jacHeadN) (V := [11, 12, 13, 14, 15, 16]) (by decide) (by decide)
    (p := ppt b) (q := (TX, TY, TZ)) (o := ppt !b) (by cases b <;> decide) (by cases b <;> decide)
    (by cases b <;> decide) ctx.scr ctx.far ctx.mp hV) fun s₁ ⟨K₁, U₁, R₁⟩ => ?_)
  obtain ctx₁ := ctx.next hc K₁ (by decide) U₁ (winW_pW h7 (by cases b <;> decide))
  have eP₁ : ∀ i ∈ [(ppt b).1, (ppt b).2.1, (ppt b).2.2], sv c base s₁ i = sv c base s i := fun i hi =>
    sv_pW U₁ h7 hn (hP45 i hi)
      ((by cases b <;> decide : ∀ i ∈ [(ppt b).1, (ppt b).2.1, (ppt b).2.2],
        i ∉ [T0, T1, T2, T3, T4, T5, (ppt !b).1, (ppt !b).2.1, (ppt !b).2.2, TMP]) i hi)
  have eT₁ : ∀ i ∈ [TX, TY, TZ], sv c base s₁ i = sv c base s i := fun i hi =>
    sv_pW U₁ h7 hn (hT45 i hi)
      ((by cases b <;> decide : ∀ i ∈ [TX, TY, TZ],
        i ∉ [T0, T1, T2, T3, T4, T5, (ppt !b).1, (ppt !b).2.1, (ppt !b).2.2, TMP]) i hi)
  -- Whether `H` and the two `Z` are all nonzero.
  simp only [List.append_assoc]
  refine VG.Proof.X25519.Arm.WP.append (nonzero_ok c ctx₁.scr hc.n0 (sl_le c h7 (i := T3) (by decide)))
    fun s₂ ⟨g₂, k₂, m₂⟩ => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => ?_
  have k₃ : Rest [.r4, .r5, .r7] s₁ s₃ := (k₂.mono (by simp)).trans (u₃.rest (by simp))
  have m₃ : s₃.mem = s₁.mem := by rw [u₃.mem, m₂]
  refine VG.Proof.X25519.Arm.WP.append (nonzero_ok c (ctx₁.scr.of_rest k₃ (by decide)) hc.n0
    (sl_le c h7 (i := (ppt b).2.2) (hP45 _ mem3₃))) fun s₄ ⟨g₄, k₄, m₄⟩ => ?_
  refine wp_dp (op2_reg _ _) fun s₅ u₅ => ?_
  have k₅ : Rest [.r4, .r5, .r7] s₁ s₅ := (k₃.trans (k₄.mono (by simp))).trans (u₅.rest (by simp))
  have m₅ : s₅.mem = s₁.mem := by rw [u₅.mem, m₄, m₃]
  refine VG.Proof.X25519.Arm.WP.append (nonzero_ok c (ctx₁.scr.of_rest k₅ (by decide)) hc.n0
    (sl_le c h7 (i := TZ) (by decide))) fun s₆ ⟨g₆, k₆, m₆⟩ => ?_
  refine wp_dp (op2_reg _ _) fun s₇ u₇ => wp_cmp (op2_imm (by decide)) fun s₈ f₈ z₈ => WP.block_nil ?_
  have k₈ : Rest [.r4, .r5, .r7] s₁ s₈ := ((k₅.trans (k₆.mono (by simp))).trans (u₇.rest (by simp))).trans
    (f₈.rest _)
  have m₈ : s₈.mem = s₁.mem := by rw [f₈.mem, u₇.mem, m₆, m₅]
  have hz : s₈.z = !decide ((sv c base s₁ T3 ≠ 0 ∧ sv c base s₁ (ppt b).2.2 ≠ 0) ∧ sv c base s₁ TZ ≠ 0) := by
    rw [z₈, u₇.gpr, dpVal, g₆, k₆.gpr .r7 (by decide), u₅.gpr, dpVal, g₄, k₄.gpr .r7 (by decide), u₃.gpr,
      g₂, m₅, m₃, mask32_and, mask32_and]
    exact mask32_sub_zero _
  have e₈ : ∀ i, sv c base s₈ i = sv c base s₁ i := fun i => by
    show wordsVal s₈.mem _ _ _ = wordsVal s₁.mem _ _ _
    rw [m₈]
  refine ⟨ctx₁.same hc k₈ (by decide) m₈, K₁.trans (k₈.mono (by decide)), ?_, fun i hi => ?_,
    fun i hi => (e₈ i).trans (eP₁ i hi), fun i hi => (e₈ i).trans (eT₁ i hi), by rw [e₈, e₈, e₈]; exact hz⟩
  · rw [m₈]; exact unch_winWr_pW (by cases b <;> decide) U₁
  · have := R₁ i hi
    show wordsVal s₈.mem _ _ _ < _ ∧ toM _ _ (wordsVal s₈.mem _ _ _) = _
    rw [m₈]; exact this

/-- `pubAdd`: the sum of the Jacobian points in `R` or `D` (`b`) and in `T`,
in the other of `R` and `D`. -/
theorem pubAdd_ok (hc : CfgOk c) (hC : Law c.C) {base : Addr} {s : State} (ctx : CoreCtx c base s) (b : Bool)
    {A B : Point c.C} (hA : onCurve c.C A = true) (hB : onCurve c.C B = true)
    (hp : ∀ i ∈ [(ppt b).1, (ppt b).2.1, (ppt b).2.2], sv c base s i < c.C.p)
    (hq : ∀ i ∈ [TX, TY, TZ], sv c base s i < c.C.p)
    (JA : InvJ c.C (fv c base s (ppt b).1) (fv c base s (ppt b).2.1) (fv c base s (ppt b).2.2) A)
    (JB : InvJ c.C (fv c base s TX) (fv c base s TY) (fv c base s TZ) B) :
    WP isa (c.pubAdd (c.pt (ppt b).1 (ppt b).2.1 (ppt b).2.2) (c.pt TX TY TZ)
        (c.pt (ppt !b).1 (ppt !b).2.1 (ppt !b).2.2)) s fun s' =>
      Rest Mont.callClob s s' ∧ Unch base (pW c winWr) s.mem s'.mem ∧
      (∀ i ∈ [(ppt !b).1, (ppt !b).2.1, (ppt !b).2.2], sv c base s' i < c.C.p) ∧
      InvJ c.C (fv c base s' (ppt !b).1) (fv c base s' (ppt !b).2.1) (fv c base s' (ppt !b).2.2)
        (Spec.Weierstrass.add A B) := by
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  rw [Cfg.pubAdd]
  refine WP.seq (WP.mono (pubAddHead_ok hc ctx b hp hq) fun s₈ M => ?_)
  obtain hr := jacHeadN_run (fun y => tmv c.C c.n base s (pσ c (ppt b) (TX, TY, TZ) (ppt !b) y))
  by_cases hg : (sv c base s₈ T3 ≠ 0 ∧ sv c base s₈ (ppt b).2.2 ≠ 0) ∧ sv c base s₈ TZ ≠ 0
  · -- The Jacobian addition.
    refine WP.ite true (by change some (!s₈.z) = some true; rw [M.z, decide_eq_true hg]; rfl) (fun _ => ?_)
      (fun impossible => nomatch impossible)
    rw [jacTail_eq]
    refine WP.mono (ptRun_ok hc (N := jacTailN) (V := [2, 3, 4, 5, 13, 16]) (by decide) (by decide)
      (p := ppt b) (q := (TX, TY, TZ)) (o := ppt !b) (by cases b <;> decide) (by cases b <;> decide)
      (by cases b <;> decide) M.ctx.scr M.ctx.far M.ctx.mp (fun i hi => (M.vals i ((by decide :
        ∀ i ∈ [2, 3, 4, 5, 13, 16], i ∈ [11, 12, 13, 14, 15, 16] ∨ i ∈ jacHeadN.map FOp.out) i hi)).1))
      fun s₉ ⟨K₉, U₉, R₉⟩ => ?_
    have a2 : tmv c.C c.n base s₈ (pσ c (ppt b) (TX, TY, TZ) (ppt !b) 2) =
        fv c base s (ppt b).1 * (fv c base s TZ * fv c base s TZ) :=
      (M.vals 2 (Or.inr (by decide))).2.trans hr.1
    have a3 : tmv c.C c.n base s₈ (pσ c (ppt b) (TX, TY, TZ) (ppt !b) 3) =
        fv c base s TX * (fv c base s (ppt b).2.2 * fv c base s (ppt b).2.2) -
          fv c base s (ppt b).1 * (fv c base s TZ * fv c base s TZ) :=
      (M.vals 3 (Or.inr (by decide))).2.trans hr.2.1
    have a4 : tmv c.C c.n base s₈ (pσ c (ppt b) (TX, TY, TZ) (ppt !b) 4) =
        fv c base s (ppt b).2.1 * fv c base s TZ * (fv c base s TZ * fv c base s TZ) :=
      (M.vals 4 (Or.inr (by decide))).2.trans hr.2.2.1
    have a5 : tmv c.C c.n base s₈ (pσ c (ppt b) (TX, TY, TZ) (ppt !b) 5) =
        fv c base s TY * fv c base s (ppt b).2.2 * (fv c base s (ppt b).2.2 * fv c base s (ppt b).2.2) -
          fv c base s (ppt b).2.1 * fv c base s TZ * (fv c base s TZ * fv c base s TZ) :=
      (M.vals 5 (Or.inr (by decide))).2.trans hr.2.2.2
    have a13 : tmv c.C c.n base s₈ (pσ c (ppt b) (TX, TY, TZ) (ppt !b) 13) = fv c base s (ppt b).2.2 :=
      (M.vals 13 (Or.inl (by decide))).2
    have a16 : tmv c.C c.n base s₈ (pσ c (ppt b) (TX, TY, TZ) (ppt !b) 16) = fv c base s TZ :=
      (M.vals 16 (Or.inl (by decide))).2
    have hz1 : fv c base s (ppt b).2.2 ≠ 0 := fun h0 =>
      hg.1.2 (by rw [M.eP _ mem3₃]; exact (toM_eq_zero_iff hpR (hp _ mem3₃)).mp h0)
    have hz2 : fv c base s TZ ≠ 0 := fun h0 =>
      hg.2 (by rw [M.eT _ mem3₃]; exact (toM_eq_zero_iff hpR (hq _ mem3₃)).mp h0)
    have hh : fv c base s TX * (fv c base s (ppt b).2.2 * fv c base s (ppt b).2.2) -
        fv c base s (ppt b).1 * (fv c base s TZ * fv c base s TZ) ≠ 0 := fun h0 =>
      hg.1.1 ((toM_eq_zero_iff hpR (M.vals 3 (Or.inr (by decide))).1).mp (a3.trans h0))
    have hj : InvJ c.C (jacAddF (fv c base s (ppt b).1) (fv c base s (ppt b).2.1) (fv c base s (ppt b).2.2)
          (fv c base s TX) (fv c base s TY) (fv c base s TZ)).1
        (jacAddF (fv c base s (ppt b).1) (fv c base s (ppt b).2.1) (fv c base s (ppt b).2.2)
          (fv c base s TX) (fv c base s TY) (fv c base s TZ)).2.1
        (jacAddF (fv c base s (ppt b).1) (fv c base s (ppt b).2.1) (fv c base s (ppt b).2.2)
          (fv c base s TX) (fv c base s TY) (fv c base s TZ)).2.2 (Spec.Weierstrass.add A B) :=
      InvJ.add_ne' hC hA hB JA JB hz1 hz2 hh
    obtain ht := jacTailN_run (fun y => tmv c.C c.n base s₈ (pσ c (ppt b) (TX, TY, TZ) (ppt !b) y))
    refine ⟨M.keep.trans K₉, unch_winWr_trans M.unch (unch_winWr_pW (by cases b <;> decide) U₉),
      fun i hi => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl
      exacts [(R₉ 6 (Or.inr (by decide))).1, (R₉ 7 (Or.inr (by decide))).1, (R₉ 8 (Or.inr (by decide))).1]
    · show InvJ c.C (tmv c.C c.n base s₉ (pσ c (ppt b) (TX, TY, TZ) (ppt !b) 6))
        (tmv c.C c.n base s₉ (pσ c (ppt b) (TX, TY, TZ) (ppt !b) 7))
        (tmv c.C c.n base s₉ (pσ c (ppt b) (TX, TY, TZ) (ppt !b) 8)) _
      rw [(R₉ 6 (Or.inr (by decide))).2, (R₉ 7 (Or.inr (by decide))).2, (R₉ 8 (Or.inr (by decide))).2,
        show runOps jacTailN _ 6 = _ from congrArg Prod.fst ht,
        show runOps jacTailN _ 7 = _ from congrArg (fun x => x.2.1) ht,
        show runOps jacTailN _ 8 = _ from congrArg (fun x => x.2.2) ht, a2, a3, a4, a5, a13, a16]
      exact hj
  · -- The complete addition.
    refine WP.ite false (by change some (!s₈.z) = some false; rw [M.z, decide_eq_false hg]; rfl)
      (fun impossible => nomatch impossible) (fun _ => ?_)
    refine WP.mono (pubSlow_ok hc hC M.ctx b hA hB
      (fun i hi => by rw [M.eP i hi]; exact hp i hi) (fun i hi => by rw [M.eT i hi]; exact hq i hi)
      (by
        show InvJ _ (toM _ _ (sv c base s₈ _)) (toM _ _ (sv c base s₈ _)) (toM _ _ (sv c base s₈ _)) _
        rw [M.eP _ mem3₁, M.eP _ mem3₂, M.eP _ mem3₃]; exact JA)
      (by
        show InvJ _ (toM _ _ (sv c base s₈ _)) (toM _ _ (sv c base s₈ _)) (toM _ _ (sv c base s₈ _)) _
        rw [M.eT _ mem3₁, M.eT _ mem3₂, M.eT _ mem3₃]; exact JB))
      fun s₉ ⟨K₉, U₉, L₉, J₉⟩ => ⟨M.keep.trans K₉, unch_winWr_trans M.unch U₉, L₉, J₉⟩

/-! ## The table of odd multiples -/

/-- The first `cnt` entries of the table are, below `p`, Jacobian triples of
the odd multiples `[2e + 1]P`. -/
def OddOk (c : Cfg) (base : Addr) (P : Point c.C) (m : Mem) (cnt : Nat) : Prop :=
  ∀ e < cnt, (∀ j < 3, wordsVal m base (tblAt c e j) c.n < c.C.p) ∧
    InvJ c.C (toM c.C.p (2 ^ (64 * c.n)) (wordsVal m base (tblAt c e 0) c.n))
      (toM c.C.p (2 ^ (64 * c.n)) (wordsVal m base (tblAt c e 1) c.n))
      (toM c.C.p (2 ^ (64 * c.n)) (wordsVal m base (tblAt c e 2) c.n)) (mul (2 * e + 1) P)

theorem OddOk.unch {base : Addr} {P : Point c.C} {W : List (Nat × Nat)} {m m' : Mem} {cnt : Nat}
    (h : OddOk c base P m cnt) (hu : Unch base W m m') (hfit : c.winTbl + 4 * (6 * c.n) * cnt ≤ 8192)
    (hW : ∀ w ∈ W, w.1 + w.2 ≤ c.winTbl ∨ c.winTbl + 4 * (6 * c.n) * cnt ≤ w.1) :
    OddOk c base P m' cnt := by
  intro e he
  obtain ⟨hl, hr⟩ := h e he
  refine ⟨fun j hj => by rw [winTbl_unch hu he hj hfit hW]; exact hl j hj, ?_⟩
  rw [winTbl_unch hu he (by decide) hfit hW, winTbl_unch hu he (by decide) hfit hW,
    winTbl_unch hu he (by decide) hfit hW]
  exact hr

/-- A point stored as entry `e` extends the table. -/
theorem OddOk.store {base : Addr} {P : Point c.C} {m m' : Mem} {e : Nat} (h : OddOk c base P m e)
    (hc : CfgOk c) (he : e < 2 ^ c.winW) (O : Outside base (tblAt c e 0) (24 * c.n) m m') {x y z : Nat}
    (hx : wordsVal m' base (tblAt c e 0) c.n = x) (hy : wordsVal m' base (tblAt c e 1) c.n = y)
    (hz : wordsVal m' base (tblAt c e 2) c.n = z) (lx : x < c.C.p) (ly : y < c.C.p) (lz : z < c.C.p)
    (hr : InvJ c.C (toM c.C.p (2 ^ (64 * c.n)) x) (toM c.C.p (2 ^ (64 * c.n)) y)
      (toM c.C.p (2 ^ (64 * c.n)) z) (mul (2 * e + 1) P)) : OddOk c base P m' (e + 1) := by
  have hle := tblAt_le hc he
  intro e' he'
  rcases Nat.lt_succ_iff_lt_or_eq.mp he' with h' | rfl
  · exact h.unch O.unch (by dsimp only [tblAt] at hle; omega_using [hle]) (fun w hw => by
      rw [List.mem_singleton.mp hw]; exact Or.inr (by dsimp only [tblAt]; omega_using [])) e' h'
  · refine ⟨fun j hj => ?_, by rw [hx, hy, hz]; exact hr⟩
    obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by omega_using [hj]
    · rw [hx]; exact lx
    · rw [hy]; exact ly
    · rw [hz]; exact lz

/-- `[2]P` is, below `p`, where the table of bits will be, while the table
is built. -/
def TwoOk (c : Cfg) (base : Addr) (P : Point c.C) (m : Mem) : Prop :=
  (∀ d ∈ [bitsAt c.n 0 + 0, bitsAt c.n 0 + 0 + 8 * c.n, bitsAt c.n 0 + 0 + 16 * c.n],
    wordsVal m base d c.n < c.C.p) ∧
    InvJ c.C (toM c.C.p (2 ^ (64 * c.n)) (wordsVal m base (bitsAt c.n 0 + 0) c.n))
      (toM c.C.p (2 ^ (64 * c.n)) (wordsVal m base (bitsAt c.n 0 + 0 + 8 * c.n) c.n))
      (toM c.C.p (2 ^ (64 * c.n)) (wordsVal m base (bitsAt c.n 0 + 0 + 16 * c.n) c.n)) (mul 2 P)

theorem TwoOk.unch {base : Addr} {P : Point c.C} {W : List (Nat × Nat)} {m m' : Mem} (h : TwoOk c base P m)
    (hu : Unch base W m m') (h7 : c.n < 10)
    (hW : ∀ w ∈ W, w.1 + w.2 ≤ bitsAt c.n 0 ∨ bitsAt c.n 0 + 24 * c.n ≤ w.1) : TwoOk c base P m' := by
  have e : ∀ d ∈ [bitsAt c.n 0 + 0, bitsAt c.n 0 + 0 + 8 * c.n, bitsAt c.n 0 + 0 + 16 * c.n],
      wordsVal m' base d c.n = wordsVal m base d c.n := fun d hd => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    have hb := bitsAt_eq c 0
    refine hu.wordsVal (fun w hw => ?_) (by rcases hd with rfl | rfl | rfl <;> omega_using [hb, h7])
    rcases hW w hw with h | h
    · exact Or.inr (by rcases hd with rfl | rfl | rfl <;> omega_using [h])
    · exact Or.inl (by rcases hd with rfl | rfl | rfl <;> omega_using [h])
  refine ⟨fun d hd => by rw [e d hd]; exact h.1 d hd, ?_⟩
  rw [e _ mem3₁, e _ mem3₂, e _ mem3₃]
  exact h.2

/-- What a field program writes is in the working space, below the tables
of bits. -/
theorem pW_below_bits (h7 : c.n < 10) {l : List Nat} (hl : ∀ i ∈ l, i < 45) :
    ∀ w ∈ pW c l, w.1 + w.2 ≤ bitsAt c.n 0 := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    exact sl_le c h7 (hl i hi)
  · rw [List.mem_singleton.mp hw]; exact wk_le c h7 (M := c.MP') rfl

theorem unch_mulBW {base : Addr} {m m' : Mem} (h : Unch base (winTW c) m m') : Unch base (mulBW c) m m' :=
  h.mono fun _ hw => List.mem_append_left _ hw

/-- What the windows' slots keep, `vg_<curve>_mul`'s body keeps. -/
theorem unch_mulBW_winWr {base : Addr} {m m' : Mem} (h : Unch base (pW c winWr) m m') :
    Unch base (mulBW c) m m' := unch_mulBW (unch_winTW h)

theorem unch_mulBW_trans {base : Addr} {m₁ m₂ m₃ : Mem} (h₁ : Unch base (mulBW c) m₁ m₂)
    (h₂ : Unch base (mulBW c) m₂ m₃) : Unch base (mulBW c) m₁ m₃ :=
  (h₁.trans h₂).mono fun _ hw => (List.mem_append.mp hw).elim id id

/-- The build's invariant at `r11 = e`: the entries up to `e` are there, `R`
holds the last, `[2e - 1]P`, and `[2]P` is kept. -/
structure PubBuildInv (c : Cfg) (base : Addr) (P : Point c.C) (s₀ s : State) (e : Nat) : Prop where
  ctx : CoreCtx c base s
  r11 : s.gpr .r11 = BitVec.ofNat 32 e
  keep : Rest powClob s₀ s
  unch : Unch base (mulBW c) s₀.mem s.mem
  tbl : OddOk c base P s.mem e
  two : TwoOk c base P s.mem
  lt : ∀ i ∈ [RX, RY, RZ], sv c base s i < c.C.p
  rep : InvJ c.C (fv c base s RX) (fv c base s RY) (fv c base s RZ) (mul (2 * e - 1) P)

/-- After `pubTableLoad` from `s`, at entry `e`: `D` holds the last entry,
`[2e - 1]P`, and `T` holds `[2]P`. -/
structure TblMid (c : Cfg) (base : Addr) (P : Point c.C) (s s' : State) (e : Nat) : Prop where
  ctx : CoreCtx c base s'
  r11 : s'.gpr .r11 = BitVec.ofNat 32 e
  keep : Rest [.r4, .r5] s s'
  unch : Unch base (pW c winWr) s.mem s'.mem
  ltD : ∀ i ∈ [DX, DY, DZ], sv c base s' i < c.C.p
  ltT : ∀ i ∈ [TX, TY, TZ], sv c base s' i < c.C.p
  repD : InvJ c.C (fv c base s' DX) (fv c base s' DY) (fv c base s' DZ) (mul (2 * e - 1) P)
  repT : InvJ c.C (fv c base s' TX) (fv c base s' TY) (fv c base s' TZ) (mul 2 P)

/-- `pubTableLoad`: `T = [2]P` and `D = R`. -/
theorem pubTableLoad_ok (hc : CfgOk c) {base : Addr} {P : Point c.C} {s₀ s : State} {e : Nat}
    (I : PubBuildInv c base P s₀ s e) : WP isa (.block c.pubTableLoad) s (TblMid c base P s · e) := by
  have h7 := hc.n10
  have hn := I.ctx.scr.nowrap
  have hb0 : bitsAt c.n 0 = 4096 := by rw [bitsAt_eq, Nat.mul_zero, Nat.add_zero]
  have hR45 : ∀ i ∈ [RX, RY, RZ], i < 45 := by decide
  rw [Cfg.pubTableLoad]
  simp only [List.append_assoc]
  refine wp_farPtr (by rw [hb0]; decide) (by decide) fun s₁ k₁ m₁ p₁ => ?_
  obtain ctx₁ := I.ctx.same hc k₁ (by decide) m₁
  refine VG.Proof.X25519.Arm.WP.append (loadPt_ok ctx₁.scr ctx₁.far (n := c.n) (K := bitsAt c.n 0) (d := 0)
    (p := c.pt TX TY TZ) p₁
    (fun x hx => by
      have hx' : x ∈ [TX, TY, TZ].map c.sl := hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
      exact sl_le c h7 ((by decide : ∀ i ∈ [TX, TY, TZ], i < 45) i hi))
    ⟨sl_apart c (by decide), sl_apart c (by decide), sl_apart c (by decide)⟩
    (by rw [hb0]) (by omega_using [hb0, h7]) (by omega_using [h7])) fun s₂ ⟨ex₂, ey₂, ez₂, k₂, O₂⟩ => ?_
  rw [m₁] at ex₂ ey₂ ez₂
  obtain ex₂ : sv c base s₂ TX = wordsVal s.mem base (bitsAt c.n 0 + 0) c.n := ex₂
  obtain ey₂ : sv c base s₂ TY = wordsVal s.mem base (bitsAt c.n 0 + 0 + 8 * c.n) c.n := ey₂
  obtain ez₂ : sv c base s₂ TZ = wordsVal s.mem base (bitsAt c.n 0 + 0 + 16 * c.n) c.n := ez₂
  obtain U₂ : Unch base (slW c [TX, TY, TZ]) s.mem s₂.mem := by
    rw [← m₁]; exact VG.Proof.Weierstrass.Arm.Outs.unch O₂
  obtain ctx₂ := ctx₁.next hc k₂ (by decide) (VG.Proof.Weierstrass.Arm.Outs.unch O₂ :
    Unch base (slW c [TX, TY, TZ]) s₁.mem s₂.mem) (winW_slW h7 (by decide))
  have eR₂ : ∀ i ∈ [RX, RY, RZ], sv c base s₂ i = sv c base s i := fun i hi =>
    sv_unch U₂ h7 hn (hR45 i hi) (apart_slW ((by decide : ∀ i ∈ [RX, RY, RZ], i ∉ [TX, TY, TZ]) i hi))
  -- `D = R`.
  refine WP.mono (copySlots_ok hc ctx₂.scr (o₁ := DX) (o₂ := DY) (o₃ := DZ)
    (a₁ := RX) (a₂ := RY) (a₃ := RZ) (by decide) (by decide) (by decide))
    fun s₃ ⟨ex₃, ey₃, ez₃, k₃, U₃⟩ => ?_
  have eT₃ : ∀ i ∈ [TX, TY, TZ], sv c base s₃ i = sv c base s₂ i := fun i hi =>
    sv_unch U₃ h7 hn ((by decide : ∀ i ∈ [TX, TY, TZ], i < 45) i hi)
      (apart_slW ((by decide : ∀ i ∈ [TX, TY, TZ], i ∉ [DX, DY, DZ]) i hi))
  refine ⟨ctx₂.next hc k₃ (by decide) U₃ (winW_slW h7 (by decide)), ?_,
    ((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans (k₃.mono (by decide)),
    unch_winWr_trans (unch_winWr_slW (by decide) U₂) (unch_winWr_slW (by decide) U₃),
    fun i hi => ?_, fun i hi => ?_, ?_, ?_⟩
  · rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide), I.r11]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · rw [ex₃, eR₂ _ mem3₁]; exact I.lt _ mem3₁
    · rw [ey₃, eR₂ _ mem3₂]; exact I.lt _ mem3₂
    · rw [ez₃, eR₂ _ mem3₃]; exact I.lt _ mem3₃
  · rw [eT₃ i hi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact lt_of_eq_of_lt ex₂ (I.two.1 _ mem3₁)
    · exact lt_of_eq_of_lt ey₂ (I.two.1 _ mem3₂)
    · exact lt_of_eq_of_lt ez₂ (I.two.1 _ mem3₃)
  · show InvJ _ (toM _ _ (sv c base s₃ DX)) (toM _ _ (sv c base s₃ DY)) (toM _ _ (sv c base s₃ DZ)) _
    rw [ex₃, ey₃, ez₃, eR₂ _ mem3₁, eR₂ _ mem3₂, eR₂ _ mem3₃]; exact I.rep
  · show InvJ _ (toM _ _ (sv c base s₃ TX)) (toM _ _ (sv c base s₃ TY)) (toM _ _ (sv c base s₃ TZ)) _
    rw [eT₃ _ mem3₁, eT₃ _ mem3₂, eT₃ _ mem3₃, ex₂, ey₂, ez₂]; exact I.two.2

/-- Entry `e`. -/
theorem pubTableStep_ok (hc : CfgOk c) (hC : Law c.C) {base : Addr} {P : Point c.C}
    (hP : onCurve c.C P = true) {s₀ s : State} {e : Nat} (he1 : 1 ≤ e) (he : e < 8)
    (I : PubBuildInv c base P s₀ s e) :
    WP isa c.pubTableStep s fun s' => PubBuildInv c base P s₀ s' (e + 1) ∧ s'.z = decide (e + 1 = 8) := by
  have h7 := hc.n10
  have hn := I.ctx.scr.nowrap
  have hfit := winTbl_fit hc.n10
  have hsz : size = 4096 := rfl
  have h16 : 8 ≤ 2 ^ c.winW := by rcases pow_winW c with h | h <;> rw [h] <;> decide
  have he16 : e < 2 ^ c.winW := Nat.lt_of_lt_of_le he h16
  have h24 : 4 * (6 * c.n) = 24 * c.n := by omega_using []
  have hb0 : bitsAt c.n 0 = 4096 := by rw [bitsAt_eq, Nat.mul_zero, Nat.add_zero]
  have hwt : c.winTbl = 4096 + 192 * c.n := by unfold Cfg.winTbl; rw [bitsAt_eq]; omega_using []
  have hR45 : ∀ i ∈ [RX, RY, RZ], i < 45 := by decide
  have below : ∀ {l : List Nat}, (∀ i ∈ l, i < 45) → ∀ {cnt : Nat}, ∀ w ∈ pW c l,
      w.1 + w.2 ≤ c.winTbl ∨ c.winTbl + 4 * (6 * c.n) * cnt ≤ w.1 :=
    fun hl _ w hw => Or.inl (pW_below_tbl h7 hl w hw)
  have belowB : ∀ {l : List Nat}, (∀ i ∈ l, i < 45) → ∀ w ∈ pW c l,
      w.1 + w.2 ≤ bitsAt c.n 0 ∨ bitsAt c.n 0 + 24 * c.n ≤ w.1 :=
    fun hl w hw => Or.inl (pW_below_bits h7 hl w hw)
  rw [Cfg.pubTableStep]
  -- `T = [2]P` and `D = R`.
  refine WP.seq (WP.mono (pubTableLoad_ok hc I) fun s₃ M => ?_)
  -- `R = D + [2]P`.
  refine WP.seq (WP.mono (pubAdd_ok hc hC M.ctx false (hC.onCurve_mul hP _) (hC.onCurve_mul hP _)
    M.ltD M.ltT M.repD M.repT) fun s₄ ⟨K₄, U₄, L₄, J₄⟩ => ?_)
  obtain ctx₄ := M.ctx.next hc K₄ (by decide) U₄ (winW_winWr h7)
  rw [hC.add_mul_mul hP, show 2 * e - 1 + 2 = 2 * e + 1 by omega_using [he1]] at J₄
  obtain g₄ : s₄.gpr .r11 = BitVec.ofNat 32 e := by rw [K₄.gpr _ r11_not_clob, M.r11]
  -- The entry, stored.
  rw [Cfg.pubTableStore]
  simp only [List.append_assoc]
  refine wp_entryPtr ((by decide : ∀ n < 10, encodable (BitVec.ofNat 32 (24 * n)) = true) _ h7)
    (by omega_using [hwt, h7]) g₄ fun s₅ k₅ m₅ p₅ => ?_
  obtain ctx₅ := ctx₄.same hc k₅ (by decide) m₅
  refine VG.Proof.X25519.Arm.WP.append (storeEntry_ok hc ctx₅.scr ctx₅.far (d := 0) (e := e) p₅
    (by dsimp only [tblAt]; rw [h24]; omega_using []) he16 (by omega_using [h7]) (by decide))
    fun s₆ ⟨sx, sy, sz, k₆, O₆⟩ => ?_
  obtain e₅ : ∀ i, sv c base s₅ i = sv c base s₄ i := fun i => by show wordsVal s₅.mem _ _ _ = _; rw [m₅]
  rw [e₅] at sx sy sz
  obtain ctx₆ := ctx₅.next hc k₆ (by decide) O₆.unch
    (winW_tbl (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)))
  -- `r11 += 1`.
  refine wp_dp (op2_imm (by decide)) fun s₇ u₇ => wp_cmp (op2_imm (by decide)) fun s₈ f₈ z₈ => WP.block_nil ?_
  obtain g₇ : s₇.gpr .r11 = BitVec.ofNat 32 (e + 1) := by
    rw [u₇.gpr, dpVal, k₆.gpr _ (by decide), k₅.gpr _ (by decide), g₄]
    exact (BitVec.ofNat_add _ _).symm
  obtain k₇₈ : Rest [.r11] s₆ s₈ := (u₇.rest (by simp)).trans (f₈.rest _)
  obtain m₈ : s₈.mem = s₆.mem := by rw [f₈.mem, u₇.mem]
  -- What changed since the step's start, but the entry: the slots.
  obtain U₅ : Unch base (pW c winWr) s.mem s₅.mem := by
    rw [m₅]; exact unch_winWr_trans M.unch U₄
  obtain tbl₆ : OddOk c base P s₆.mem (e + 1) :=
    (I.tbl.unch U₅ (by have := Nat.mul_le_mul_left (4 * (6 * c.n)) (Nat.le_of_lt he16); omega_using [hfit, this])
      (below (by decide))).store hc he16 O₆ sx sy sz (L₄ _ mem3₁) (L₄ _ mem3₂) (L₄ _ mem3₃) J₄
  obtain two₆ : TwoOk c base P s₆.mem :=
    (I.two.unch U₅ h7 (belowB (by decide))).unch O₆.unch h7 fun w hw => by
      rw [List.mem_singleton.mp hw]
      exact Or.inr (by dsimp only [tblAt]; omega_using [hwt, hb0])
  obtain r₆ : ∀ i ∈ [RX, RY, RZ], sv c base s₆ i = sv c base s₄ i := fun i hi => by
    have hle := sl_le c h7 (hR45 i hi)
    have : sv c base s₆ i = sv c base s₅ i := O₆.wordsVal
      (Or.inl (by dsimp only [tblAt]; omega_using [hle, hwt, hsz])) (by omega_using [hle, hsz])
    rw [this, e₅]
  refine ⟨⟨ctx₆.same hc k₇₈ (by decide) m₈, by rw [f₈.gpr, g₇], ?_, ?_, by rw [m₈]; exact tbl₆,
    by rw [m₈]; exact two₆, fun i hi => ?_, ?_⟩, ?_⟩
  · exact (((((I.keep.trans (M.keep.mono (by decide))).trans (K₄.mono (by decide))).trans
      (k₅.mono (by decide))).trans (k₆.mono (by decide))).trans (k₇₈.mono (by decide)))
  · rw [m₈]
    exact unch_mulBW_trans I.unch (unch_mulBW (unch_winTW_trans (unch_winTW U₅) (unch_winTW_entry he16 O₆)))
  · show wordsVal s₈.mem _ _ _ < _
    rw [m₈]
    show sv c base s₆ i < _
    rw [r₆ i hi]
    exact L₄ i hi
  · show InvJ _ (toM _ _ (wordsVal s₈.mem _ _ _)) (toM _ _ (wordsVal s₈.mem _ _ _))
      (toM _ _ (wordsVal s₈.mem _ _ _)) _
    rw [m₈]
    show InvJ _ (toM _ _ (sv c base s₆ RX)) (toM _ _ (sv c base s₆ RY)) (toM _ _ (sv c base s₆ RZ)) _
    rw [r₆ _ mem3₁, r₆ _ mem3₂, r₆ _ mem3₃, show 2 * (e + 1) - 1 = 2 * e + 1 by omega_using []]
    exact J₄
  · rw [z₈, g₇]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    change BitVec.ofNat 32 (e + 1) - BitVec.ofNat 32 8 = 0#32 ↔ e + 1 = 8
    rw [TComb.sub_zero_iff, TComb.ofNat32_eq (by omega_using [he]) (by decide)]

/-- `pubTableInit`: entry 0 is `P`, the affine point in `R`'s first two
slots, `R` holds it and `[2]P` is kept. -/
theorem pubTableInit_ok (hc : CfgOk c) (hC : Law c.C) {base : Addr} {P : Point c.C} (hP : onCurve c.C P = true)
    {s : State} (ctx : CoreCtx c base s) (hqx : sv c base s RX < c.C.p) (hqy : sv c base s RY < c.C.p)
    (hG : Rep c.C (fv c base s RX) (fv c base s RY) 1 P) :
    WP isa c.pubTableInit s fun s' => PubBuildInv c base P s s' 1 := by
  have h7 := hc.n10
  have hn := ctx.scr.nowrap
  have hfit := winTbl_fit hc.n10
  have hsz : size = 4096 := rfl
  have h16 : 8 ≤ 2 ^ c.winW := by rcases pow_winW c with h | h <;> rw [h] <;> decide
  have hb0 : bitsAt c.n 0 = 4096 := by rw [bitsAt_eq, Nat.mul_zero, Nat.add_zero]
  have hwt : c.winTbl = 4096 + 192 * c.n := by unfold Cfg.winTbl; rw [bitsAt_eq]; omega_using []
  have hR45 : ∀ i ∈ [RX, RY, RZ], i < 45 := by decide
  have hRZ := sl_le c h7 (i := RZ) (by decide)
  have hONE := sl_le c h7 (i := ONEP) (by decide)
  have h1z := sl_lt c (i := ONEP) (j := RZ) (by decide)
  have below : ∀ {l : List Nat}, (∀ i ∈ l, i < 45) → ∀ {cnt : Nat}, ∀ w ∈ pW c l,
      w.1 + w.2 ≤ c.winTbl ∨ c.winTbl + 4 * (6 * c.n) * cnt ≤ w.1 :=
    fun hl _ w hw => Or.inl (pW_below_tbl h7 hl w hw)
  rw [Cfg.pubTableInit]
  simp only [List.append_assoc]
  -- `R = (x : y : 1)`.
  refine WP.seq (VG.Proof.X25519.Arm.WP.append (copy_ok (2 * c.n) ctx.scr (o := c.sl RZ) (a := c.sl ONEP)
    (by omega_using [hRZ]) (by omega_using [hONE]) (Or.inr (by omega_using [h1z]))) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
  rw [show 4 * (2 * c.n) = 8 * c.n by omega_using []] at O₁
  rw [← wordsVal_eq_val32, ← wordsVal_eq_val32] at e₁
  obtain U₁ : Unch base (slW c [RZ]) s.mem s₁.mem := O₁.unch
  obtain ctx₁ := ctx.next hc k₁ (by decide) U₁ (winW_slW h7 (by decide))
  -- Entry 0.
  refine wp_farPtr (by omega_using [hwt, h7]) (by decide) fun s₂ k₂ m₂ p₂ => ?_
  obtain ctx₂ := ctx₁.same hc k₂ (by decide) m₂
  refine WP.mono (storeEntry_ok hc ctx₂.scr ctx₂.far (d := 0) (e := 0) p₂
    (by dsimp only [tblAt]; omega_using []) (by omega_using [h16]) (by omega_using [h7]) (by decide))
    fun s₃ ⟨sx, sy, sz, k₃, O₃⟩ => ?_
  obtain ctx₃ := ctx₂.next hc k₃ (by decide) O₃.unch
    (winW_tbl (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)))
  have e₃ : ∀ i, i < 45 → sv c base s₃ i = sv c base s₁ i := fun i hi => by
    have hle := sl_le c h7 hi
    have : sv c base s₃ i = sv c base s₂ i := O₃.wordsVal
      (Or.inl (by dsimp only [tblAt]; omega_using [hle, hwt, hsz])) (by omega_using [hle, hsz])
    rw [this]; show wordsVal s₂.mem _ _ _ = _; rw [m₂]
  have x₁ : sv c base s₁ RX = sv c base s RX := sv_unch U₁ h7 hn (by decide) (apart_slW (l := [RZ]) (by decide))
  have y₁ : sv c base s₁ RY = sv c base s RY := sv_unch U₁ h7 hn (by decide) (apart_slW (l := [RZ]) (by decide))
  have z₁ : sv c base s₁ RZ = sv c base s ONEP := e₁
  obtain J₃ : InvJ c.C (fv c base s₃ RX) (fv c base s₃ RY) (fv c base s₃ RZ) P := by
    refine InvJ.of_rep01 ?_ (Or.inl ?_)
    · show Rep _ (toM _ _ (sv c base s₃ RX)) (toM _ _ (sv c base s₃ RY)) (toM _ _ (sv c base s₃ RZ)) _
      rw [e₃ _ (by decide), e₃ _ (by decide), e₃ _ (by decide), x₁, y₁, z₁]
      have h1 := ctx.fv_onep hc
      rw [show toM c.C.p (2 ^ (64 * c.n)) (sv c base s ONEP) = 1 from h1]
      exact hG
    · show toM _ _ (sv c base s₃ RZ) = 1
      rw [e₃ _ (by decide), z₁]; exact ctx.fv_onep hc
  have ltR₃ : ∀ i ∈ [RX, RY, RZ], sv c base s₃ i < c.C.p := by
    intro i hi
    rw [e₃ i (hR45 i hi)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · rw [x₁]; exact hqx
    · rw [y₁]; exact hqy
    · rw [z₁]; exact ctx.lt hc _ (by decide)
  obtain tbl₃ : OddOk c base P s₃.mem 1 := by
    refine OddOk.store (m := s₂.mem) (fun e he => absurd he (Nat.not_lt_zero _)) hc (by omega_using [h16]) O₃
      sx sy sz ?_ ?_ ?_ ?_
    · show wordsVal s₂.mem _ _ _ < _; rw [m₂]; exact lt_of_eq_of_lt (e₃ RX (by decide)).symm (ltR₃ _ mem3₁)
    · show wordsVal s₂.mem _ _ _ < _; rw [m₂]; exact lt_of_eq_of_lt (e₃ RY (by decide)).symm (ltR₃ _ mem3₂)
    · show wordsVal s₂.mem _ _ _ < _; rw [m₂]; exact lt_of_eq_of_lt (e₃ RZ (by decide)).symm (ltR₃ _ mem3₃)
    · rw [show 2 * 0 + 1 = 1 from rfl, mul_one_pt]
      show InvJ _ (toM _ _ (wordsVal s₂.mem _ _ _)) (toM _ _ (wordsVal s₂.mem _ _ _))
        (toM _ _ (wordsVal s₂.mem _ _ _)) _
      rw [m₂]
      show InvJ _ (toM _ _ (sv c base s₁ RX)) (toM _ _ (sv c base s₁ RY)) (toM _ _ (sv c base s₁ RZ)) _
      rw [← e₃ RX (by decide), ← e₃ RY (by decide), ← e₃ RZ (by decide)]
      exact J₃
  -- `D = [2]P`.
  obtain ⟨N, hN, eN, hd⟩ := winDbl_ok (c := c) hC
  rw [eN]
  refine WP.seq (WP.mono (ptOp_ok hc hN (p₁ := RX) (p₂ := RY) (p₃ := RZ) (q₁ := RX) (q₂ := RY) (q₃ := RZ)
    (o₁ := DX) (o₂ := DY) (o₃ := DZ) (by decide) (by decide) (by decide) ctx₃.scr ctx₃.far ctx₃.mp
    (ctx₃.lt8 hc ltR₃ ltR₃)) fun s₄ ⟨K₄, U₄, L₄, V₄⟩ => ?_)
  obtain ctx₄ := ctx₃.next hc K₄ (by decide) U₄ (winW_pW h7 (by decide))
  have h2 : Spec.Weierstrass.add P P = mul 2 P := by
    have := hC.add_mul_mul hP 1 1
    rwa [mul_one_pt] at this
  obtain J₄ : InvJ c.C (fv c base s₄ DX) (fv c base s₄ DY) (fv c base s₄ DZ) (mul 2 P) := by
    have := hd (fun y => tmv c.C c.n base s₃ (rcbσ c.rcbSlots (c.pt RX RY RZ) (c.pt RX RY RZ)
      (c.pt DX DY DZ) y)) hP (ctx₃.fv_ap hc) J₃
    simp only [Prod.mk.injEq] at V₄
    rw [V₄.1, V₄.2.1, V₄.2.2, ← h2]; exact this
  -- `[2]P`, kept where the table of bits will be.
  refine wp_farPtr (by rw [hb0]; decide) (by decide) fun s₅ k₅ m₅ p₅ => ?_
  obtain ctx₅ := ctx₄.same hc k₅ (by decide) m₅
  refine VG.Proof.X25519.Arm.WP.append (storePt_ok ctx₅.scr ctx₅.far (n := c.n) (K := bitsAt c.n 0) (d := 0)
    (p := c.pt DX DY DZ) p₅ (fun x hx => by
      have hx' : x ∈ [DX, DY, DZ].map c.sl := hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
      exact sl_le c h7 ((by decide : ∀ i ∈ [DX, DY, DZ], i < 45) i hi))
    (by rw [hb0]) (by omega_using [hb0, h7]) (by omega_using [h7])) fun s₆ ⟨tx, ty, tz, k₆, O₆⟩ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₇ u₇ => WP.block_nil ?_
  obtain e₅ : ∀ i, sv c base s₅ i = sv c base s₄ i := fun i => by show wordsVal s₅.mem _ _ _ = _; rw [m₅]
  obtain tx : wordsVal s₆.mem base (bitsAt c.n 0 + 0) c.n = sv c base s₄ DX := tx.trans (e₅ DX)
  obtain ty : wordsVal s₆.mem base (bitsAt c.n 0 + 0 + 8 * c.n) c.n = sv c base s₄ DY := ty.trans (e₅ DY)
  obtain tz : wordsVal s₆.mem base (bitsAt c.n 0 + 0 + 16 * c.n) c.n = sv c base s₄ DZ := tz.trans (e₅ DZ)
  obtain U₆ : Unch base [(bitsAt c.n 0 + 0, 24 * c.n)] s₄.mem s₆.mem := by rw [← m₅]; exact O₆.unch
  obtain k₇ : Rest powClob s s₇ := ((((((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans
    (k₃.mono (by decide))).trans (K₄.mono (by decide))).trans (k₅.mono (by decide))).trans
    (k₆.mono (by decide))).trans (u₇.rest (by decide))
  obtain m₇ : s₇.mem = s₆.mem := u₇.mem
  obtain ctx₆ := ctx₅.far_store hc k₆ (by decide) O₆.unch (by rw [hb0])
  obtain ctx₇ := ctx₆.same hc (u₇.rest (ws := [.r11]) (by simp)) (by decide) m₇
  have eR₇ : ∀ i ∈ [RX, RY, RZ], sv c base s₇ i = sv c base s₃ i := fun i hi => by
    have hle := sl_le c h7 (hR45 i hi)
    have a₆ : sv c base s₆ i = sv c base s₅ i :=
      O₆.wordsVal (Or.inl (by omega_using [hle, hb0, hsz])) (by omega_using [hle, hsz])
    have a₄ : sv c base s₄ i = sv c base s₃ i := sv_pW U₄ h7 hn (hR45 i hi)
      ((by decide : ∀ i ∈ [RX, RY, RZ], i ∉ [T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP]) i hi)
    show wordsVal s₇.mem _ _ _ = _
    rw [m₇]; exact a₆.trans ((e₅ i).trans a₄)
  have hfit1 : c.winTbl + 4 * (6 * c.n) * 1 ≤ 8192 := by
    have := Nat.mul_le_mul_left (4 * (6 * c.n)) (show 1 ≤ 2 ^ c.winW by omega_using [h16])
    omega_using [hfit, this]
  refine ⟨ctx₇, u₇.gpr, k₇, ?_, ?_, ?_, fun i hi => ?_, ?_⟩
  · rw [m₇]
    exact unch_mulBW_trans (unch_mulBW (unch_winTW (unch_winWr_slW (by decide) U₁)))
      (unch_mulBW_trans (unch_mulBW (unch_winTW_entry (e := 0) (by omega_using [h16]) (m₂ ▸ O₃)))
        (unch_mulBW_trans (unch_mulBW (unch_winTW (unch_winWr_pW (by decide) U₄)))
          (U₆.cover fun w hw => by
            rw [List.mem_singleton.mp hw]
            exact ⟨(bitsAt c.n 0, 64 * c.n), List.mem_append_right _ List.mem_cons_self,
              Nat.le_add_right _ _, by omega_using []⟩)))
  · rw [m₇]
    exact (tbl₃.unch U₄ hfit1 (below (by decide))).unch U₆ hfit1 fun w hw => by
      rw [List.mem_singleton.mp hw]; exact Or.inl (by omega_using [hwt, hb0])
  · rw [m₇]
    refine ⟨fun d hd => ?_, by rw [tx, ty, tz]; exact J₄⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · rw [tx]; exact L₄ _ mem3₁
    · rw [ty]; exact L₄ _ mem3₂
    · rw [tz]; exact L₄ _ mem3₃
  · rw [eR₇ i hi]; exact ltR₃ i hi
  · show InvJ _ (toM _ _ (sv c base s₇ RX)) (toM _ _ (sv c base s₇ RY)) (toM _ _ (sv c base s₇ RZ)) _
    rw [eR₇ _ mem3₁, eR₇ _ mem3₂, eR₇ _ mem3₃, show 2 * 1 - 1 = 1 from rfl, mul_one_pt]
    exact J₃

/-- `pubTable`: the table holds the odd multiples `[2e + 1]P` for `e < 8`,
for the affine point `P` in `R`'s first two slots. -/
theorem pubTable_ok (hc : CfgOk c) (hC : Law c.C) {base : Addr} {P : Point c.C} (hP : onCurve c.C P = true)
    {s : State} (ctx : CoreCtx c base s) (hqx : sv c base s RX < c.C.p) (hqy : sv c base s RY < c.C.p)
    (hG : Rep c.C (fv c base s RX) (fv c base s RY) 1 P) :
    WP isa c.pubTable s fun s' => CoreCtx c base s' ∧ Rest powClob s s' ∧
      Unch base (mulBW c) s.mem s'.mem ∧ OddOk c base P s'.mem 8 := by
  rw [Cfg.pubTable]
  refine WP.seq (WP.mono (pubTableInit_ok hc hC hP ctx hqx hqy hG) fun s₁ I₁ => ?_)
  exact upLoop_ok (Inv := fun e t => PubBuildInv c base P s t e) (n := 8) (i := 1)
    (fun e t h1 h8 I => pubTableStep_ok hc hC hP h1 h8 I)
    (fun t I => ⟨I.ctx, I.keep, I.unch, I.tbl⟩) (by decide) I₁

/-! ## The digits and the sum -/

/-- What the sum's code keeps throughout: the working space and the
constants, `k`'s digits where the table of its bits was, and the table. -/
structure PubCtx (c : Cfg) (base : Addr) (P : Point c.C) (k : Nat) (s : State) : Prop
    extends CoreCtx c base s where
  digs : ∀ t < c.pubBits, s.mem (off base (bitsAt c.n 0 + t)) = BitVec.ofNat 8 (Slide.digits c.pubBits k t)
  tbl : OddOk c base P s.mem 8

theorem pubBits_le (hc : CfgOk c) : c.pubBits ≤ 64 * c.n := scalarBits_le hc

theorem tbl8_fit (h7 : c.n < 10) : c.winTbl + 4 * (6 * c.n) * 8 ≤ 8192 := by
  have hfit := winTbl_fit h7
  have h16 : 8 ≤ 2 ^ c.winW := by rcases pow_winW c with h | h <;> rw [h] <;> decide
  have := Nat.mul_le_mul_left (4 * (6 * c.n)) h16
  omega_using [hfit, this]

/-- Code that keeps `r12` and writes only the slots the windows write keeps
it. -/
theorem PubCtx.next {base : Addr} {P : Point c.C} {k : Nat} {s s' : State} (h : PubCtx c base P k s)
    (hc : CfgOk c) {rs : List Reg} (hr : Rest rs s s') (h12 : .r12 ∉ rs)
    (hu : Unch base (pW c winWr) s.mem s'.mem) : PubCtx c base P k s' := by
  have h7 := hc.n10
  refine ⟨h.toCoreCtx.next hc hr h12 hu (winW_winWr h7), fun t ht => ?_,
    h.tbl.unch hu (tbl8_fit h7) fun w hw => Or.inl (pW_below_tbl h7 (by decide) w hw)⟩
  have ht' : t < 64 * c.n := Nat.lt_of_lt_of_le ht (pubBits_le hc)
  rw [tbl_unch hu h7 (j := 0) (by decide) ht' fun w hw =>
    Or.inr (Nat.le_trans (pW_below_bits h7 (by decide) w hw) (Nat.le_add_right _ _)), h.digs t ht]

theorem PubCtx.same {base : Addr} {P : Point c.C} {k : Nat} {s s' : State} (h : PubCtx c base P k s)
    (hc : CfgOk c) {rs : List Reg} (hr : Rest rs s s') (h12 : .r12 ∉ rs) (hm : s'.mem = s.mem) :
    PubCtx c base P k s' :=
  h.next hc hr h12 (by rw [hm]; exact Unch.refl _ _ _)

/-- Digits that are zero from `j` up do not move the top position. -/
theorem topPos_above {D : Nat → Nat} {j : Nat} : ∀ d, (∀ q, j ≤ q → q < j + d → D q = 0) →
    Slide.topPos D (j + d) = Slide.topPos D j
  | 0, _ => rfl
  | d + 1, h => by
    rw [← Nat.add_assoc, Slide.topPos_succ_zero (h _ (Nat.le_add_right _ _) (by omega_using [])),
      topPos_above d fun q h1 h2 => h q h1 (by omega_using [h2])]

/-- The digits from `j` up, of which only the one at `j` is not zero, weigh
that digit. -/
theorem wsum_top {D : Nat → Nat} {j n : Nat} (h : ∀ q, j < q → q < j + (n + 1) → D q = 0) :
    Slide.wsum D j (n + 1) = D j := by
  rw [Slide.wsum_succ, Slide.wsum_eq_zero fun q h1 h2 => h q (by omega_using [h1]) (by omega_using [h2]),
    Nat.mul_zero, Nat.add_zero]

/-- `pubEntry`: the slots `x`, `y`, `z` hold the entry of the odd digit `d`
in `r9`, a Jacobian triple of `[d]P`. -/
theorem pubEntry_ok (hc : CfgOk c) {base : Addr} {P : Point c.C} {k : Nat} {s : State}
    (ctx : PubCtx c base P k s) {d : Nat} (gd : s.gpr .r9 = BitVec.ofNat 32 d) (hd : d % 2 = 1) (hd16 : d < 16)
    {x y z : Nat} (h45 : ∀ i ∈ [x, y, z], i < 45) (hnd : x ≠ y ∧ x ≠ z ∧ y ≠ z) :
    WP isa (.block (c.pubEntry (c.pt x y z))) s fun s' =>
      (∀ i ∈ [x, y, z], sv c base s' i < c.C.p) ∧
      InvJ c.C (fv c base s' x) (fv c base s' y) (fv c base s' z) (mul d P) ∧
      Rest [.r4, .r5] s s' ∧ Unch base (slW c [x, y, z]) s.mem s'.mem := by
  have h7 := hc.n10
  have hsz : size = 4096 := rfl
  have hwt : c.winTbl = 4096 + 192 * c.n := by unfold Cfg.winTbl; rw [bitsAt_eq]; omega_using []
  have h16 : 8 ≤ 2 ^ c.winW := by rcases pow_winW c with h | h <;> rw [h] <;> decide
  obtain ⟨e, rfl⟩ : ∃ e, d = 2 * e + 1 := ⟨d / 2, by omega_using [hd]⟩
  have he : e < 8 := by omega_using [hd16]
  obtain ⟨hl, hJ⟩ := ctx.tbl e he
  have hle := tblAt_le hc (Nat.lt_of_lt_of_le he h16)
  have hK : c.winTbl + 12 * c.n * (2 * e) + 0 = tblAt c e 0 := by
    dsimp only [tblAt]
    have := (by decide : ∀ n < 10, ∀ e < 8, 12 * n * (2 * e) = 4 * (6 * n) * e) _ h7 _ he
    omega_using [this]
  rw [Cfg.pubEntry]
  refine wp_digitEntry ((by decide : ∀ n < 10, encodable (BitVec.ofNat 32 (12 * n)) = true) _ h7)
    (by omega_using [hwt, h7]) gd (by omega_using []) fun s₁ k₁ m₁ p₁ => ?_
  rw [show 2 * e + 1 - 1 = 2 * e by omega_using []] at p₁
  obtain ctx₁ := ctx.same hc k₁ (by decide) m₁
  refine WP.mono (loadPt_ok ctx₁.scr ctx₁.far (n := c.n) (K := c.winTbl + 12 * c.n * (2 * e)) (d := 0)
    (p := c.pt x y z) p₁ (fun i hi => by
      have hi' : i ∈ [x, y, z].map c.sl := hi
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi'
      exact sl_le c h7 (h45 j hj))
    ⟨sl_apart c hnd.1, sl_apart c hnd.2.1, sl_apart c hnd.2.2⟩
    (by rw [hK]; dsimp only [tblAt]; omega_using [hwt, hsz]) (by rw [hK]; exact hle) (by omega_using [h7]))
    fun s₂ ⟨ex, ey, ez, k₂, O₂⟩ => ?_
  rw [hK, m₁] at ex ey ez
  rw [show tblAt c e 0 + 8 * c.n = tblAt c e 1 by dsimp only [tblAt]; omega_using []] at ey
  rw [show tblAt c e 0 + 16 * c.n = tblAt c e 2 by dsimp only [tblAt]; omega_using []] at ez
  obtain ex : sv c base s₂ x = wordsVal s.mem base (tblAt c e 0) c.n := ex
  obtain ey : sv c base s₂ y = wordsVal s.mem base (tblAt c e 1) c.n := ey
  obtain ez : sv c base s₂ z = wordsVal s.mem base (tblAt c e 2) c.n := ez
  refine ⟨fun i hi => ?_, ?_, k₁.trans (k₂.mono (by simp)), ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact lt_of_eq_of_lt ex (hl 0 (by decide))
    · exact lt_of_eq_of_lt ey (hl 1 (by decide))
    · exact lt_of_eq_of_lt ez (hl 2 (by decide))
  · show InvJ _ (toM _ _ (sv c base s₂ x)) (toM _ _ (sv c base s₂ y)) (toM _ _ (sv c base s₂ z)) _
    rw [ex, ey, ez]; exact hJ
  · rw [← m₁]; exact VG.Proof.Weierstrass.Arm.Outs.unch O₂

/-- The search's invariant at `r11 = j`, from `s`: every digit from `j` up is
zero. -/
structure TopInv (c : Cfg) (k : Nat) (s t : State) (j : Nat) : Prop where
  h1 : 1 ≤ j
  hj : j ≤ c.pubBits
  r11 : t.gpr .r11 = BitVec.ofNat 32 j
  keep : Rest [.r4, .r9, .r11] s t
  mem : t.mem = s.mem
  zero : ∀ q, j ≤ q → q < c.pubBits → Slide.digits c.pubBits k q = 0

/-- After the load of the digit of position `j - 1`: it is in `r9`, and `Z`
is set if it is zero. -/
structure TopMid (c : Cfg) (k : Nat) (s t : State) (j : Nat) : Prop where
  r11 : t.gpr .r11 = BitVec.ofNat 32 (j - 1)
  r9 : t.gpr .r9 = BitVec.ofNat 32 (Slide.digits c.pubBits k (j - 1))
  z : t.z = decide (Slide.digits c.pubBits k (j - 1) = 0)
  keep : Rest [.r4, .r9, .r11] s t
  mem : t.mem = s.mem

/-- The search's end: `r11` is the top position and `r9` its digit. -/
def TopDone (c : Cfg) (k : Nat) (s t : State) : Prop :=
  t.gpr .r11 = BitVec.ofNat 32 (Slide.topPos (Slide.digits c.pubBits k) c.pubBits) ∧
    t.gpr .r9 = BitVec.ofNat 32
      (Slide.digits c.pubBits k (Slide.topPos (Slide.digits c.pubBits k) c.pubBits)) ∧
    Rest [.r4, .r9, .r11] s t ∧ t.mem = s.mem

/-- Whether the search goes on below position `j - 1`: its digit is zero and
it is not the last. -/
def topMore (c : Cfg) (k j : Nat) : Bool := decide (Slide.digits c.pubBits k (j - 1) = 0 ∧ j - 1 ≠ 0)

theorem pubTopLoad_ok (hc : CfgOk c) {base : Addr} {P : Point c.C} {k : Nat} {s t : State}
    (ctx : PubCtx c base P k s) {j : Nat} (I : TopInv c k s t j) :
    WP isa (.block (decCounter :: digitLoad (bitsAt c.n 0))) t (TopMid c k s · j) := by
  have h7 := hc.n10
  have hN := pubBits_le hc
  have hb0 : bitsAt c.n 0 = 4096 := by rw [bitsAt_eq, Nat.mul_zero, Nat.add_zero]
  have hd16 : ∀ q, Slide.digits c.pubBits k q < 16 := fun q => by
    rcases Slide.digits_odd c.pubBits k q with h | h
    · rw [h]; decide
    · exact h.2
  obtain ⟨h1, hj, g, kp, mt, -⟩ := I
  obtain ctxt := ctx.same hc kp (by decide) mt
  refine wp_decCounter h1 g fun t₁ v₁ => ?_
  obtain ctx₁ := ctxt.same hc (v₁.rest (ws := [.r11]) (by simp)) (by decide) v₁.mem
  refine wp_digitLoad ctx₁.scr ctx₁.far (nb := c.pubBits) (v := Slide.digits c.pubBits k (j - 1))
    (by omega_using [hb0, hN, h7]) (by rw [hb0]; decide) (by omega_using [h1, hj]) v₁.gpr
    (ctx₁.digs _ (by omega_using [h1, hj])) (hd16 _) fun t₂ k₂ m₂ g₂ z₂ => WP.block_nil ?_
  exact ⟨by rw [k₂.gpr _ (by decide), v₁.gpr], g₂, z₂,
    (kp.trans (v₁.rest (by simp))).trans (k₂.mono (by simp)), by rw [m₂, v₁.mem, mt]⟩

/-- The search's branch, after the digit's load. -/
theorem pubTopTail_ok (hc : CfgOk c) {k : Nat} {s t t₂ : State} {j : Nat} (I : TopInv c k s t j)
    (M : TopMid c k s t₂ j) :
    WP isa (.ite .eq (.block [testCounter]) (.block [.cmp .r9 (.reg .r9)])) t₂ fun t' =>
      isa.eval .ne t' = some (topMore c k j) ∧ (topMore c k j = true → TopInv c k s t' (j - 1)) ∧
      (topMore c k j = false → TopDone c k s t') := by
  have h7 := hc.n10
  have hN := pubBits_le hc
  obtain ⟨h1, hj, -, -, -, hz⟩ := I
  obtain ⟨g11, g₂, z₂, kp₂, mt₂⟩ := M
  by_cases hd : Slide.digits c.pubBits k (j - 1) = 0
  · -- A zero digit: the next position, if any.
    refine WP.ite true (by change some t₂.z = some true; rw [z₂, decide_eq_true hd]) (fun _ => ?_)
      (fun impossible => nomatch impossible)
    refine wp_testCounter (by omega_using [hj, hN, h7]) g11 fun t₃ f₃ z₃ => WP.block_nil ?_
    have hz' : ∀ q, j - 1 ≤ q → q < c.pubBits → Slide.digits c.pubBits k q = 0 := fun q a b => by
      rcases Nat.eq_or_lt_of_le a with e | l
      · rw [← e]; exact hd
      · exact hz q (by omega_using [l]) b
    by_cases h0 : j - 1 = 0
    · have hm : topMore c k j = false := decide_eq_false fun h => h.2 h0
      rw [hm]
      refine ⟨by rw [VG.Proof.X25519.Arm.eval_ne, z₃, decide_eq_true h0]; rfl, nofun, fun _ => ?_⟩
      have etop : Slide.topPos (Slide.digits c.pubBits k) c.pubBits = 0 := by
        have := topPos_above (D := Slide.digits c.pubBits k) (j := 0) c.pubBits
          (fun q _ b => hz' q (by omega_using [h0]) (by omega_using [b]))
        rw [Nat.zero_add] at this
        exact this
      unfold TopDone
      rw [etop]
      refine ⟨by rw [f₃.gpr, g11, h0], ?_, kp₂.trans (f₃.rest _), by rw [f₃.mem, mt₂]⟩
      rw [f₃.gpr, g₂, h0]
    · have hm : topMore c k j = true := decide_eq_true ⟨hd, h0⟩
      rw [hm]
      exact ⟨by rw [VG.Proof.X25519.Arm.eval_ne, z₃, decide_eq_false h0]; rfl, fun _ =>
        ⟨by omega_using [h0], by omega_using [hj], by rw [f₃.gpr, g11],
          kp₂.trans (f₃.rest _), by rw [f₃.mem, mt₂], hz'⟩, nofun⟩
  · -- The top digit.
    refine WP.ite false (by change some t₂.z = some false; rw [z₂, decide_eq_false hd])
      (fun impossible => nomatch impossible) (fun _ => ?_)
    refine wp_cmp (op2_reg _ _) fun t₃ f₃ z₃ => WP.block_nil ?_
    have hm : topMore c k j = false := decide_eq_false fun h => hd h.1
    have etop : Slide.topPos (Slide.digits c.pubBits k) c.pubBits = j - 1 := by
      have := topPos_above (D := Slide.digits c.pubBits k) (j := j) (c.pubBits - j)
        (fun q a b => hz q a (by omega_using [b, hj]))
      rw [show j + (c.pubBits - j) = c.pubBits by omega_using [hj]] at this
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega_using [h1]⟩
      rw [this, Nat.add_sub_cancel]
      exact Slide.topPos_succ_ne (by rw [Nat.add_sub_cancel] at hd; exact hd)
    rw [hm]
    refine ⟨by rw [VG.Proof.X25519.Arm.eval_ne, z₃, BitVec.sub_self]; rfl, nofun, fun _ => ?_⟩
    unfold TopDone
    rw [etop]
    exact ⟨by rw [f₃.gpr, g11], by rw [f₃.gpr, g₂], kp₂.trans (f₃.rest _), by rw [f₃.mem, mt₂]⟩

/-- One position of the search. -/
theorem pubTopStep_ok (hc : CfgOk c) {base : Addr} {P : Point c.C} {k : Nat} {s t : State}
    (ctx : PubCtx c base P k s) {j : Nat} (I : TopInv c k s t j) :
    WP isa c.pubTopStep t fun t' =>
      isa.eval .ne t' = some (topMore c k j) ∧ (topMore c k j = true → TopInv c k s t' (j - 1)) ∧
      (topMore c k j = false → TopDone c k s t') :=
  WP.seq (WP.mono (pubTopLoad_ok hc ctx I) fun _ M => pubTopTail_ok hc I M)

/-- The search's start: `r11` is the number of digits. -/
theorem pubTopInit_ok (hc : CfgOk c) {k : Nat} {s : State} :
    WP isa (.block [.movw .r11 (BitVec.ofNat 16 c.pubBits)]) s (TopInv c k s · c.pubBits) := by
  have h7 := hc.n10
  have hN := pubBits_le hc
  have hN0 : 0 < c.pubBits := by have := hc.len8; unfold Cfg.pubBits; omega_using [this]
  refine VG.Proof.X25519.Arm.wp_movw fun s₁ u₁ => WP.block_nil ?_
  refine ⟨hN0, Nat.le_refl _, ?_, u₁.rest (by simp), u₁.mem, fun q h1 h2 => by omega_using [h1, h2]⟩
  rw [u₁.gpr]
  exact BitVec.eq_of_toNat_eq (by
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega_using [hN, h7])

/-- `pubTop`: `r11` is the position of the highest digit that is not zero
(0 if there is none), and `r9` the digit there. -/
theorem pubTop_ok (hc : CfgOk c) {base : Addr} {P : Point c.C} {k : Nat} {s : State}
    (ctx : PubCtx c base P k s) : WP isa c.pubTop s (TopDone c k s) := by
  rw [Cfg.pubTop]
  refine WP.seq (WP.mono (pubTopInit_ok hc (k := k)) fun s₁ I₁ => ?_)
  refine WP.loop (M := isa) (fun j t => TopInv c k s t j) (fun j t I => ?_) c.pubBits s₁ I₁
  refine WP.mono (pubTopStep_ok hc ctx I) fun t' ⟨he, hm, hd⟩ => ?_
  cases h : topMore c k j
  · exact .inl ⟨by rw [he, h], hd h⟩
  · exact .inr ⟨by rw [he, h], j - 1, by have := I.h1; omega_using [this], hm h⟩

/-- `pubStart`: `R` is a Jacobian triple of `[d]P`, for the top digit `d` in
`r9`. -/
theorem pubStart_ok (hc : CfgOk c) {base : Addr} {P : Point c.C} {k : Nat} {s : State}
    (ctx : PubCtx c base P k s) {d : Nat} (gd : s.gpr .r9 = BitVec.ofNat 32 d)
    (hd : d = 0 ∨ (d % 2 = 1 ∧ d < 16)) :
    WP isa c.pubStart s fun s' =>
      (∀ i ∈ [RX, RY, RZ], sv c base s' i < c.C.p) ∧
      InvJ c.C (fv c base s' RX) (fv c base s' RY) (fv c base s' RZ) (mul d P) ∧
      Rest [.r4, .r5] s s' ∧ Unch base (slW c [RX, RY, RZ]) s.mem s'.mem := by
  rw [Cfg.pubStart]
  refine WP.seq (wp_cmp (op2_imm (by decide)) fun s₁ f₁ z₁ => WP.block_nil ?_)
  obtain ctx₁ := ctx.same hc (f₁.rest []) (by decide) f₁.mem
  have g₁ : s₁.gpr .r9 = BitVec.ofNat 32 d := by rw [f₁.gpr, gd]
  rcases hd with rfl | ⟨hodd, h16⟩
  · refine WP.ite false (by change some (!s₁.z) = some false; rw [z₁, gd]; rfl)
      (fun impossible => nomatch impossible) (fun _ => ?_)
    refine WP.mono (copySlots_ok hc ctx₁.scr (o₁ := RX) (o₂ := RY) (o₃ := RZ) (a₁ := ZERO) (a₂ := ONEP)
      (a₃ := ZERO) (by decide) (by decide) (by decide)) fun s₂ ⟨ex, ey, ez, k₂, U₂⟩ => ?_
    refine ⟨fun i hi => ?_, ?_, (f₁.rest _).trans (k₂.mono (by simp)), by rw [← f₁.mem]; exact U₂⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl
      · exact lt_of_eq_of_lt ex (ctx₁.lt hc _ (by decide))
      · exact lt_of_eq_of_lt ey (ctx₁.lt hc _ (by decide))
      · exact lt_of_eq_of_lt ez (ctx₁.lt hc _ (by decide))
    · rw [mul_zero_pt]
      refine Or.inl ⟨rfl, ?_⟩
      show toM _ _ (sv c base s₂ RZ) = 0
      rw [ez]; exact ctx₁.fv_zero
  · have hne := (by decide : ∀ x < 16, x % 2 = 1 → (BitVec.ofNat 32 x - 0#32 == 0#32) = false) d h16 hodd
    refine WP.ite true (by
        change some (!s₁.z) = some true
        rw [z₁, gd]
        exact congrArg (fun b => some (!b)) hne) (fun _ => ?_) (fun impossible => nomatch impossible)
    exact WP.mono (pubEntry_ok hc ctx₁ g₁ hodd h16 (by decide) (by decide)) fun s₂ ⟨L, J, k₂, U₂⟩ =>
      ⟨L, J, (f₁.rest _).trans k₂, by rw [← f₁.mem]; exact U₂⟩

/-- The sum's invariant at `r11 = j`: `R` is a Jacobian triple, below `p`,
of the multiple of `P` by what the digits from `j` up weigh. -/
structure PubInv (c : Cfg) (base : Addr) (P : Point c.C) (k : Nat) (s₀ s : State) (j : Nat) : Prop where
  ctx : PubCtx c base P k s
  r11 : s.gpr .r11 = BitVec.ofNat 32 j
  keep : Rest powClob s₀ s
  unch : Unch base (mulBW c) s₀.mem s.mem
  lt : ∀ i ∈ [RX, RY, RZ], sv c base s i < c.C.p
  rep : InvJ c.C (fv c base s RX) (fv c base s RY) (fv c base s RZ)
    (mul (Slide.wsum (Slide.digits c.pubBits k) j (c.pubBits - j)) P)

/-- `pubAdd`'s precondition on `D` and `T`: Jacobian triples of `A` and of
`B`, below `p`. -/
structure AddPre (c : Cfg) (base : Addr) (A B : Point c.C) (s : State) : Prop where
  ctx : CoreCtx c base s
  ltD : ∀ i ∈ [DX, DY, DZ], sv c base s i < c.C.p
  ltT : ∀ i ∈ [TX, TY, TZ], sv c base s i < c.C.p
  repD : InvJ c.C (fv c base s DX) (fv c base s DY) (fv c base s DZ) A
  repT : InvJ c.C (fv c base s TX) (fv c base s TY) (fv c base s TZ) B

theorem TblMid.addPre {base : Addr} {P : Point c.C} {s s' : State} {e : Nat} (M : TblMid c base P s s' e) :
    AddPre c base (mul (2 * e - 1) P) (mul 2 P) s' :=
  ⟨M.ctx, M.ltD, M.ltT, M.repD, M.repT⟩

/-- After `pubStepHead` at `r11 = j`: `D` is a Jacobian triple of twice the
sum, the digit of position `j - 1` is in `r9`, and `Z` is set if it is zero. -/
structure StepMid (c : Cfg) (base : Addr) (P : Point c.C) (k : Nat) (s₀ s : State) (j : Nat) : Prop where
  ctx : PubCtx c base P k s
  r11 : s.gpr .r11 = BitVec.ofNat 32 (j - 1)
  r9 : s.gpr .r9 = BitVec.ofNat 32 (Slide.digits c.pubBits k (j - 1))
  z : s.z = decide (Slide.digits c.pubBits k (j - 1) = 0)
  keep : Rest powClob s₀ s
  unch : Unch base (mulBW c) s₀.mem s.mem
  ltD : ∀ i ∈ [DX, DY, DZ], sv c base s i < c.C.p
  repD : InvJ c.C (fv c base s DX) (fv c base s DY) (fv c base s DZ)
    (mul (2 * Slide.wsum (Slide.digits c.pubBits k) j (c.pubBits - j)) P)

/-- `pubStepHead`: the position, `D = 2R` and the digit. -/
theorem pubStepHead_ok (hc : CfgOk c) (hC : Law c.C) {base : Addr} {P : Point c.C} (hP : onCurve c.C P = true)
    {k : Nat} {s₀ s : State} {j : Nat} (hj1 : 1 ≤ j) (hj : j ≤ c.pubBits) (I : PubInv c base P k s₀ s j) :
    WP isa c.pubStepHead s (StepMid c base P k s₀ · j) := by
  have h7 := hc.n10
  have hN := pubBits_le hc
  have hb0 : bitsAt c.n 0 = 4096 := by rw [bitsAt_eq, Nat.mul_zero, Nat.add_zero]
  have hd16 : Slide.digits c.pubBits k (j - 1) < 16 := by
    rcases Slide.digits_odd c.pubBits k (j - 1) with h | h
    · rw [h]; decide
    · exact h.2
  rw [Cfg.pubStepHead]
  refine WP.seq (wp_decCounter hj1 I.r11 fun s₁ u₁ => WP.block_nil ?_)
  obtain ctx₁ := I.ctx.same hc (u₁.rest (ws := [.r11]) (by simp)) (by decide) u₁.mem
  have e₁ : ∀ i, sv c base s₁ i = sv c base s i := fun i => by
    show wordsVal s₁.mem _ _ _ = _; rw [u₁.mem]
  obtain JR₁ : InvJ c.C (fv c base s₁ RX) (fv c base s₁ RY) (fv c base s₁ RZ)
      (mul (Slide.wsum (Slide.digits c.pubBits k) j (c.pubBits - j)) P) := by
    show InvJ _ (toM _ _ (sv c base s₁ RX)) (toM _ _ (sv c base s₁ RY)) (toM _ _ (sv c base s₁ RZ)) _
    rw [e₁, e₁, e₁]; exact I.rep
  have ltR₁ : ∀ i ∈ [RX, RY, RZ], sv c base s₁ i < c.C.p := fun i hi => by rw [e₁]; exact I.lt i hi
  -- `D = 2R`.
  obtain ⟨N, hN', eN, hd⟩ := winDbl_ok (c := c) hC
  rw [eN]
  refine WP.seq (WP.mono (ptOp_ok hc hN' (p₁ := RX) (p₂ := RY) (p₃ := RZ) (q₁ := RX) (q₂ := RY) (q₃ := RZ)
    (o₁ := DX) (o₂ := DY) (o₃ := DZ) (by decide) (by decide) (by decide) ctx₁.scr ctx₁.far ctx₁.mp
    (ctx₁.lt8 hc ltR₁ ltR₁)) fun s₂ ⟨K₂, U₂, L₂, V₂⟩ => ?_)
  obtain U₂' : Unch base (pW c winWr) s₁.mem s₂.mem := unch_winWr_pW (by decide) U₂
  obtain ctx₂ := ctx₁.next hc K₂ (by decide) U₂'
  obtain J₂ : InvJ c.C (fv c base s₂ DX) (fv c base s₂ DY) (fv c base s₂ DZ)
      (mul (2 * Slide.wsum (Slide.digits c.pubBits k) j (c.pubBits - j)) P) := by
    have := hd (fun y => tmv c.C c.n base s₁ (rcbσ c.rcbSlots (c.pt RX RY RZ) (c.pt RX RY RZ)
      (c.pt DX DY DZ) y)) (hC.onCurve_mul hP _) (ctx₁.fv_ap hc) JR₁
    simp only [Prod.mk.injEq] at V₂
    rw [V₂.1, V₂.2.1, V₂.2.2, Nat.two_mul, ← hC.add_mul_mul hP]; exact this
  obtain g₂ : s₂.gpr .r11 = BitVec.ofNat 32 (j - 1) := by rw [K₂.gpr _ r11_not_clob, u₁.gpr]
  -- The digit.
  refine wp_digitLoad ctx₂.scr ctx₂.far (nb := c.pubBits) (v := Slide.digits c.pubBits k (j - 1))
    (by omega_using [hb0, hN, h7]) (by rw [hb0]; decide) (by omega_using [hj1, hj]) g₂
    (ctx₂.digs _ (by omega_using [hj1, hj])) hd16 fun s₃ k₃ m₃ g₃ z₃ => WP.block_nil ?_
  obtain ctx₃ := ctx₂.same hc k₃ (by decide) m₃
  have e₃ : ∀ i, sv c base s₃ i = sv c base s₂ i := fun i => by
    show wordsVal s₃.mem _ _ _ = _; rw [m₃]
  obtain g11₃ : s₃.gpr .r11 = BitVec.ofNat 32 (j - 1) := by rw [k₃.gpr _ (by decide), g₂]
  obtain k₀₃ : Rest powClob s₀ s₃ := ((I.keep.trans (u₁.rest (by decide))).trans (K₂.mono (by decide))).trans
    (k₃.mono (by decide))
  obtain U₀₃ : Unch base (mulBW c) s₀.mem s₃.mem := by
    rw [m₃]; exact unch_mulBW_trans I.unch (unch_mulBW_winWr (by rw [← u₁.mem]; exact U₂'))
  exact ⟨ctx₃, g11₃, g₃, z₃, k₀₃, U₀₃, fun i hi => by rw [e₃]; exact L₂ i hi, by
    show InvJ _ (toM _ _ (sv c base s₃ DX)) (toM _ _ (sv c base s₃ DY)) (toM _ _ (sv c base s₃ DZ)) _
    rw [e₃, e₃, e₃]; exact J₂⟩

/-- The entry of a digit that is not zero, into `T`, after `pubStepHead`. -/
theorem pubStepEntry_ok (hc : CfgOk c) {base : Addr} {P : Point c.C} {k : Nat} {s₀ s : State} {j : Nat}
    (M : StepMid c base P k s₀ s j) (hd0 : Slide.digits c.pubBits k (j - 1) ≠ 0) :
    WP isa (.block (c.pubEntry (c.pt TX TY TZ))) s fun s' =>
      AddPre c base (mul (2 * Slide.wsum (Slide.digits c.pubBits k) j (c.pubBits - j)) P)
        (mul (Slide.digits c.pubBits k (j - 1)) P) s' ∧
      PubCtx c base P k s' ∧ Rest [.r4, .r5] s s' ∧ Unch base (pW c winWr) s.mem s'.mem := by
  have h7 := hc.n10
  have hn := M.ctx.scr.nowrap
  obtain ⟨hodd, hd16⟩ := (Slide.digits_odd c.pubBits k (j - 1)).resolve_left hd0
  refine WP.mono (pubEntry_ok hc M.ctx M.r9 hodd hd16 (x := TX) (y := TY) (z := TZ) (by decide)
    (by decide)) fun s₄ ⟨LT, JT, k₄, U₄⟩ => ?_
  obtain U₄' : Unch base (pW c winWr) s.mem s₄.mem := unch_winWr_slW (by decide) U₄
  obtain ctx₄ := M.ctx.next hc k₄ (by decide) U₄'
  have eD₄ : ∀ i ∈ [DX, DY, DZ], sv c base s₄ i = sv c base s i := fun i hi =>
    sv_unch U₄ h7 hn ((by decide : ∀ i ∈ [DX, DY, DZ], i < 45) i hi)
      (apart_slW ((by decide : ∀ i ∈ [DX, DY, DZ], i ∉ [TX, TY, TZ]) i hi))
  exact ⟨⟨ctx₄.toCoreCtx, fun i hi => by rw [eD₄ i hi]; exact M.ltD i hi, LT, by
    show InvJ _ (toM _ _ (sv c base s₄ DX)) (toM _ _ (sv c base s₄ DY)) (toM _ _ (sv c base s₄ DZ)) _
    rw [eD₄ _ mem3₁, eD₄ _ mem3₂, eD₄ _ mem3₃]; exact M.repD, JT⟩, ctx₄, k₄, U₄'⟩

/-- One digit: from the digits above `j - 1` to those from it. -/
theorem pubStep_ok (hc : CfgOk c) (hC : Law c.C) {base : Addr} {P : Point c.C} (hP : onCurve c.C P = true)
    {k : Nat} {s₀ s : State} {j : Nat} (hj1 : 1 ≤ j) (hj : j ≤ c.pubBits) (I : PubInv c base P k s₀ s j) :
    WP isa c.pubStep s fun s' => PubInv c base P k s₀ s' (j - 1) ∧ s'.z = decide (j - 1 = 0) := by
  have h7 := hc.n10
  have hN := pubBits_le hc
  have hw : Slide.wsum (Slide.digits c.pubBits k) (j - 1) (c.pubBits - (j - 1)) =
      Slide.digits c.pubBits k (j - 1) + 2 * Slide.wsum (Slide.digits c.pubBits k) j (c.pubBits - j) := by
    rw [show c.pubBits - (j - 1) = c.pubBits - j + 1 by omega_using [hj1, hj], Slide.wsum_succ,
      show j - 1 + 1 = j by omega_using [hj1]]
  -- What is left after the digit's addition, or none: the test of the position.
  have fin : ∀ t, PubCtx c base P k t → t.gpr .r11 = BitVec.ofNat 32 (j - 1) → Rest powClob s₀ t →
      Unch base (mulBW c) s₀.mem t.mem → (∀ i ∈ [RX, RY, RZ], sv c base t i < c.C.p) →
      InvJ c.C (fv c base t RX) (fv c base t RY) (fv c base t RZ)
        (mul (Slide.wsum (Slide.digits c.pubBits k) (j - 1) (c.pubBits - (j - 1))) P) →
      WP isa (.block [testCounter]) t fun s' => PubInv c base P k s₀ s' (j - 1) ∧ s'.z = decide (j - 1 = 0) := by
    intro t ct gt kt ut lt' rt
    refine wp_testCounter (by omega_using [hj, hN, h7]) gt fun t' f z => WP.block_nil
      ⟨⟨ct.same hc (f.rest []) (by decide) f.mem, by rw [f.gpr, gt], kt.trans (f.rest _),
        by rw [f.mem]; exact ut, fun i hi => by show wordsVal t'.mem _ _ _ < _; rw [f.mem]; exact lt' i hi, ?_⟩, z⟩
    show InvJ _ (toM _ _ (wordsVal t'.mem _ _ _)) (toM _ _ (wordsVal t'.mem _ _ _))
      (toM _ _ (wordsVal t'.mem _ _ _)) _
    rw [f.mem]; exact rt
  rw [Cfg.pubStep]
  refine WP.seq (WP.mono (pubStepHead_ok hc hC hP hj1 hj I) fun s₃ M => ?_)
  by_cases hd0 : Slide.digits c.pubBits k (j - 1) = 0
  · -- A zero digit: `R = D`.
    refine WP.seq (WP.ite false (by change some (!s₃.z) = some false; rw [M.z, decide_eq_true hd0]; rfl)
      (fun impossible => nomatch impossible) (fun _ => ?_))
    refine WP.mono (copySlots_ok hc M.ctx.scr (o₁ := RX) (o₂ := RY) (o₃ := RZ) (a₁ := DX) (a₂ := DY)
      (a₃ := DZ) (by decide) (by decide) (by decide)) fun s₄ ⟨ex, ey, ez, k₄, U₄⟩ => ?_
    refine fin s₄ (M.ctx.next hc k₄ (by decide) (unch_winWr_slW (by decide) U₄))
      (by rw [k₄.gpr _ (by decide), M.r11]) (M.keep.trans (k₄.mono (by decide)))
      (unch_mulBW_trans M.unch (unch_mulBW_winWr (unch_winWr_slW (by decide) U₄))) (fun i hi => ?_) ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl
      · exact lt_of_eq_of_lt ex (M.ltD _ mem3₁)
      · exact lt_of_eq_of_lt ey (M.ltD _ mem3₂)
      · exact lt_of_eq_of_lt ez (M.ltD _ mem3₃)
    · show InvJ _ (toM _ _ (sv c base s₄ RX)) (toM _ _ (sv c base s₄ RY)) (toM _ _ (sv c base s₄ RZ)) _
      rw [ex, ey, ez, hw, hd0, Nat.zero_add]; exact M.repD
  · -- `R = D + T`, for the digit's entry `T`.
    refine WP.seq (WP.ite true (by change some (!s₃.z) = some true; rw [M.z, decide_eq_false hd0]; rfl)
      (fun _ => ?_) (fun impossible => nomatch impossible))
    refine WP.seq (WP.mono (pubStepEntry_ok hc M hd0) fun s₄ ⟨A₄, ctx₄, k₄, U₄⟩ => ?_)
    refine WP.mono (pubAdd_ok hc hC A₄.ctx false (hC.onCurve_mul hP _) (hC.onCurve_mul hP _)
      A₄.ltD A₄.ltT A₄.repD A₄.repT) fun s₅ ⟨K₅, U₅, L₅, J₅⟩ => ?_
    refine fin s₅ (ctx₄.next hc K₅ (by decide) U₅)
      (by rw [K₅.gpr _ r11_not_clob, k₄.gpr _ (by decide), M.r11])
      ((M.keep.trans (k₄.mono (by decide))).trans (K₅.mono (by decide)))
      (unch_mulBW_trans M.unch (unch_mulBW_winWr (unch_winWr_trans U₄ U₅))) L₅ ?_
    rw [hw, Nat.add_comm, ← hC.add_mul_mul hP]; exact J₅

/-- A slot the windows do not write is apart from everything
`vg_<curve>_mul` writes. -/
theorem sv_mulBW {base : Addr} {m m' : Mem} (hu : Unch base (mulBW c) m m') (h7 : c.n < 10)
    (hn : base.toNat + size ≤ 2 ^ 32) {i : Nat} (hi : i < 45) (hw : i ∉ winWr) :
    wordsVal m' base (c.sl i) c.n = wordsVal m base (c.sl i) c.n :=
  sv_unch hu h7 hn hi fun w hw' => by
    rcases List.mem_append.mp hw' with h | h
    · rcases List.mem_append.mp h with h | h
      · exact apart_append (apart_slW hw) (apart_wk h7 hi) w h
      · rw [List.mem_singleton.mp h]; exact Or.inl (Nat.le_trans (sl_le c h7 hi) (winTbl_ge c))
    · rw [List.mem_singleton.mp h]; exact Or.inl (sl_below_bits c h7 hi 0 0)

/-! ## The stages of `pubBody` -/

/-- `pubBody`'s start: the affine point `P` in `R`'s first two slots, below
`p`, and the number `k < 2^(8 len)` at `K`'s slot. -/
structure PubPre (c : Cfg) (base : Addr) (P : Point c.C) (k : Nat) (s : State) : Prop where
  ctx : CoreCtx c base s
  ltx : sv c base s RX < c.C.p
  lty : sv c base s RY < c.C.p
  rep : Rep c.C (fv c base s RX) (fv c base s RY) 1 P
  kv : sv c base s K = k
  kb : k < 2 ^ (8 * c.C.len)

/-- The top position of `k`'s digits. -/
def pubTopPos (c : Cfg) (k : Nat) : Nat := Slide.topPos (Slide.digits c.pubBits k) c.pubBits

/-- After `pubTable`, from `s₀`: the table, and `k` still at `K`'s slot. -/
def PubS1 (c : Cfg) (base : Addr) (P : Point c.C) (k : Nat) (s₀ s : State) : Prop :=
  CoreCtx c base s ∧ Rest powClob s₀ s ∧ Unch base (mulBW c) s₀.mem s.mem ∧ OddOk c base P s.mem 8 ∧
    sv c base s K = k

/-- After `bits`: the table, and the table of `k`'s bits. -/
def PubS2 (c : Cfg) (base : Addr) (P : Point c.C) (k : Nat) (s₀ s : State) : Prop :=
  CoreCtx c base s ∧ Rest powClob s₀ s ∧ Unch base (mulBW c) s₀.mem s.mem ∧ OddOk c base P s.mem 8 ∧
    ∀ t < c.pubBits, s.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0

/-- After `recode`: the table and `k`'s digits. -/
def PubS3 (c : Cfg) (base : Addr) (P : Point c.C) (k : Nat) (s₀ s : State) : Prop :=
  PubCtx c base P k s ∧ Rest powClob s₀ s ∧ Unch base (mulBW c) s₀.mem s.mem

/-- After `pubTop`: the top position in `r11` and its digit in `r9`. -/
def PubS4 (c : Cfg) (base : Addr) (P : Point c.C) (k : Nat) (s₀ s : State) : Prop :=
  PubS3 c base P k s₀ s ∧ s.gpr .r11 = BitVec.ofNat 32 (pubTopPos c k) ∧
    s.gpr .r9 = BitVec.ofNat 32 (Slide.digits c.pubBits k (pubTopPos c k))

/-- After `pubStart`: `R` is a Jacobian triple of the top digit's multiple. -/
def PubS5 (c : Cfg) (base : Addr) (P : Point c.C) (k : Nat) (s₀ s : State) : Prop :=
  PubS3 c base P k s₀ s ∧ s.gpr .r11 = BitVec.ofNat 32 (pubTopPos c k) ∧
    (∀ i ∈ [RX, RY, RZ], sv c base s i < c.C.p) ∧
    InvJ c.C (fv c base s RX) (fv c base s RY) (fv c base s RZ)
      (mul (Slide.digits c.pubBits k (pubTopPos c k)) P)

theorem pubS1_ok (hc : CfgOk c) (hC : Law c.C) {base : Addr} {P : Point c.C} (hP : onCurve c.C P = true)
    {k : Nat} {s : State} (h : PubPre c base P k s) : WP isa c.pubTable s (PubS1 c base P k s) :=
  WP.mono (pubTable_ok hc hC hP h.ctx h.ltx h.lty h.rep) fun _ ⟨ctx₁, K₁, U₁, tbl₁⟩ =>
    ⟨ctx₁, K₁, U₁, tbl₁, (sv_mulBW U₁ hc.n10 h.ctx.scr.nowrap (by decide) (by decide)).trans h.kv⟩

theorem pubS2_ok (hc : CfgOk c) {base : Addr} {P : Point c.C} {k : Nat} {s₀ s : State}
    (h : PubS1 c base P k s₀ s) :
    WP isa (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) s (PubS2 c base P k s₀) := by
  have h7 := hc.n10
  have hN := pubBits_le hc
  have hb0 : bitsAt c.n 0 = 4096 := by rw [bitsAt_eq, Nat.mul_zero, Nat.add_zero]
  have hwt : c.winTbl = 4096 + 192 * c.n := by unfold Cfg.winTbl; rw [bitsAt_eq]; omega_using []
  obtain ⟨ctx₁, K₁, U₁, tbl₁, eK⟩ := h
  refine WP.mono (tbl_bits_ok hc ctx₁.scr ctx₁.far (i := K) (j := 0) (by decide) (by decide))
    fun s₂ ⟨T₂, K₂, O₂⟩ => ?_
  refine ⟨ctx₁.far_store hc K₂ (by decide) O₂.unch (by rw [hb0]), K₁.trans (K₂.mono (by decide)),
    unch_mulBW_trans U₁ (O₂.unch.mono fun w hw => by
      rw [List.mem_singleton.mp hw]; exact List.mem_append_right _ List.mem_cons_self),
    tbl₁.unch O₂.unch (tbl8_fit h7) fun w hw => by
      rw [List.mem_singleton.mp hw]; exact Or.inl (by omega_using [hwt, hb0]), fun t ht => ?_⟩
  rw [T₂ t (Nat.lt_of_lt_of_le ht hN)]
  show (if (sv c base s K).testBit t then (1 : BitVec 8) else 0) = _
  rw [eK]

theorem pubS3_ok (hc : CfgOk c) {base : Addr} {P : Point c.C} {k : Nat} {s₀ s : State}
    (h : PubS2 c base P k s₀ s) : WP isa (recode (bitsAt c.n 0) c.pubBits) s (PubS3 c base P k s₀) := by
  have h7 := hc.n10
  have hN := pubBits_le hc
  have hN0 : 0 < c.pubBits := by have := hc.len8; unfold Cfg.pubBits; omega_using [this]
  have hb0 : bitsAt c.n 0 = 4096 := by rw [bitsAt_eq, Nat.mul_zero, Nat.add_zero]
  have hwt : c.winTbl = 4096 + 192 * c.n := by unfold Cfg.winTbl; rw [bitsAt_eq]; omega_using []
  obtain ⟨ctx₂, K₂, U₂, tbl₂, B₂⟩ := h
  refine WP.mono (recode_ok ctx₂.scr ctx₂.far (tb := bitsAt c.n 0) (nb := c.pubBits) (k := k)
    (by omega_using [hb0, hN, h7]) (by rw [hb0]; decide) hN0 (by omega_using [hN, h7]) B₂)
    fun s₃ ⟨D₃, K₃, O₃⟩ => ?_
  exact ⟨⟨ctx₂.far_store hc K₃ (by decide) O₃.unch (by rw [hb0]), D₃,
      tbl₂.unch O₃.unch (tbl8_fit h7) fun w hw => by
        rw [List.mem_singleton.mp hw]; exact Or.inl (by omega_using [hwt, hb0, hN])⟩,
    K₂.trans (K₃.mono (by decide)), unch_mulBW_trans U₂ (O₃.unch.cover fun w hw => by
      rw [List.mem_singleton.mp hw]
      exact ⟨(bitsAt c.n 0, 64 * c.n), List.mem_append_right _ List.mem_cons_self, Nat.le_refl _,
        by omega_using [hN]⟩)⟩

theorem pubS4_ok (hc : CfgOk c) {base : Addr} {P : Point c.C} {k : Nat} {s₀ s : State}
    (h : PubS3 c base P k s₀ s) : WP isa c.pubTop s (PubS4 c base P k s₀) :=
  WP.mono (pubTop_ok hc h.1) fun _ ⟨g11, g9, k₄, m₄⟩ =>
    ⟨⟨h.1.same hc k₄ (by decide) m₄, h.2.1.trans (k₄.mono (by decide)), by rw [m₄]; exact h.2.2⟩, g11, g9⟩

theorem pubS5_ok (hc : CfgOk c) {base : Addr} {P : Point c.C} {k : Nat} {s₀ s : State}
    (h : PubS4 c base P k s₀ s) : WP isa c.pubStart s (PubS5 c base P k s₀) :=
  WP.mono (pubStart_ok hc h.1.1 h.2.2 (Slide.digits_odd _ _ _)) fun _ ⟨L₅, J₅, k₅, U₅⟩ =>
    ⟨⟨h.1.1.next hc k₅ (by decide) (unch_winWr_slW (by decide) U₅), h.1.2.1.trans (k₅.mono (by decide)),
      unch_mulBW_trans h.1.2.2 (unch_mulBW_winWr (unch_winWr_slW (by decide) U₅))⟩,
      by rw [k₅.gpr _ (by decide), h.2.1], L₅, J₅⟩

/-- The test of the top position: the sum's invariant there. -/
theorem pubS6_ok (hc : CfgOk c) {base : Addr} {P : Point c.C} {k : Nat} {s₀ s : State}
    (h : PubS5 c base P k s₀ s) :
    WP isa (.block [testCounter]) s fun s' =>
      PubInv c base P k s₀ s' (pubTopPos c k) ∧ s'.z = decide (pubTopPos c k = 0) := by
  have h7 := hc.n10
  have hN := pubBits_le hc
  have hN0 : 0 < c.pubBits := by have := hc.len8; unfold Cfg.pubBits; omega_using [this]
  have htl : pubTopPos c k < c.pubBits := Slide.topPos_lt _ hN0
  obtain ⟨⟨pctx₅, K₅, U₅⟩, g₅, L₅, J₅⟩ := h
  refine wp_testCounter (by omega_using [htl, hN, h7]) g₅ fun s₆ f₆ z₆ => WP.block_nil ⟨?_, z₆⟩
  refine ⟨pctx₅.same hc (f₆.rest []) (by decide) f₆.mem, by rw [f₆.gpr, g₅], K₅.trans (f₆.rest _),
    by rw [f₆.mem]; exact U₅, fun i hi => ?_, ?_⟩
  · show wordsVal s₆.mem _ _ _ < _; rw [f₆.mem]; exact L₅ i hi
  · show InvJ _ (toM _ _ (wordsVal s₆.mem _ _ _)) (toM _ _ (wordsVal s₆.mem _ _ _))
      (toM _ _ (wordsVal s₆.mem _ _ _)) _
    have hz : ∀ q, pubTopPos c k < q → q < c.pubBits → Slide.digits c.pubBits k q = 0 := fun q a b =>
      Slide.topPos_zero _ _ q a b
    rw [f₆.mem, show c.pubBits - pubTopPos c k = c.pubBits - pubTopPos c k - 1 + 1 by omega_using [htl],
      wsum_top (D := Slide.digits c.pubBits k) (j := pubTopPos c k) fun q a b =>
        hz q a (by omega_using [b, htl])]
    exact J₅

/-- `pubFinal`: `R` in projective coordinates, after every digit. -/
theorem pubFinal_ok (hc : CfgOk c) (hC : Law c.C) {base : Addr} {P : Point c.C} {k : Nat}
    (hk : k < 2 ^ c.pubBits) {s₀ t : State} (I : PubInv c base P k s₀ t 0) :
    WP isa c.pubFinal t fun s' => Rest powClob s₀ s' ∧ Unch base (mulBW c) s₀.mem s'.mem ∧
      sv c base s' MP = c.C.p ∧ (∀ i ∈ [RX, RY, RZ], sv c base s' i < c.C.p) ∧
      Rep c.C (fv c base s' RX) (fv c base s' RY) (fv c base s' RZ) (mul k P) := by
  have h7 := hc.n10
  have hn := I.ctx.scr.nowrap
  rw [Cfg.pubFinal]
  obtain JR : InvJ c.C (fv c base t RX) (fv c base t RY) (fv c base t RZ) (mul k P) := by
    have := I.rep
    rwa [Nat.sub_zero, Slide.digits_sum hk] at this
  rw [fromJ_eq]
  refine WP.seq (WP.mono (ptOp_ok hc fromJN_ok (p₁ := RX) (p₂ := RY) (p₃ := RZ) (q₁ := ZERO) (q₂ := ZERO)
    (q₃ := ZERO) (o₁ := DX) (o₂ := DY) (o₃ := DZ) (by decide) (by decide) (by decide) I.ctx.scr I.ctx.far
    I.ctx.mp (I.ctx.lt8 hc I.lt (I.ctx.lt_zero hc))) fun t₁ ⟨K₁', U₁', L₁', V₁'⟩ => ?_)
  obtain ctx₁' := I.ctx.toCoreCtx.next hc K₁' (by decide) U₁' (winW_pW h7 (by decide))
  obtain V := V₁'.trans (fromJN_run _)
  simp only [Prod.mk.injEq] at V
  obtain ⟨vx, vy, vz⟩ := V
  obtain vy : fv c base t₁ DY = fv c base t RY := vy.trans (by
    show fv c base t RY + fv c base t ZERO = _
    rw [I.ctx.fv_zero]; grind)
  refine VG.Proof.X25519.Arm.WP.append (copySlots_ok hc ctx₁'.scr (o₁ := RX) (o₂ := RY) (o₃ := RZ)
    (a₁ := DX) (a₂ := DY) (a₃ := DZ) (by decide) (by decide) (by decide))
    fun t₂ ⟨ex, ey, ez, k₂', U₂'⟩ => ?_
  obtain ctx₂' := ctx₁'.next hc k₂' (by decide) U₂' (winW_slW h7 (by decide))
  refine WP.mono (pubFixY_ok hc ctx₂'.scr (x := RX) (y := RY) (z := RZ) (by decide) (by decide) (by decide))
    fun t₃ ⟨ey₃, k₃', U₃'⟩ => ?_
  obtain ctx₃' := ctx₂'.next hc k₃' (by decide) U₃' (winW_slW h7 (by decide))
  have o₃ : ∀ i, i < 45 → i ≠ RY → sv c base t₃ i = sv c base t₂ i := fun i hi hne =>
    sv_unch (c := c) U₃' h7 hn hi (apart_slW (l := [RY]) (by simpa using hne))
  refine ⟨((I.keep.trans (K₁'.mono (by decide))).trans (k₂'.mono (by decide))).trans
    (k₃'.mono (by decide)), ?_, ctx₃'.mp, fun i hi => ?_, ?_⟩
  · exact unch_mulBW_trans I.unch (unch_mulBW_winWr
      (unch_winWr_trans (unch_winWr_pW (by decide) U₁') (unch_winWr_trans (unch_winWr_slW (by decide) U₂')
        (unch_winWr_slW (by decide) U₃'))))
  · by_cases h : i = RY
    · subst h
      rw [ey₃]; split
      · exact lt_of_eq_of_lt ey (L₁' _ mem3₂)
      · exact ctx₂'.lt hc _ (by decide)
    · rw [o₃ i ((by decide : ∀ i ∈ [RX, RY, RZ], i < 45) i hi) h]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl
      · exact lt_of_eq_of_lt ex (L₁' _ mem3₁)
      · exact absurd rfl h
      · exact lt_of_eq_of_lt ez (L₁' _ mem3₃)
  · have := rep_fromJ_fix hc hC JR (x := sv c base t₂ RX) (y := sv c base t₂ RY) (z := sv c base t₂ RZ)
      (one := sv c base t₂ ONEP) (lt_of_eq_of_lt ez (L₁' _ mem3₃)) (by rw [ex]; exact vx)
      (by rw [ey]; exact vy) (by rw [ez]; exact vz) (ctx₂'.fv_onep hc)
    show Rep _ (toM _ _ (sv c base t₃ RX)) (toM _ _ (sv c base t₃ RY)) (toM _ _ (sv c base t₃ RZ)) _
    rw [o₃ RX (by decide) (by decide), ey₃, o₃ RZ (by decide) (by decide)]
    exact this
/-- The digits below the top one. -/
theorem pubLoop_ok (hc : CfgOk c) (hC : Law c.C) {base : Addr} {P : Point c.C} (hP : onCurve c.C P = true)
    {k : Nat} {s₀ s : State} {j : Nat} (hj1 : 1 ≤ j) (hj : j ≤ c.pubBits) (I : PubInv c base P k s₀ s j) :
    WP isa (.loop c.pubStep .ne) s (PubInv c base P k s₀ · 0) :=
  countLoop_ok (Inv := fun j t => PubInv c base P k s₀ t j) (n := j)
    (fun _ _ h1 h2 I => pubStep_ok hc hC hP h1 (Nat.le_trans h2 hj) I) (fun _ I => I) hj1 I

/-- The digits below the top one, if it is not at position 0. -/
theorem pubDigits_ok (hc : CfgOk c) (hC : Law c.C) {base : Addr} {P : Point c.C} (hP : onCurve c.C P = true)
    {k : Nat} {s₀ s : State} (I : PubInv c base P k s₀ s (pubTopPos c k))
    (hz : s.z = decide (pubTopPos c k = 0)) :
    WP isa (.ite .ne (.loop c.pubStep .ne) (.block [])) s (PubInv c base P k s₀ · 0) := by
  have hN0 : 0 < c.pubBits := by have := hc.len8; unfold Cfg.pubBits; omega_using [this]
  by_cases h0 : pubTopPos c k = 0
  · exact WP.ite false (by change some (!s.z) = some false; rw [hz, decide_eq_true h0]; rfl)
      (fun impossible => nomatch impossible) (fun _ => WP.block_nil (h0 ▸ I))
  · exact WP.ite true (by change some (!s.z) = some true; rw [hz, decide_eq_false h0]; rfl)
      (fun _ => pubLoop_ok hc hC hP (j := pubTopPos c k) (by omega_using [h0])
        (Nat.le_of_lt (Slide.topPos_lt _ hN0)) I) (fun impossible => nomatch impossible)

/-- `pubBody`: `R` holds a representative of `[k]P`, below `p`, for the
affine point `P` of the curve in `R`'s first two slots and the number
`k < 2^(8 len)` at `K`'s slot; only `powClob` and `mulBW` change. -/
theorem pubBody_ok (hc : CfgOk c) (hC : Law c.C) {base : Addr} {s : State} (hs : Scr s base size)
    (hf : Far s base 8192) (hmp : sv c base s MP = c.C.p) (hap : sv c base s AP = c.mont c.C.a)
    (hb3 : sv c base s B3P = c.mont (3 * c.C.b)) (hzero : sv c base s ZERO = 0)
    (hone : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p) (hqx : sv c base s RX < c.C.p)
    (hqy : sv c base s RY < c.C.p) {P : Point c.C} (hP : onCurve c.C P = true)
    (hG : Rep c.C (fv c base s RX) (fv c base s RY) 1 P) (hk : sv c base s K < 2 ^ (8 * c.C.len)) :
    WP isa c.pubBody s fun s' => Rest powClob s s' ∧ Unch base (mulBW c) s.mem s'.mem ∧
      sv c base s' MP = c.C.p ∧ (∀ i ∈ [RX, RY, RZ], sv c base s' i < c.C.p) ∧
      Rep c.C (fv c base s' RX) (fv c base s' RY) (fv c base s' RZ) (mul (sv c base s K) P) := by
  rw [Cfg.pubBody]
  refine WP.seq (WP.mono (pubS1_ok hc hC hP ⟨⟨hs, hf, hmp, hap, hb3, hzero, hone⟩, hqx, hqy, hG, rfl, hk⟩)
    fun _ h₁ => ?_)
  refine WP.seq (WP.mono (pubS2_ok hc h₁) fun _ h₂ => ?_)
  refine WP.seq (WP.mono (pubS3_ok hc h₂) fun _ h₃ => ?_)
  refine WP.seq (WP.mono (pubS4_ok hc h₃) fun _ h₄ => ?_)
  refine WP.seq (WP.mono (pubS5_ok hc h₄) fun _ h₅ => ?_)
  refine WP.seq (WP.mono (pubS6_ok hc h₅) fun s₆ ⟨I₆, z₆⟩ => ?_)
  exact WP.seq (WP.mono (pubDigits_ok hc hC hP I₆ z₆) fun _ I => pubFinal_ok hc hC hk I)

end VG.Proof.Ecdsa.Arm
