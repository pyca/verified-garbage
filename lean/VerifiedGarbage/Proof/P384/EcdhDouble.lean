module

public import VerifiedGarbage.Impl.P384.EcdhDouble
public import VerifiedGarbage.Proof.P384.Linear
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJStep
import VerifiedGarbage.Proof.Weierstrass.JacMul
import VerifiedGarbage.Proof.Framework.Block

/-!
# P-384's doubling for the windows on AArch64

`raw_ok`: the doubling (`Impl/P384/EcdhDouble.lean`) writes the Jacobian
doubling's coordinates (`dblJF`), and so is what the window needs of its
doublings (`dblsOk`).
-/

@[expose] public section

set_option exponentiation.threshold 1024

namespace VG.Proof.P384.EcdhDouble

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Impl.P384.EcdhDouble
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass.Cms
open VG.Proof.P384.Ops (clobX OpKeepX ProgKeepX)
open VG.Proof.Weierstrass.AArch64.Mont (p384)
open Spec.Weierstrass

/-- The slot a step writes. -/
def out : Step → Nat
  | .op f => f.out
  | .lin98 o _ _ | .lin41 o _ _ | .lin38 o _ _ => o

/-- The slots it reads. -/
def ins : Step → List Nat
  | .op f => f.ins
  | .lin98 _ a b | .lin41 _ a b | .lin38 _ a b => [a, b]

/-- What it computes. -/
def run {F : Type _} [Lean.Grind.CommRing F] (E : Nat → F) : Step → Nat → F
  | .op f => f.run E
  | .lin98 o a b => Function.update E o (smulN 9 (E a) - smulN 8 (E b))
  | .lin41 o a b => Function.update E o (smulN 4 (E a) - smulN 1 (E b))
  | .lin38 o a b => Function.update E o (smulN 3 (E a) - smulN 8 (E b))

/-- What steps compute. -/
def runSteps {F : Type _} [Lean.Grind.CommRing F] (l : List Step) (E : Nat → F) : Nat → F := l.foldl run E

/-- Each step reads slots of `V`, or that the steps before it write. -/
def readOk : List Step → List Nat → Bool
  | [], _ => true
  | st :: l, V => (ins st).all (fun x => decide (x ∈ V)) && readOk l (out st :: V)

/-- The slots that hold values after the steps. -/
def valid : List Step → List Nat → List Nat
  | [], V => V
  | st :: l, V => valid l (out st :: V)

theorem mem_valid {x : Nat} : ∀ (l : List Step) (V : List Nat), x ∈ V ∨ x ∈ l.map out → x ∈ valid l V
  | [], V, h => by simpa [valid] using h
  | st :: l, V, h => by
    refine mem_valid l _ ?_
    simp only [List.map_cons, List.mem_cons] at h ⊢
    grind

/-- A step on other slots. -/
def rename (σ : Nat → Nat) : Step → Step
  | .op f => .op (f.rename σ)
  | .lin98 o a b => .lin98 (σ o) (σ a) (σ b)
  | .lin41 o a b => .lin41 (σ o) (σ a) (σ b)
  | .lin38 o a b => .lin38 (σ o) (σ a) (σ b)

theorem run_rename {F : Type _} [Lean.Grind.CommRing F] (σ : Nat → Nat) (st : Step) (E : Nat → F)
    (h : ∀ y, σ y = σ (out st) → y = out st) :
    (fun y => run E (rename σ st) (σ y)) = run (fun y => E (σ y)) st := by
  funext y
  have hy : σ y = σ (out st) ↔ y = out st := ⟨h y, fun h => h ▸ rfl⟩
  cases st with
  | op f => exact congrFun (FOp.run_rename σ f E h) y
  | lin98 o a b | lin41 o a b | lin38 o a b =>
    simp only [out] at hy
    simp only [rename, run, Function.update_apply, hy]

theorem runSteps_rename {F : Type _} [Lean.Grind.CommRing F] (σ : Nat → Nat) : ∀ (l : List Step) (E : Nat → F),
    (∀ st ∈ l, ∀ y, σ y = σ (out st) → y = out st) →
      (fun y => runSteps (l.map (rename σ)) E (σ y)) = runSteps l fun y => E (σ y)
  | [], _, _ => rfl
  | st :: l, E, h => by
    change (fun y => runSteps (l.map (rename σ)) (run E (rename σ st)) (σ y)) = runSteps l (run (fun y => E (σ y)) st)
    rw [runSteps_rename σ l _ (fun st hst => h st (List.mem_cons_of_mem _ hst)),
      run_rename σ st E (h st (List.mem_cons_self ..))]

theorem step_ok {size m : Nat} [NeZero m] (hmp : m = p384) {Sl : Nat → Prop} (hL : Lay Impl.P384.Ops.M size Sl)
    (hAl : Aligned Impl.P384.Ops.M Sl) (hm : UnitMod m (2 ^ (64 * Impl.P384.Ops.M.n))) {base : Addr} {V : List Nat}
    {E : Nat → Fin m} {s : State} (hI : Inv Impl.P384.Ops.M base size m Sl V E s) {st : Step}
    (hS : ∀ x ∈ out st :: ins st, Sl x) (hR : ∀ x ∈ ins st, x ∈ V) :
    WP isa (.block st.code) s fun t => OpKeepX base (out st) s t ∧
      Inv Impl.P384.Ops.M base size m Sl (out st :: V) (run E st) t := by
  cases st with
  | op f => exact Ops.fop_ok hmp hL hAl hm hI hS hR
  | lin98 o a b =>
    simp only [out, ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hS hR
    exact WP.mono (Linear.lin98_ok hI.scr (hmp ▸ hI.mod) hAl.mod (hL.le o hS.1) (hL.le a hS.2.1) (hL.le b hS.2.2)
      (hAl.sl o hS.1) (hAl.sl a hS.2.1) (hAl.sl b hS.2.2) (hmp ▸ hI.lt a hR.1) (hmp ▸ hI.lt b hR.2))
      fun t ⟨k, e⟩ => ⟨k, Linear.cms_ok hmp hL hI hS.1 hR.1 hR.2 k e⟩
  | lin41 o a b =>
    simp only [out, ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hS hR
    exact WP.mono (Linear.lin41_ok hI.scr (hmp ▸ hI.mod) hAl.mod (hL.le o hS.1) (hL.le a hS.2.1) (hL.le b hS.2.2)
      (hAl.sl o hS.1) (hAl.sl a hS.2.1) (hAl.sl b hS.2.2) (hmp ▸ hI.lt a hR.1) (hmp ▸ hI.lt b hR.2))
      fun t ⟨k, e⟩ => ⟨k, Linear.cms_ok hmp hL hI hS.1 hR.1 hR.2 k e⟩
  | lin38 o a b =>
    simp only [out, ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hS hR
    exact WP.mono (Linear.lin38_ok hI.scr (hmp ▸ hI.mod) hAl.mod (hL.le o hS.1) (hL.le a hS.2.1) (hL.le b hS.2.2)
      (hAl.sl o hS.1) (hAl.sl a hS.2.1) (hAl.sl b hS.2.2) (hmp ▸ hI.lt a hR.1) (hmp ▸ hI.lt b hR.2))
      fun t ⟨k, e⟩ => ⟨k, Linear.cms_ok hmp hL hI hS.1 hR.1 hR.2 k e⟩

theorem program_ok {size m : Nat} [NeZero m] (hmp : m = p384) {Sl : Nat → Prop} (hL : Lay Impl.P384.Ops.M size Sl)
    (hAl : Aligned Impl.P384.Ops.M Sl) (hm : UnitMod m (2 ^ (64 * Impl.P384.Ops.M.n))) {base : Addr} :
    ∀ (l : List Step) {V : List Nat} {E : Nat → Fin m} {s : State},
      Inv Impl.P384.Ops.M base size m Sl V E s →
      (∀ st ∈ l, ∀ x ∈ out st :: ins st, Sl x) → readOk l V = true →
      WP isa (.block (l.flatMap Step.code)) s fun t =>
        ProgKeepX base (l.map out) s t ∧
        Inv Impl.P384.Ops.M base size m Sl (valid l V) (runSteps l E) t
  | [], _, _, s, hI, _, _ => WP.block_nil ⟨ProgKeepX.refl _ _ s, hI⟩
  | st :: l, V, E, s, hI, hS, hR => by
    simp only [readOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hR
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (step_ok hmp hL hAl hm hI (hS st (List.mem_cons_self ..)) hR.1) fun u ⟨k₁, I₁⟩ => ?_
    exact WP.mono (program_ok hmp hL hAl hm l I₁ (fun st' h => hS st' (List.mem_cons_of_mem _ h)) hR.2)
      fun t ⟨k₂, I₂⟩ => ⟨(Ops.OpKeepX.prog k₁).trans k₂, I₂⟩

/-! ## The values -/

/-- The steps on the slots `0, 1, …`: the ones they write first. -/
def numbered : List Step := steps ⟨9, 10, 0, 1, 2, 3, 4, 5⟩ ⟨11, 12, 13⟩ ⟨6, 7, 8⟩

theorem numbered_run {F : Type _} [Lean.Grind.CommRing F] (E : Nat → F) :
    (runSteps numbered E 6, runSteps numbered E 7, runSteps numbered E 8) =
      dblJF (E 11) (E 12) (E 13) := by
  simp only [numbered, steps, runSteps, List.foldl, run, FOp.run, Function.update_apply, dblJF, smulN, Prod.mk.injEq, Nat.reduceEqDiff, ite_true,
    ite_false]
  refine ⟨?_, ?_, ?_⟩ <;> grind

theorem steps_run {F : Type _} [Lean.Grind.CommRing F] {S : RcbSlots} {p o : Pt} (E : Nat → F)
    (hAp : RcbApart S p p o) :
    (runSteps (steps S p o) E o.x, runSteps (steps S p o) E o.y,
      runSteps (steps S p o) E o.z) = dblJF (E p.x) (E p.y) (E p.z) := by
  have he : steps S p o = numbered.map (rename (rcbσ S p p o)) := rfl
  have hn : ∀ st ∈ numbered, out st < 9 := by decide
  have hr := runSteps_rename (rcbσ S p p o) numbered E (fun st hst => hAp.inj (hn st hst))
  rw [← he] at hr
  have h := numbered_run fun y => E (rcbσ S p p o y)
  rw [← hr] at h
  exact h

/-- The doubling's values, as the window's contract has them. -/
theorem steps_vals {F : Type _} [Lean.Grind.CommRing F] {S : RcbSlots} {p o : Pt} (E : Nat → F) (hAp : RcbApart S p p o)
    (b : Bool) :
    (runSteps (steps S p o) E o.x, runSteps (steps S p o) E o.y, runSteps (steps S p o) E o.z) =
      (runOps (dblJChoiceN b) (fun y => E (rcbσ S p p o y)) 6, runOps (dblJChoiceN b) (fun y => E (rcbσ S p p o y)) 7,
        runOps (dblJChoiceN b) (fun y => E (rcbσ S p p o y)) 8) :=
  (steps_run E hAp).trans (dblJChoiceN_run b fun y => E (rcbσ S p p o y)).symm

/-! ## The window's doublings -/

theorem p384_C_p : Impl.Ecdsa.AArch64.p384.C.p = p384 := by decide

/-- The slots of a doubling from `p` into `o`. -/
structure RawSlots (p o : Pt) : Prop where
  sl : ∀ st ∈ steps K.S p o, ∀ x ∈ out st :: ins st, x ∈ winSlots K
  out : ∀ st ∈ steps K.S p o, out st ∈ winOther K
  read : readOk (steps K.S p o) [p.x, p.y, p.z] = true
  apart : RcbApart K.S p p o

theorem rawSlots_RD : RawSlots K.R K.D := ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
  by decide +kernel⟩

theorem rawSlots_DR : RawSlots K.D K.R := ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
  by decide +kernel⟩

/-- The doubling from `p` into `o`, as the window's. -/
theorem raw_ok {C : Curve} (hC : C.p = p384) {base : Addr} {size : Nat} (hL : WinLay K size) (hA : WinA K)
    (hm : UnitMod C.p (2 ^ (64 * K.M.n))) {p o : Pt} (h : RawSlots p o) {V : List Nat}
    (hV : ∀ x ∈ [p.x, p.y, p.z], x ∈ V) : DblSpec K C base size (.block (raw p o)) p o V := by
  intro E s hI
  have hR : ∀ (l : List Step) {U W : List Nat}, (∀ x ∈ U, x ∈ W) → readOk l U = true → readOk l W = true := by
    intro l
    induction l with
    | nil => exact fun _ _ => rfl
    | cons st l ih =>
      intro U W hUW hr
      simp only [readOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hr ⊢
      refine ⟨fun x hx => hUW x (hr.1 x hx), ih (fun x hx => ?_) hr.2⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (hUW x hx)
  refine WP.mono (program_ok hC hL.lay hA.al hm (steps K.S p o) hI h.sl (hR _ hV h.read)) fun t ⟨k, I⟩ => ?_
  refine ⟨⟨fun r hr => k.gpr r fun h' => hr ?_, k.rd, k.wr, k.sp⟩, ?_, runSteps (steps K.S p o) E, I.sub fun x hx => ?_, ?_⟩
  · have : ∀ r ∈ clobX, r ∈ clob K.M.n ++ winSaved K.M.n := by decide
    exact this r h'
  · refine (ProgKeepX.mono k (W' := winOther K) fun w hw => ?_).unch
    obtain ⟨st, hst, rfl⟩ := List.mem_map.mp hw
    exact h.out st hst
  · refine mem_valid _ _ ?_
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (by
        simp only [steps, List.map_cons, List.map_nil, out, FOp.out, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        rcases hx with rfl | rfl | rfl <;> simp)
    · exact Or.inl hx
  · exact steps_vals E h.apart _

/-- P-384's doublings, as the window's. -/
theorem dblsOk {C : Curve} (hC : C.p = p384) (hL : WinLay K 8192) (hA : WinA K)
    (hm : UnitMod C.p (2 ^ (64 * K.M.n))) (base : Addr) :
    DblsOk K C base 8192 (some (.block doubleRD, .block doubleDR)) := by
  intro d hd
  cases hd
  exact ⟨raw_ok hC hL hA hm rawSlots_RD (by simp [dblVR]), raw_ok hC hL hA hm rawSlots_DR (by simp)⟩

end VG.Proof.P384.EcdhDouble
