module

import VerifiedGarbage.Proof.P384.EcdhDouble.Raw
public import VerifiedGarbage.Proof.P384.Ops
public import VerifiedGarbage.Proof.P384.EcdhDouble.Certificate
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJStep

/-!
# P-384's allocated doublings

`doubleRD_ok` and `doubleDR_ok`: the allocated doublings
(`Impl/P384/EcdhAllocatedCode.lean`) do what the raw ones do (`raw_ok`), as
their certificates (`Certificate.lean`) let the raw blocks' results stand for
theirs on every slot but the spills, which hold nothing the window reads.
-/

@[expose] public section

-- Powers of two up to `2^384` are evaluated.
set_option exponentiation.threshold 512

namespace VG.Proof.P384.EcdhDouble
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Impl.P384.EcdhDouble
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.P384.Ops (clobX)
open VG.Proof.Weierstrass.AArch64.Mont (p384)
open Spec.Weierstrass

theorem wordsVal_of_words {m m' : Mem} {base : Addr} :
    ∀ {x k : Nat}, (∀ i < k, word m' base (x + 8 * i) = word m base (x + 8 * i)) →
      wordsVal m' base x k = wordsVal m base x k
  | _, 0, _ => rfl
  | x, k + 1, h => by
    simp only [wordsVal]
    have h0 := h 0 (by omega)
    simp only [Nat.mul_zero, Nat.add_zero] at h0
    have hk := wordsVal_of_words (m := m) (m' := m') (base := base) (x := x + 8) (k := k) fun i hi => by
      have := h (i + 1) (by omega)
      rwa [show x + 8 * (i + 1) = x + 8 + 8 * i by omega] at this
    rw [h0, hk]

theorem regs_clobX : ∀ r ∈ regs, r ∈ clobX := by decide

/-- What the window's doublings conclude, as `raw_ok` states it. -/
def DblPost (C : Curve) (base : Addr) (size : Nat) (p o : Pt) (V : List Nat) (E : Nat → Fe C)
    (s s' : State) : Prop :=
  KeepRegs clobX s s' ∧ Unch base (loopW K) s.mem s'.mem ∧ ∃ E' : Nat → Fe C,
    Inv K.M base size C.p (· ∈ winSlots K) ([o.x, o.y, o.z] ++ V) E' s' ∧
    (∀ x, x ∉ rcbW K.S o → E' x = E x) ∧
    (E' o.x, E' o.y, E' o.z) = dblJF (E p.x) (E p.y) (E p.z)

/-- An allocated block refining the raw doubling, which writes only within
the window's loop slots and agrees with it on the slots the result is read
from, concludes what the raw one does. -/
theorem alloc_ok {C : Curve} (hC : C.p = p384) {base : Addr} (hL : WinLay K 8192)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {p o : Pt} (hS : RawSlots p o)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base 8192 C.p (· ∈ winSlots K) V E s) (hV : ∀ x ∈ [p.x, p.y, p.z], x ∈ V)
    {c : List Instr} {Wk : List (Nat × Nat)}
    (hR : ∀ {Q : State → Prop}, WP isa (.block (raw p o)) s Q → WP isa (.block c) s fun t => ∃ u, Q u ∧
      (∀ off, Certificate.observe off → off % 8 = 0 → off + 8 ≤ 8192 → word t.mem base off = word u.mem base off) ∧
      AllocatedFrame regs base Wk s t)
    (hWk : ∀ w ∈ Wk, ∃ w' ∈ loopW K, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2)
    (hobs : ∀ x ∈ K.M.mo :: ([o.x, o.y, o.z] ++ V), ∀ i < 6, Certificate.observe (x + 8 * i)) :
    WP isa (.block c) s fun t => DblPost C base 8192 p o V E s t := by
  refine WP.mono (hR (raw_ok hC hL hA hp hS hI hV)) fun t ⟨u, ⟨_, _, E', Iu, hE, hv⟩, hw, F⟩ => ?_
  have hs : Scr t base 8192 := F.scr (by decide) hI.scr
  have hwv : ∀ x ∈ K.M.mo :: ([o.x, o.y, o.z] ++ V), x + 48 ≤ 8192 →
      wordsVal t.mem base x 6 = wordsVal u.mem base x 6 := fun x hx hx8 =>
    wordsVal_of_words fun i hi => hw _ (hobs x hx i hi) (by
      have : x % 8 = 0 := by
        rcases List.mem_cons.mp hx with rfl | hx
        · decide
        · exact hA.al.sl x (Iu.sl x hx)
      omega) (by omega)
  refine ⟨F.regs.mono regs_clobX, F.unch.cover hWk, E', ⟨hs, ?_, Iu.sl, fun x hx => ?_, fun x hx => ?_⟩, hE, hv⟩
  · have hmo := Iu.mod
    exact ⟨hmo.n0, hmo.n10, hmo.mo, hmo.tmp, hmo.sep,
      by rw [show K.M.n = 6 from rfl, hwv _ (List.mem_cons_self ..) (by decide)]; exact hmo.val,
      hmo.inv, hmo.red, hmo.call⟩
  · rw [show K.M.n = 6 from rfl, hwv x (List.mem_cons_of_mem _ hx) (hL.lay.le x (Iu.sl x hx))]
    exact Iu.lt x hx
  · rw [show K.M.n = 6 from rfl, hwv x (List.mem_cons_of_mem _ hx) (hL.lay.le x (Iu.sl x hx))]
    exact Iu.val x hx

/-- The window's spec of a doubling, from `alloc_ok`. -/
theorem dblSpec_of_alloc {C : Curve} (hC : C.p = p384) {base : Addr} (hL : WinLay K 8192)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {p o : Pt}
    (hS : RawSlots p o) {V : List Nat} (hV : ∀ x ∈ [p.x, p.y, p.z], x ∈ V) {c : List Instr} {Wk : List (Nat × Nat)}
    (hR : ∀ {s : State}, Scr s base 8192 → ∀ {Q : State → Prop}, WP isa (.block (raw p o)) s Q →
      WP isa (.block c) s fun t => ∃ u, Q u ∧
      (∀ off, Certificate.observe off → off % 8 = 0 → off + 8 ≤ 8192 → word t.mem base off = word u.mem base off) ∧
      AllocatedFrame regs base Wk s t)
    (hWk : ∀ w ∈ Wk, ∃ w' ∈ loopW K, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2)
    (hobs : ∀ x ∈ K.M.mo :: ([o.x, o.y, o.z] ++ V), ∀ i < 6, Certificate.observe (x + 8 * i)) :
    DblSpec K C base 8192 (.block c) p o V := by
  intro E s hI
  have hv : dblJF (E p.x) (E p.y) (E p.z) =
      (runOps (dblJChoiceN (K.M.n == 4)) (fun y => E (rcbσ K.S p p o y)) 6,
        runOps (dblJChoiceN (K.M.n == 4)) (fun y => E (rcbσ K.S p p o y)) 7,
        runOps (dblJChoiceN (K.M.n == 4)) (fun y => E (rcbσ K.S p p o y)) 8) := by
    rw [dblJChoiceN_run]
    rfl
  exact WP.mono (alloc_ok hC hL hA hp hS hI hV (hR hI.scr) hWk hobs)
    fun t ⟨k, U, E', I, _, v⟩ => ⟨k.mono fun r h => by
      have : ∀ r ∈ clobX, r ∈ clob K.M.n ++ winSaved K.M.n := by decide
      exact this r h, U, E', I, v.trans hv⟩

theorem p384_C_p : Impl.Ecdsa.AArch64.p384.C.p = p384 := by decide

/-- P-384's allocated doublings do what the window's doublings must. -/
theorem dblsOk {C : Curve} (hC : C.p = p384) (hL : WinLay K 8192) (hA : WinA K)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (base : Addr) :
    DblsOk K C base 8192
      (some (.block Impl.P384.EcdhAllocatedCode.doubleRD, .block Impl.P384.EcdhAllocatedCode.doubleDR)) := by
  intro d hd
  cases hd
  refine ⟨dblSpec_of_alloc hC hL hA hp rawSlots_RD (by decide)
    (fun hs _ hq => Certificate.refineRD hs hq) (by decide) (by decide), ?_⟩
  exact dblSpec_of_alloc hC hL hA hp rawSlots_DR (by decide)
    (fun hs _ hq => Certificate.refineDR hs hq) (by decide) (by decide)

end VG.Proof.P384.EcdhDouble
