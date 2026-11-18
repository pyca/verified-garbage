module

import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardField
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacEntry
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacBuild
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
import VerifiedGarbage.Proof.Weierstrass.X86_64.Pow
import VerifiedGarbage.Proof.Weierstrass.WinJacMath
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacOdd
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Mont.X86_64.Csub
public import VerifiedGarbage.Proof.Weierstrass.Env
public import VerifiedGarbage.Proof.Weierstrass.Law3
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacOddState
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacLay
public import VerifiedGarbage.Proof.Weierstrass.JacAdd
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Impl.Weierstrass.X86_64.CachedJac
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacDbls
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacIter
public import VerifiedGarbage.Proof.Weierstrass.Layout
import VerifiedGarbage.Proof.Weierstrass.JacMadd
public import VerifiedGarbage.Proof.Weierstrass.Jac
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Fprog
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
public import VerifiedGarbage.Proof.Weierstrass.Window5
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Weierstrass.X86_64.Unch
import VerifiedGarbage.Proof.Mont.X86_64.Ops
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacState

/-! ### `Weierstrass.X86_64.WinJacOddBuild`, which this module and modules that import it used -/

section

/-!
# The odd window method on x86-64: the table of odd multiples

`T = P` stored as entry 1 (`buildInit_ok`); DBLU gives `2 P` and `P` sharing
its `Z`, which become `D` and `T` (`jbuildDbluO_ok`); then `T = T + D` by
ZADDU, which leaves `D = 2 P` with the sum's `Z` and is never exceptional for
`1 ≤ m ≤ 15` (`zadduO_x`, from `OddWin.tbl_noexc`), stored as entry `m + 1`,
`[2m + 1]P` (`jbuildStepO_ok`), to entry 16 (`jbuildO_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

variable {K : JacWinCfg} {size : Nat} {C : Curve}

/-- The odd table's invariant at `rbx = m`: entries `1 … m`, `T = [2m - 1]P`,
and `D` a triple of `2 P` sharing `T`'s `Z`. -/
structure JBInvO (K : JacWinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ : State) (m : Nat)
    (s : State) : Prop where
  fr : JFrame K C base size s₀ s
  tbl : JTblOkO K C base P m s
  T : JPt C K.M.n base s (TS K) (mul (2 * m - 1) P)
  rbx : s.gpr .rbx = BitVec.ofNat 64 m
  lt : ∀ x ∈ [K.D.x, K.D.y], wordsVal s.mem base x K.M.n < C.p
  d : InvJ C (tmv C K.M.n base s K.D.x) (tmv C K.M.n base s K.D.y) (tmv C K.M.n base s K.E.z) (mul 2 P)

/-- `D = 2 P` and `T = P` sharing its `Z`, by DBLU from `T = P` and the copies. -/
theorem jbuildDbluO_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C)
    (hM3 : AM3 C) (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true) (hP0 : P ≠ .infinity)
    (hn17 : 17 ≤ C.n) {base : Addr} {s₀ : State} (hF : JacWinPt K C base s₀ P) {s : State}
    (hI : JBInv K C base size P s₀ 1 s) :
    WP isa (ForwardField.programB K.M K.dbluOps).inline s fun s₁ =>
      WP isa (.block (copy K.M.n K.D.x K.E.x ++ copy K.M.n K.D.y K.E.y ++ copy K.M.n K.E.x K.S.t3 ++
        copy K.M.n K.E.y K.S.t2)) s₁ (JBInvO K C base size P s₀ 1) := by
  have hs := hI.fr.scr
  have hn := hs.nowrap
  obtain ⟨tx, ty, tz, t2, t3⟩ := hL.TS_eq
  obtain ⟨-, -, -, -, σ4, σ5, -, -, σ8, σ9, σ10, σ11, σ12, σ13, σ14, σ15⟩ := tblσ_eq K
  obtain o := fun i j hi hj h => hL.oth_ne (K := K) (i := i) (j := j) hi hj h
  obtain hPs : ∀ x ∈ [K.P.x, K.P.y, K.P.z], x ∈ jwSlots K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact ro_mem (by jw_mem)
  obtain I0 : Inv K.M base size C.p (· ∈ jwSlots K) [K.P.x, K.P.y, K.P.z] (tmv C K.M.n base s) s :=
    ⟨hs, hI.fr.mod, hPs, hF.lt hL hI.fr, fun _ _ => rfl⟩
  rw [dblu_eq]
  refine WP.mono (tblProg_ok hL hp dbluN_out dbluN_reads I0 (fun i hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · rw [σ13]; simp
    · rw [σ14]; simp
    · rw [σ15]; simp)) fun s₁ ⟨k₁, I₁, v₁⟩ => ?_
  obtain F₁ := hI.fr.next hL (k₁.scr hs) k₁.regs (k₁.loopW (tblW_loopW hL)) (jwLoopW_sub K)
  obtain val := fun {i : Nat} (h : i ∈ dbluN.map FOp.out) => tbl_val I₁ v₁ h
  -- The points.
  obtain h15 : tmv C K.M.n base s (tblσ K 15) = 1 := by rw [σ15, hI.fr.ro_tmv hL (by jw_mem)]; exact hF.pz
  obtain ⟨hT, h11, h12, h5, h4⟩ := dbluN_run (fun y => tmv C K.M.n base s (tblσ K y)) h15
  generalize runOps dbluN (fun y => tmv C K.M.n base s (tblσ K y)) = r at val hT h11 h12 h5 h4
  obtain JP := hF.jac hL hI.fr
  rw [← σ13, ← σ14] at JP
  obtain J2 := InvJ.dbl' hC hM3 hP JP hT
  rw [show Spec.Weierstrass.add P P = mul 2 P by
    rw [show Spec.Weierstrass.add P P = Spec.Weierstrass.add (mul 1 P) (mul 1 P) by rw [mul_one_pt],
      hC.add_mul_mul hP]] at J2
  obtain hz : r 10 ≠ 0 := fun h =>
    Window5.mul_ne_infinity hO hP hP0 (m := 2) (by decide) (by omega_arith) ((J2.z_zero_iff hC).mp h)
  obtain JD : InvJ C (r 5) (r 4) (r 10) P := JP.rescale hC hz hC.one_ne_zero h5 h4 (by grind)
  -- The values at `s₁`.
  obtain v4 := val (i := 4) (by decide); have v5 := val (i := 5) (by decide)
  obtain v8 := val (i := 8) (by decide); have v9 := val (i := 9) (by decide)
  obtain v10 := val (i := 10) (by decide); have v11 := val (i := 11) (by decide)
  obtain v12 := val (i := 12) (by decide)
  rw [σ4] at v4; rw [σ5] at v5; rw [σ8] at v8; rw [σ9] at v9; rw [σ10] at v10; rw [σ11] at v11
  rw [σ12] at v12
  obtain I₁' : Inv K.M base size C.p (· ∈ jwSlots K) [K.S.t2, K.S.t3, K.E.x, K.E.y, K.E.z, K.z2,
      K.z2 + 8 * K.M.n] (tmv C K.M.n base s₁) s₁ := by
    refine ⟨F₁.scr, F₁.mod, fun x hx => ?_, fun x hx => ?_, fun _ _ => rfl⟩ <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx <;>
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact v4.2.1 | exact v5.2.1 | exact v8.2.1 | exact v9.2.1 | exact v10.2.1 | exact v11.2.1
      | exact v12.2.1 | exact v4.2.2 | exact v5.2.2 | exact v8.2.2 | exact v9.2.2 | exact v10.2.2
      | exact v11.2.2 | exact v12.2.2
  obtain ⟨mx, my, -, -, -⟩ := hL.T_mem
  -- `D = T`, then `T = (S, 8 L)`.
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (copyField_ok hL.lay I₁' (o := K.D.x) (a := K.E.x) (by jw_mem) (by simp))
    fun s₂ ⟨k₂, I₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copyField_ok hL.lay I₂ (o := K.D.y) (a := K.E.y) (by jw_mem) (by simp))
    fun s₃ ⟨k₃, I₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copyField_ok hL.lay I₃ (o := K.E.x) (a := K.S.t3) mx (by simp))
    fun s₄ ⟨k₄, I₄⟩ => ?_
  refine WP.mono (copyField_ok hL.lay I₄ (o := K.E.y) (a := K.S.t2) my (by simp))
    fun s₅ ⟨k₅, I₅⟩ => ?_
  obtain hs₂ := k₂.scr F₁.scr; have hs₃ := k₃.scr hs₂; have hs₄ := k₄.scr hs₃; have hs₅ := k₅.scr hs₄
  obtain F₅ := (((F₁.next hL hs₂ k₂.regs (k₂.loopW (other_loopW (by jw_mem))) (jwLoopW_sub K)).next hL
    hs₃ k₃.regs (k₃.loopW (other_loopW (by jw_mem))) (jwLoopW_sub K)).next hL
    hs₄ k₄.regs (k₄.loopW hL.T_lw.1) (jwLoopW_sub K)).next hL
    hs₅ k₅.regs (k₅.loopW hL.T_lw.2.1) (jwLoopW_sub K)
  -- The slots apart.
  obtain gx : ∀ x ∈ jwOther K, ∀ c < 5, jg K (80 + c) ≠ x := fun x hx c hc e =>
    hL.jg_ne (List.mem_append_right _ hx) (i := 80 + c) (by omega_arith) e.symm
  obtain dxEx : K.D.x ≠ K.E.x := by rw [hL.Tx]; exact (gx _ (by jw_mem) 0 (by decide)).symm
  obtain dxEy : K.D.x ≠ K.E.y := by rw [hL.Ty]; exact (gx _ (by jw_mem) 1 (by decide)).symm
  obtain dyEx : K.D.y ≠ K.E.x := by rw [hL.Tx]; exact (gx _ (by jw_mem) 0 (by decide)).symm
  obtain dyEy : K.D.y ≠ K.E.y := by rw [hL.Ty]; exact (gx _ (by jw_mem) 1 (by decide)).symm
  obtain dyx : K.D.y ≠ K.D.x := o 4 3 (by decide) (by decide) (by decide)
  obtain t3Ex : K.S.t3 ≠ K.E.x := by rw [hL.Tx]; exact (gx _ (by jw_mem) 0 (by decide)).symm
  obtain t2Ex : K.S.t2 ≠ K.E.x := by rw [hL.Tx]; exact (gx _ (by jw_mem) 0 (by decide)).symm
  obtain t2Ey : K.S.t2 ≠ K.E.y := by rw [hL.Ty]; exact (gx _ (by jw_mem) 1 (by decide)).symm
  obtain t3dx : K.S.t3 ≠ K.D.x := o 10 3 (by decide) (by decide) (by decide)
  obtain t3dy : K.S.t3 ≠ K.D.y := o 10 4 (by decide) (by decide) (by decide)
  obtain t2dx : K.S.t2 ≠ K.D.x := o 9 3 (by decide) (by decide) (by decide)
  obtain t2dy : K.S.t2 ≠ K.D.y := o 9 4 (by decide) (by decide) (by decide)
  obtain ExEy : K.E.x ≠ K.E.y := (jw_T_ne hL).1
  obtain jne : ∀ {i j : Nat}, i ≠ j → jg K i ≠ jg K j := fun h e => by
    have := jg_apart K h; rw [e] at this; have := hL.n0; omega_arith
  obtain hT4 : ∀ c, 2 ≤ c → c < 5 → TS K c ≠ K.D.x ∧ TS K c ≠ K.D.y ∧ TS K c ≠ K.E.x ∧ TS K c ≠ K.E.y :=
    fun c h2 hc => ⟨gx _ (by jw_mem) c hc, gx _ (by jw_mem) c hc,
      by rw [hL.Tx]; exact jne (by omega_arith), by rw [hL.Ty]; exact jne (by omega_arith)⟩
  -- The values at `s₅`.
  obtain val₅ := fun x (hx : x ∈ K.E.y :: K.E.x :: K.D.y :: K.D.x :: [K.S.t2, K.S.t3, K.E.x, K.E.y, K.E.z,
      K.z2, K.z2 + 8 * K.M.n]) =>
    And.intro (show tmv C K.M.n base s₅ x = _ from I₅.val x hx) (I₅.lt x hx)
  obtain dx₅ := val₅ K.D.x (by simp)
  rw [Function.update_of_ne dxEy, Function.update_of_ne dxEx, Function.update_of_ne dyx.symm,
    Function.update_self] at dx₅
  obtain dy₅ := val₅ K.D.y (by simp)
  rw [Function.update_of_ne dyEy, Function.update_of_ne dyEx, Function.update_self,
    Function.update_of_ne dxEy.symm] at dy₅
  obtain ex₅ := val₅ K.E.x (by simp)
  rw [Function.update_of_ne ExEy, Function.update_self, Function.update_of_ne t3dy,
    Function.update_of_ne t3dx] at ex₅
  obtain ey₅ := val₅ K.E.y (by simp)
  rw [Function.update_self, Function.update_of_ne t2Ex, Function.update_of_ne t2dy,
    Function.update_of_ne t2dx] at ey₅
  obtain eT : ∀ c, 2 ≤ c → c < 5 → tmv C K.M.n base s₅ (TS K c) = tmv C K.M.n base s₁ (TS K c) ∧
      wordsVal s₅.mem base (TS K c) K.M.n < C.p := fun c h2 hc => by
    obtain hx : TS K c ∈ K.E.y :: K.E.x :: K.D.y :: K.D.x :: [K.S.t2, K.S.t3, K.E.x, K.E.y, K.E.z,
        K.z2, K.z2 + 8 * K.M.n] := by
      have : c = 2 ∨ c = 3 ∨ c = 4 := by omega_arith
      rcases this with rfl | rfl | rfl
      · rw [tz]; simp
      · rw [t2]; simp
      · rw [t3]; simp
    obtain ⟨n1, n2, n3, n4⟩ := hT4 c h2 hc
    refine ⟨(show tmv C K.M.n base s₅ _ = _ from I₅.val _ hx).trans ?_, I₅.lt _ hx⟩
    rw [Function.update_of_ne n4, Function.update_of_ne n3, Function.update_of_ne n2,
      Function.update_of_ne n1]
  obtain e2 := eT 2 (by decide) (by decide); have e3 := eT 3 (by decide) (by decide)
  obtain e4 := eT 4 (by decide) (by decide)
  rw [tz] at e2; rw [t2] at e3; rw [t3] at e4
  -- `T = P` with `Z = Z(2P)`.
  obtain J₅ : JPt C K.M.n base s₅ (TS K) (mul (2 * 1 - 1) P) := by
    rw [show 2 * 1 - 1 = 1 from rfl, mul_one_pt]
    refine ⟨fun c hc => ?_, ?_, ?_, ?_, ?_⟩
    · have : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by omega_arith
      rcases this with rfl | rfl | rfl | rfl | rfl
      · rw [tx]; exact ex₅.2
      · rw [ty]; exact ey₅.2
      · rw [tz]; exact e2.2
      · rw [t2]; exact e3.2
      · rw [t3]; exact e4.2
    · rw [tx, ty, tz, ex₅.1, ey₅.1, e2.1, v5.1, v4.1, v10.1]; exact JD
    · rw [tz, e2.1, v10.1]; exact hz
    · rw [t2, tz, e3.1, e2.1, v11.1, v10.1]; exact h11
    · rw [t3, t2, tz, e4.1, e3.1, e2.1, v12.1, v11.1, v10.1]; exact h12
  obtain T₅ : JTblOkO K C base P 1 s₅ := by
    obtain T₁ := (hI.tbl.loopW hL (k₁.loopW (tblW_loopW hL)) hn (by decide))
    obtain U : Unch base (jwLoopW K) s₁.mem s₅.mem :=
      (((k₂.loopW (other_loopW (by jw_mem))).trans (k₃.loopW (other_loopW (by jw_mem)))).trans
        ((k₄.loopW hL.T_lw.1).trans (k₅.loopW hL.T_lw.2.1))).mono fun w hw => by
          simp only [List.mem_append] at hw; rcases hw with ((h | h) | (h | h)) <;> exact h
    intro m h1 hm
    obtain rfl : m = 1 := by omega_arith
    exact ((T₁.loopW hL U hn (by decide)) 1 (Nat.le_refl _) (Nat.le_refl _))
  obtain hb : s₅.gpr .rbx = BitVec.ofNat 64 1 := by
    rw [k₅.gpr _ (rbx_not_clob _), k₄.gpr _ (rbx_not_clob _), k₃.gpr _ (rbx_not_clob _), k₂.gpr _ (rbx_not_clob _),
      k₁.gpr _ (rbx_not_clob _), hI.rbx]
  refine ⟨F₅, T₅, J₅, hb, fun x hx => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact dx₅.2
    · exact dy₅.2
  · rw [dx₅.1, dy₅.1, e2.1, v8.1, v9.1, v10.1]
    exact J2

/-- ZADDU is not exceptional: for `1 ≤ m ≤ 15`, triples of `2 P` and
`[2m - 1]P` sharing `Z ≠ 0` have different `X`. -/
theorem zadduO_x (hC : Law C) (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true)
    (hP0 : P ≠ .infinity) (hn : 34 ≤ C.n) {m : Nat} (h1 : 1 ≤ m) (h15 : m ≤ 15) {X1 Y1 X2 Y2 Z : Fe C}
    (hd : InvJ C X1 Y1 Z (mul 2 P)) (hm : InvJ C X2 Y2 Z (mul (2 * m - 1) P)) (hz : Z ≠ 0) :
    X1 - X2 ≠ 0 := by
  intro hx
  obtain ⟨ne1, ne2⟩ := OddWin.tbl_noexc hC hO hP hP0 hn h1 h15
  obtain hx' : X1 * (Z * Z) - X2 * (Z * Z) = 0 := by
    obtain e : X1 * (Z * Z) - X2 * (Z * Z) = (X1 - X2) * (Z * Z) := by grind
    rw [e, hx]; grind
  by_cases hy : Y1 * Z * (Z * Z) - Y2 * Z * (Z * Z) = 0
  · exact ne1 (hm.same hC hd hz hz hx' hy)
  · exact ne2 (hm.opposite hC (hC.onCurve_mul hP _) (hC.onCurve_mul hP 2) hd hz hz hx' hy)

/-- An entry of the odd table: `T = T + D` by ZADDU, `D = 2 P` with the sum's
`Z`, stored as entry `m + 1`. -/
theorem jbuildStepO_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C)
    (hM3 : AM3 C) (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true) (hP0 : P ≠ .infinity)
    (hn : 34 ≤ C.n) {base : Addr} {s₀ : State} {m : Nat} (h1 : 1 ≤ m) (h15 : m ≤ 15) {s : State}
    (hI : JBInvO K C base size P s₀ m s) :
    WP isa K.buildStep.inline s fun s' =>
      JBInvO K C base size P s₀ (m + 1) s' ∧ s'.zf = some (decide (m + 1 = 16)) := by
  have hs := hI.fr.scr
  have hn' := hs.nowrap
  obtain ⟨tx, ty, tz, t2, t3⟩ := hL.TS_eq
  obtain ⟨σ0, σ1, -, -, -, -, -, -, σ8, σ9, σ10, σ11, σ12, -⟩ := tblσ_eq K
  rw [JacWinCfg.buildStep]
  simp only [Code.inline]
  refine WP.seq (WP.mono (addRbx_ok s (c := 1) (by decide) hI.rbx) fun s₁ ⟨b₁, k₁⟩ => ?_)
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  have m₁ : s₁.mem = s.mem := k₁.2.1
  obtain F₁ := hI.fr.next hL hs₁ ((Keeps.regs k₁).mono (sub_powClob (by decide))) (W := [])
    (by rw [m₁]; exact Unch.refl _ _ _) (by simp)
  obtain tv₁ : ∀ x, tmv C K.M.n base s₁ x = tmv C K.M.n base s x := fun x => by
    show toM _ _ _ = toM _ _ _; rw [m₁]
  obtain ⟨mx, my, mz, m2, -⟩ := hL.T_mem
  obtain I₁ : Inv K.M base size C.p (· ∈ jwSlots K) [K.D.x, K.D.y, K.E.x, K.E.y, K.E.z, K.z2]
      (tmv C K.M.n base s₁) s₁ := by
    refine ⟨hs₁, F₁.mod, fun x hx => ?_, fun x hx => ?_, fun _ _ => rfl⟩ <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx <;>
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · jw_mem
    · jw_mem
    · exact mx
    · exact my
    · exact mz
    · exact m2
    · rw [m₁]; exact hI.lt _ (by simp)
    · rw [m₁]; exact hI.lt _ (by simp)
    · rw [m₁, ← tx]; exact hI.T.lt 0 (by decide)
    · rw [m₁, ← ty]; exact hI.T.lt 1 (by decide)
    · rw [m₁, ← tz]; exact hI.T.lt 2 (by decide)
    · rw [m₁, ← t2]; exact hI.T.lt 3 (by decide)
  rw [zaddu_eq]
  refine WP.seq (WP.mono (tblProg_ok hL hp zadduN_out zadduN_reads I₁ (fun i hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [σ0]; simp
    · rw [σ1]; simp
    · rw [σ8]; simp
    · rw [σ9]; simp
    · rw [σ10]; simp
    · rw [σ11]; simp)) fun s₂ ⟨k₂, I₂, v₂⟩ => ?_)
  obtain F₂ := F₁.next hL (k₂.scr hs₁) k₂.regs (k₂.loopW (tblW_loopW hL)) (jwLoopW_sub K)
  obtain val := fun {i : Nat} (h : i ∈ zadduN.map FOp.out) => tbl_val I₂ v₂ h
  obtain ⟨hZ, h11, h12⟩ := zadduN_run (fun y => tmv C K.M.n base s₁ (tblσ K y))
  generalize runOps zadduN (fun y => tmv C K.M.n base s₁ (tblσ K y)) = r at val hZ h11 h12
  simp only [σ0, σ1, σ8, σ9, σ10, σ11, tv₁] at hZ h11
  -- The point.
  obtain JT : InvJ C (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z)
      (mul (2 * m - 1) P) := by
    rw [← tx, ← ty, ← tz]; exact hI.T.jac
  obtain hz : tmv C K.M.n base s K.E.z ≠ 0 := by rw [← tz]; exact hI.T.z
  obtain hx := zadduO_x hC hO hP hP0 hn h1 h15 hI.d JT hz
  obtain ⟨JS, JD⟩ := InvJ.zaddu hC hM3 (hC.onCurve_mul hP 2) (hC.onCurve_mul hP _) hI.d JT hz hx
  rw [← hZ] at JS JD
  rw [hC.add_mul_mul hP, show 2 * m - 1 + 2 = 2 * (m + 1) - 1 by omega_arith] at JS
  obtain h11' := h11 (by rw [← tz, ← t2]; exact hI.T.z2)
  obtain v0 := val (i := 0) (by decide); have v1 := val (i := 1) (by decide)
  obtain v8 := val (i := 8) (by decide); have v9 := val (i := 9) (by decide)
  obtain v10 := val (i := 10) (by decide); have v11 := val (i := 11) (by decide)
  obtain v12 := val (i := 12) (by decide)
  rw [σ0] at v0; rw [σ1] at v1; rw [σ8] at v8; rw [σ9] at v9; rw [σ10] at v10; rw [σ11] at v11
  rw [σ12] at v12
  obtain hm1 : mul (2 * (m + 1) - 1) P ≠ .infinity :=
    Window5.mul_ne_infinity hO hP hP0 (by omega_arith) (by omega_arith)
  obtain J₂ : JPt C K.M.n base s₂ (TS K) (mul (2 * (m + 1) - 1) P) := by
    refine ⟨fun c hc => ?_, ?_, ?_, ?_, ?_⟩
    · have : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by omega_arith
      rcases this with rfl | rfl | rfl | rfl | rfl
      · rw [tx]; exact v8.2.1
      · rw [ty]; exact v9.2.1
      · rw [tz]; exact v10.2.1
      · rw [t2]; exact v11.2.1
      · rw [t3]; exact v12.2.1
    · rw [tx, ty, tz, v8.1, v9.1, v10.1]; exact JS
    · rw [tz, v10.1]; exact fun h => hm1 ((JS.z_zero_iff hC).mp h)
    · rw [t2, tz, v11.1, v10.1]; exact h11'
    · rw [t3, t2, tz, v12.1, v11.1, v10.1]; exact h12
  obtain T₂ : JTblOkO K C base P m s₂ :=
    (hI.tbl.loopW hL (by rw [m₁]; exact Unch.refl _ _ _) hn' (by omega_arith)).loopW hL
      (k₂.loopW (tblW_loopW hL)) hn' (by omega_arith)
  -- The entry.
  obtain hb₂ : s₂.gpr .rbx = BitVec.ofNat 64 (m + 1) := by rw [k₂.gpr _ (rbx_not_clob _), b₁]
  rw [WP.block_append_iff]
  refine WP.mono (jstoreEntry_ok hL F₂.scr hb₂ (by omega_arith) (by omega_arith)) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  obtain K₃ := dz_store hL (e := m + 1) (by omega_arith) (by omega_arith) O₃ hn'
  rw [Nat.add_sub_cancel] at e₃ O₃
  obtain hs₃ := F₂.scr.of_keepRegs k₃ (by decide)
  refine WP.mono (cmpRbxJ_ok s₃ (j := m + 1) (i := 16) (by decide) (by omega_arith)
    (by rw [k₃.gpr _ (by decide), hb₂])) fun s₄ ⟨z₄, k₄⟩ => ?_
  have m₄ : s₄.mem = s₃.mem := k₄.2.1
  obtain F₄ := (F₂.next hL hs₃ (k₃.mono (sub_powClob (by decide))) (outside_grid5 O₃)
    (grid5_jwW (by omega_arith))).next hL (hs₃.of_keeps k₄ (by decide)) ((Keeps.regs k₄).mono (by simp))
    (W := []) (by rw [m₄]; exact Unch.refl _ _ _) (by simp)
  obtain tv₄ : ∀ x ∈ [K.D.x, K.D.y, K.E.z], tmv C K.M.n base s₄ x = tmv C K.M.n base s₂ x := fun x hx => by
    show toM _ _ _ = toM _ _ _; rw [m₄, K₃ x hx]
  refine ⟨⟨F₄, fun j hj1 hj => ?_, (J₂.store hL (b := 5 * m) (by omega_arith) O₃ hn').congr fun c _ => by rw [m₄],
    by rw [k₄.1 _ (by simp), k₃.gpr _ (by decide), hb₂], fun x hx => ?_, ?_⟩, z₄⟩
  · rcases Nat.lt_or_ge j (m + 1) with h | h
    · exact ((T₂.store hL O₃ hn' (by omega_arith)) j hj1 (by omega_arith)).congr fun c _ => by rw [m₄]
    · obtain rfl : j = m + 1 := by omega_arith
      exact J₂.congr fun c hc => by rw [m₄]; exact e₃ c hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rw [m₄, K₃ _ (by simp)]; exact v0.2.1
    · rw [m₄, K₃ _ (by simp)]; exact v1.2.1
  · rw [tv₄ _ (by simp), tv₄ _ (by simp), tv₄ _ (by simp), v0.1, v1.1, v10.1]
    exact JD

/-- The table `[1]P, [3]P, …, [31]P`. -/
theorem jbuildO_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C)
    (hM3 : AM3 C) (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true) (hP0 : P ≠ .infinity)
    (hn : 34 ≤ C.n) {base : Addr} {s : State} (hs : Scr s base size) (hM : ModOkW K.M size C.p s.mem base)
    (hF : JacWinPt K C base s P) :
    WP isa K.buildO.inline s fun s' => JFrame K C base size s s' ∧ JTblOkO K C base P 16 s' := by
  rw [JacWinCfg.buildO]
  simp only [Code.inline]
  refine WP.seq (WP.mono (buildInit_ok hL hC hs hM hF) fun s₁ I₁ => ?_)
  refine WP.seq (WP.mono (jbuildDbluO_ok hL hp hC hM3 hO hP hP0 (by omega_arith) hF I₁) fun s₂ h₂ =>
    WP.seq (WP.mono h₂ fun s₃ I₃ => ?_))
  exact countLoop_ok (Inv := fun j t => JBInvO K C base size P s (16 - j) t) (n := 15)
    (fun j t h1 h2 hi => WP.mono (jbuildStepO_ok hL hp hC hM3 hO hP hP0 hn (m := 16 - j) (by omega_arith)
      (by omega_arith) hi) fun u ⟨I, z⟩ => ⟨by rw [show 16 - (j - 1) = 16 - j + 1 by omega_arith]; exact I,
        by rw [z]; congr 1; simp only [decide_eq_decide]; omega_arith⟩)
    (fun t hi => ⟨hi.fr, hi.tbl⟩) (by decide) I₃

end VG.Proof.Weierstrass.X86_64

end

end

/-! ### `Weierstrass.X86_64.WinJacOddStep`, which this module and modules that import it used -/

section

/-! ### `Weierstrass.X86_64.WinJacOddEntry`, which this module and modules that import it used -/

section

/-!
# The odd window method on x86-64: the entry of a digit

Digit `j = rbx`: its window `e` of `oq J k`, read as the comb reads one
(`winIndex`, `hornerBits`), gives the entry `magO e = ((e ⊕ s) ∧ 15) + 1`
(`magnitudeO_ok`, `digitO_ok`), never zero, which is selected into `T`
(`jselect_ok`) and its `Y` negated for `e < 16` (`negY`, as the comb's), so
that `T` holds digit `j`'s point `oddPt` with its powers (`jentryO_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

variable {K : JacWinCfg} {size : Nat} {C : Curve}

/-- The entry of the odd digit of window `v`: `v - 15` for `v ≥ 16`, else `16 - v`. -/
def magO (v : Nat) : Nat := if 16 ≤ v then v - 15 else 16 - v

private theorem magO_fact : ∀ v < 32,
    ((BitVec.ofNat 64 v ^^^ BitVec.ofNat 64 v >>> 4 - BitVec.signExtend 64 (1 : BitVec 32)) &&&
        BitVec.signExtend 64 (15 : BitVec 32)) + BitVec.signExtend 64 (1 : BitVec 32) =
      BitVec.ofNat 64 (magO v) := by
  decide +kernel

/-- `rax = r8 = magO v` from the window `v < 32` in `rax`, through `rdx`. -/
theorem magnitudeO_ok (s : State) {v : Nat} (hv : v < 32) (hx : s.gpr .rax = BitVec.ofNat 64 v) :
    WP isa (.block JacWinCfg.magnitudeO) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (magO v) ∧ t.gpr .r8 = BitVec.ofNat 64 (magO v) ∧
        Keeps [.rax, .rdx, .r8] s t := by
  crun [JacWinCfg.magnitudeO, hx]
  rw [magO_fact v hv]
  refine ⟨rfl, rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2,
    ite_false]

theorem magO_pos {v : Nat} (hv : v < 32) : 1 ≤ magO v ∧ magO v ≤ 16 := by
  unfold magO; split <;> omega_arith

/-- The entry `magO e` of digit `rbx = j` into `rax` and `r8`, from window `j`
of `k` in its table of bits at `K.bits`. -/
theorem digitO_ok (K : JacWinCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {k j N : Nat} (hj : 5 * j + 5 ≤ N) (hN : K.bits + N ≤ size)
    (hx : s.gpr .rbx = BitVec.ofNat 64 j)
    (hbits : ∀ t < N, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0) :
    WP isa (.block K.digitO) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (magO (Window5.nib k j)) ∧
      t.gpr .r8 = BitVec.ofNat 64 (magO (Window5.nib k j)) ∧ Keeps [.rax, .rcx, .rdx, .r8] s t := by
  have hn := hs.nowrap
  obtain hj32 : j < 2 ^ 64 := by omega_arith
  rw [JacWinCfg.digitO, List.append_assoc, WP.block_append_iff]
  refine WP.mono (winIndex_ok s (by decide) hj32 hx) fun a ⟨a1, ka⟩ => ?_
  rw [WP.block_append_iff]
  obtain hv : ∀ i, (fun t => (k.testBit (5 * j + (t - K.bits))).toNat) i ≤ 1 := fun _ => Bool.toNat_le _
  refine WP.mono (hornerBits_ok hv 5 K.bits (s := a) (by decide) fun i hi => ?_)
    fun b ⟨b2, kb⟩ => ?_
  · have he : a.ea (winByte (K.bits + i)) = off base (K.bits + (5 * j + i)) := by
      rw [ea_winByte ((ka.1 .rdi (by decide)).trans hs.rdi) a1]
      exact congrArg (off base) (by omega_arith)
    refine ⟨by rw [he]; exact ⟨_, List.mem_append_right _ (ka.2.2.2 ▸ hs.wr), hs.contains (by omega_arith) (by decide)⟩, ?_⟩
    rw [he, ka.2.1, hbits _ (by omega_arith), show K.bits + i - K.bits = i by omega_arith]
    cases k.testBit (5 * j + i) <;> rfl
  · have hw' : hornerVal (fun t => (k.testBit (5 * j + (t - K.bits))).toNat) K.bits 5 = Window5.nib k j := by
      have := hornerVal_eq k 5 j 5 (Nat.le_refl _)
      rw [Nat.sub_self, Nat.add_zero] at this
      rw [← Window5.combWin_five, combWin, ← this]
      exact hornerVal_congr fun i _ => by simp only [show K.bits + i - K.bits = i by omega_arith]
    refine WP.mono (magnitudeO_ok b (Window5.nib_lt k j) (by rw [b2, hw'])) fun t ⟨t1, t2, kt⟩ =>
      ⟨t1, t2, ((ka.mono (by decide)).trans (kb.mono (by decide))).trans (kt.mono (by decide))⟩

/-- The table of bits survives the method. -/
theorem JFrame.bitsO (hL : JacWinLay K size) {base : Addr} {s₀ s : State} {P : Point C} {k : Nat}
    (hF : JacWinFixedO K C base s₀ P k) (hf : JFrame K C base size s₀ s) :
    ∀ t < 5 * K.J, s.mem (off base (K.bits + t)) = if (OddWin.oq K.J k).testBit t then 1 else 0 := by
  intro t ht
  have hb := hL.bits
  have hn := hf.scr.nowrap
  rw [hf.unch.byte (fun w hw => by have := hL.bits_w w hw; omega_arith) (by omega_arith)]
  exact hF.bits t ht

/-- What `T` holds after the selection and the negation, from `s`: digit
`j`'s point with its powers. -/
structure JEntO (K : JacWinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ : State)
    (k j : Nat) (s t : State) : Prop where
  fr : JFrame K C base size s₀ t
  unch : Unch base ((List.range 5).map (fun c => (jg K (80 + c), 8 * K.M.n)) ++
    [(K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)]) s.mem t.mem
  keep : KeepRegs (clob K.M.n) s t
  ent : JPt C K.M.n base t (TS K) (OddWin.oddPt C P K.J k j)

/-- `T` holding entry `a = magO e` of digit `j`'s window `e`, its `Y` negated
for `e < 16`: `T` then holds digit `j`'s point with its powers. -/
theorem jnegO_ok (hL : JacWinLay K size) {base : Addr} {P : Point C} {s₀ : State} {k : Nat}
    (hF : JacWinFixedO K C base s₀ P k) {s₂ : State} {j : Nat} (hj : j < K.J)
    (F₂ : JFrame K C base size s₀ s₂) (hb : s₂.gpr .rbx = BitVec.ofNat 64 j)
    (T₂ : JPt C K.M.n base s₂ (TS K) (mul (2 * magO (Window5.nib (OddWin.oq K.J k) j) - 1) P)) :
    WP isa (.block K.tc.negY) s₂ fun s₅ => JFrame K C base size s₀ s₅ ∧
      Unch base [(K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n), (jg K 81, 8 * K.M.n)] s₂.mem s₅.mem ∧
      KeepRegs (clob K.M.n) s₂ s₅ ∧ JPt C K.M.n base s₅ (TS K) (OddWin.oddPt C P K.J k j) := by
  have hs₂ := F₂.scr
  have hn := hs₂.nowrap
  have hbl := hL.bits
  obtain hp0 : 0 < C.p := Nat.lt_of_le_of_lt (Nat.zero_le _) (hF.ro_lt K.P.x (by simp))
  obtain hbits := F₂.bitsO hL hF
  generalize hk' : OddWin.oq K.J k = k' at hbits T₂
  generalize ha : magO (Window5.nib k' j) = a at T₂
  obtain hwj : 5 * j + 5 ≤ 5 * K.J := by omega_arith
  obtain ⟨tx, ty, tz, t2, t3⟩ := hL.TS_eq
  obtain ⟨mx, my, mz, m2, m3⟩ := hL.T_mem
  obtain hneg : K.neg ∈ jwSlots K := by jw_mem
  obtain hzero : K.zero ∈ jwSlots K := by jw_mem
  obtain hz₂ : wordsVal s₂.mem base K.zero K.M.n = 0 := by rw [F₂.ro hL (by jw_mem)]; exact hF.zero
  obtain hy₂ : wordsVal s₂.mem base K.E.y K.M.n < C.p := by rw [← ty]; exact T₂.lt 1 (by decide)
  obtain hyneg : K.E.y + 8 * K.M.n ≤ K.neg ∨ K.neg + 8 * K.M.n ≤ K.E.y := by
    rw [hL.Ty]; exact (hL.jg_apart (x := K.neg) (by jw_mem) (by decide)).symm
  rw [TCombCfg.negY, List.append_assoc, WP.block_append_iff]
  refine WP.mono (sub_ok hs₂ F₂.mod (o := K.neg) (a := K.zero) (b := K.E.y) (hL.le hneg) (hL.le hzero)
    (hL.le my) (hL.lay.tmp _ hneg) (hL.lay.tmp _ hzero) (hL.lay.tmp _ my) (hL.lay.mo _ hneg)
    (by rw [hz₂]; exact hp0) hy₂) fun s₃ ⟨k₃, e₃⟩ => ?_
  obtain hs₃ := k₃.scr hs₂
  obtain hbits₃ : ∀ t < 5 * K.J, s₃.mem (off base (K.bits + t)) = if k'.testBit t then 1 else 0 := by
    intro t ht
    rw [k₃.unch.byte (fun w hw => by
      obtain hw' : w ∈ jwW K := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact mem_jwW_ws (other_ws (by jw_mem))
        · exact mem_jwW_tmp
      have := hL.bits_w w hw'; omega_arith) (by omega_arith)]
    exact hbits t ht
  rw [WP.block_append_iff]
  refine WP.mono (signMask_ok K.tc hs₃ (k := k') (j := j) (N := 5 * K.J) (by show 1 ≤ 5; decide)
    (by show 5 < 2 ^ 31; decide) hwj (by show K.bits + 5 * K.J ≤ size; omega_arith)
    (by rw [k₃.gpr _ (rbx_not_clob _), hb]) hbits₃) fun s₄ ⟨x₄, k₄⟩ => ?_
  obtain hs₄ := hs₃.of_keeps k₄ (by decide)
  obtain hwin : combWin K.tc.w k' j = Window5.nib k' j := Window5.combWin_five k' j
  rw [hwin] at x₄
  refine WP.mono (sel_ok (decide (Window5.nib k' j < 2 ^ (K.tc.w - 1))) K.M.n hs₄ x₄ (o := K.E.y)
    (a := K.E.y) (b := K.neg) (hL.le my) (hL.le my) (hL.le hneg) (Or.inl (Nat.le_refl _))
    (by omega_arith)) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  have m₄ : s₄.mem = s₃.mem := k₄.2.1
  obtain hs₅ := hs₄.of_keepRegs k₅ (by decide)
  obtain b64 : ∀ x ∈ jwSlots K, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by have := hL.le hx; omega_arith
  -- `T`'s words: as at `s₂` but `Y`.
  obtain keepT : ∀ c < 5, c ≠ 1 → wordsVal s₅.mem base (TS K c) K.M.n = wordsVal s₂.mem base (TS K c) K.M.n := by
    intro c hc h1
    obtain hy : TS K c + 8 * K.M.n ≤ K.E.y ∨ K.E.y + 8 * K.M.n ≤ TS K c := by
      rw [hL.Ty]; exact jg_sep K (by omega_arith)
    rw [O₅.wordsVal hy (b64 _ (jg_mem (by omega_arith))), m₄, k₃.unch.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact (hL.jg_apart (x := K.neg) (by jw_mem) (i := 80 + c) (by omega_arith)).symm
      · exact hL.lay.tmp _ (jg_mem (by omega_arith))) (b64 _ (jg_mem (by omega_arith)))]
  obtain y₃ : wordsVal s₃.mem base K.E.y K.M.n = wordsVal s₂.mem base K.E.y K.M.n :=
    k₃.unch.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hyneg
      · exact hL.lay.tmp _ my) (b64 _ my)
  obtain keepY : wordsVal s₅.mem base (TS K 1) K.M.n = if decide (Window5.nib k' j < 2 ^ (K.tc.w - 1)) then
      (0 + C.p - wordsVal s₂.mem base K.E.y K.M.n) % C.p else wordsVal s₂.mem base K.E.y K.M.n := by
    rw [ty, e₅, m₄, e₃, hz₂, y₃]
  have h16 : (2 : Nat) ^ (K.tc.w - 1) = 16 := rfl
  rw [h16] at keepY
  obtain hU : Unch base [(K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n), (jg K 81, 8 * K.M.n)] s₂.mem s₅.mem := by
    refine (k₃.unch.trans (m₄ ▸ O₅.unch)).mono fun w hw => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · rw [h, hL.Ty]; exact Or.inr (Or.inr rfl)
  obtain hcl : ∀ r ∈ [Reg.rax, .rcx, .rdx, .r8], r ∈ clob K.M.n := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simp [clob]
    · simp [clob]
    · simp [clob]
    · exact r8_mem_clob _
  obtain kk : KeepRegs (clob K.M.n) s₂ s₅ :=
    ((⟨k₃.gpr, k₃.rd, k₃.wr⟩ : KeepRegs (clob K.M.n) s₂ s₃).trans ((Keeps.regs k₄).mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h <;> simp [h]))).trans
      (k₅.mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h]))
  obtain tv : ∀ {x y : Nat}, wordsVal s₅.mem base x K.M.n = wordsVal s₂.mem base y K.M.n →
      tmv C K.M.n base s₅ x = tmv C K.M.n base s₂ y := fun h => by show toM _ _ _ = toM _ _ _; rw [h]
  obtain tz' : ∀ c < 5, c ≠ 1 → tmv C K.M.n base s₅ (TS K c) = tmv C K.M.n base s₂ (TS K c) :=
    fun c hc h1 => tv (keepT c hc h1)
  obtain hUL : Unch base (jwLoopW K) s₂.mem s₅.mem := hU.mono fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact List.mem_append_left _ (List.mem_map_of_mem (List.mem_append_left _ (by jw_mem)))
    · exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact T_loopW K (show 1 < 5 by decide)
  refine ⟨F₂.next hL hs₅ (kk.mono clob_powClob) hUL (jwLoopW_sub K), hU, kk, ?_⟩
  -- The point.
  obtain hoe : OddWin.oe K.J k j = Window5.nib k' j := by rw [← hk']; rfl
  rw [OddWin.oddPt, hoe]
  obtain hlt := Window5.nib_lt k' j
  obtain ha16 := magO_pos hlt
  rw [ha] at ha16
  by_cases hng : Window5.nib k' j < 16
  · have ha' : a = 16 - Window5.nib k' j := by
      rw [← ha, magO, ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith))]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith)), show 31 - 2 * Window5.nib k' j = 2 * a - 1 by omega_arith]
    simp only [decide_eq_true hng, ↓reduceIte] at keepY
    obtain hy : tmv C K.M.n base s₅ (TS K 1) = -tmv C K.M.n base s₂ (TS K 1) := by
      show toM _ _ _ = -toM _ _ _
      rw [keepY, toM_sub (by omega_arith), toM_zero, ty]
      grind
    refine ⟨fun c hc => ?_, ?_, ?_, ?_, ?_⟩
    · by_cases h1 : c = 1
      · subst h1; rw [keepY]; exact Nat.mod_lt _ hp0
      · rw [keepT c hc h1]; exact T₂.lt c hc
    · rw [tz' 0 (by decide) (by decide), tz' 2 (by decide) (by decide), hy]; exact T₂.jac.negY
    · rw [tz' 2 (by decide) (by decide)]; exact T₂.z
    · rw [tz' 3 (by decide) (by decide), tz' 2 (by decide) (by decide)]; exact T₂.z2
    · rw [tz' 4 (by decide) (by decide), tz' 3 (by decide) (by decide), tz' 2 (by decide) (by decide)]
      exact T₂.z3
  · have ha' : a = Window5.nib k' j - 15 := by
      rw [← ha, magO, ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith))]
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith)), show 2 * Window5.nib k' j - 31 = 2 * a - 1 by omega_arith]
    simp only [decide_eq_false hng, Bool.false_eq_true, ↓reduceIte] at keepY
    rw [← ty] at keepY
    exact T₂.congr fun c hc => by
      by_cases h1 : c = 1
      · subst h1; exact keepY
      · exact keepT c hc h1

/-- Digit `j`'s entry into `T`, negated for a negative digit. -/
theorem jentryO_ok (hL : JacWinLay K size) {base : Addr} {P : Point C} {s₀ : State} {k : Nat}
    (hF : JacWinFixedO K C base s₀ P k) {s : State} {j : Nat} (hj : j < K.J)
    (hf : JFrame K C base size s₀ s) (hT : JTblOkO K C base P 16 s) (hb : s.gpr .rbx = BitVec.ofNat 64 j) :
    WP isa (.block (K.digitO ++ K.select)) s fun s₂ =>
      WP isa (.block K.tc.negY) s₂ (JEntO K C base size P s₀ k j s) := by
  have hs := hf.scr
  have hn := hs.nowrap
  obtain hbits := hf.bitsO hL hF
  obtain hwj : 5 * j + 5 ≤ 5 * K.J := by omega_arith
  have hbl := hL.bits
  rw [WP.block_append_iff]
  refine WP.mono (digitO_ok K hs (k := OddWin.oq K.J k) (j := j) (N := 5 * K.J) hwj
    (by omega_arith) hb hbits) fun s₁ ⟨_, r₁, k₁⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  obtain ha16 := magO_pos (Window5.nib_lt (OddWin.oq K.J k) j)
  refine WP.mono (jselect_ok hL hs₁ r₁ ha16.2) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have m₁ : s₁.mem = s.mem := k₁.2.1
  rw [m₁] at e₂
  obtain U₂ : Unch base (jwLoopW K) s.mem s₂.mem := by
    rw [← m₁]; exact (outside_grid5 (b := 80) O₂).mono fun w hw => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw; exact T_loopW K (List.mem_range.mp hc)
  obtain F₂ := hf.next hL hs₂ (((Keeps.regs k₁).mono (sub_powClob (by decide))).trans
    (k₂.mono (sub_powClob (by decide)))) U₂ (jwLoopW_sub K)
  obtain e₂' : ∀ c < 5, wordsVal s₂.mem base (TS K c) K.M.n =
      wordsVal s.mem base (entS K (magO (Window5.nib (OddWin.oq K.J k) j)) c) K.M.n :=
    fun c hc => by rw [show TS K c = jg K (80 + c) from rfl, e₂ c hc, ite_eq_left_of_eq_true _ _ (eq_true ha16.1)]
  obtain T₂ := (hT _ ha16.1 ha16.2).congr fun c hc => e₂' c hc
  obtain hb₂ : s₂.gpr .rbx = BitVec.ofNat 64 j := by rw [k₂.gpr _ (by decide), k₁.1 _ (by decide), hb]
  refine WP.mono (jnegO_ok hL hF hj F₂ hb₂ T₂) fun s₅ ⟨F₅, U₅, kk₅, P₅⟩ => ⟨F₅, ?_, ?_, P₅⟩
  · rw [← m₁]
    refine ((outside_grid5 (b := 80) O₂).trans U₅).mono fun w hw => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · rw [h]; exact Or.inl (List.mem_map.mpr ⟨1, by decide, rfl⟩)
  · have hcl : ∀ r ∈ [Reg.rax, .rcx, .rdx, .r8], r ∈ clob K.M.n := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · simp [clob]
      · simp [clob]
      · simp [clob]
      · exact r8_mem_clob _
    exact (((Keeps.regs k₁).mono hcl).trans (k₂.mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h]))).trans kk₅

end VG.Proof.Weierstrass.X86_64

end

end

/-! ### `Weierstrass.X86_64.CachedJacIP`, which only this module used -/

section

/-!
# The cached Jacobian addition in place

`CachedJac.head n S p q dst ++ jacTail S p q p` adds `q` (with its `Z²` at
`dst` and `Z³` at `dst + 8 n`) to `p` in place: the head reads `p`, and the
tail never reads `p`'s `X` or `Y` again, and reads its `Z` before writing it.
On numbered slots (`ipσ`: the temporaries `0 … 5`, `p` at `6 … 8`, then what
it only reads) it computes `jacAddF` (`ip_values`), and so on any slots
apart as `ipσ` numbers them (`ip_run`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64.CachedJac
open VG VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Proof.Weierstrass

/-- The slots the addition in place writes: the temporaries and `p`. -/
def ipW (S : RcbSlots) (p : Pt) : List Nat := [S.t0, S.t1, S.t2, S.t3, S.t4, S.t5, p.x, p.y, p.z]

/-- The slots it only reads. -/
def ipR (n : Nat) (S : RcbSlots) (q : Pt) (dst : Nat) : List Nat := [S.a, S.b3, q.x, q.y, q.z, dst, dst + 8 * n]

/-- Slot `i` of the numbered program. -/
def ipσ (n : Nat) (S : RcbSlots) (p q : Pt) (dst i : Nat) : Nat := (ipW S p ++ ipR n S q dst).getD i S.a

/-- The head on numbered slots. -/
def headIPN : List FOp :=
  [.mul 0 8 8, .mul 2 6 14, .mul 3 11 0, .mul 4 7 15, .mul 5 12 8, .mul 5 5 0, .sub 3 3 2, .sub 5 5 4]

/-- The tail in place on numbered slots. -/
def tailIPN : List FOp := jacTail ⟨9, 10, 0, 1, 2, 3, 4, 5⟩ ⟨6, 7, 8⟩ ⟨11, 12, 13⟩ ⟨6, 7, 8⟩

theorem ip_eq (n : Nat) (S : RcbSlots) (p q : Pt) (dst : Nat) :
    Impl.Weierstrass.X86_64.CachedJac.head n S p q dst ++ jacTail S p q p =
      (headIPN ++ tailIPN).map (FOp.rename (ipσ n S p q dst)) := rfl

theorem ipN_out : ∀ op ∈ headIPN ++ tailIPN, op.out < 9 := by decide

theorem ip_values {F : Type _} [Lean.Grind.CommRing F] (E : Nat → F)
    (h2 : E 14 = E 13 * E 13) (h3 : E 15 = E 14 * E 13) :
    (runOps (headIPN ++ tailIPN) E 6, runOps (headIPN ++ tailIPN) E 7, runOps (headIPN ++ tailIPN) E 8) =
      jacAddF (E 6) (E 7) (E 8) (E 11) (E 12) (E 13) := by
  simp only [headIPN, tailIPN, jacTail, List.cons_append, List.nil_append,
    runOps, List.foldl_cons, List.foldl_nil, FOp.run, Function.update_apply]
  simp only [ite_true, h3, h2, jacAddF, Prod.mk.injEq]
  constructor
  · grind
  constructor <;> grind

/-- What `ip_run` needs of the slots: what is written has no duplicates, and
nothing only read (nor `S.a`, the default) is written. -/
structure IPApart (n : Nat) (S : RcbSlots) (p q : Pt) (dst : Nat) : Prop where
  nodup : (ipW S p).Nodup
  apart : ∀ x ∈ ipR n S q dst, x ∉ ipW S p

theorem ip_inj {n : Nat} {S : RcbSlots} {p q : Pt} {dst : Nat} (h : IPApart n S p q dst) {w : Nat}
    (hw : w < 9) (y : Nat) (hy : ipσ n S p q dst y = ipσ n S p q dst w) : y = w :=
  getD_append_inj h.nodup h.apart (h.apart _ (List.mem_cons_self ..)) hw y hy

/-- The addition in place computes `jacAddF`. -/
theorem ip_run {F : Type _} [Lean.Grind.CommRing F] {n : Nat} {S : RcbSlots} {p q : Pt} {dst : Nat}
    (hA : IPApart n S p q dst) (E : Nat → F) (h2 : E dst = E q.z * E q.z)
    (h3 : E (dst + 8 * n) = E dst * E q.z) :
    let ops := Impl.Weierstrass.X86_64.CachedJac.head n S p q dst ++ jacTail S p q p
    (runOps ops E p.x, runOps ops E p.y, runOps ops E p.z) =
      jacAddF (E p.x) (E p.y) (E p.z) (E q.x) (E q.y) (E q.z) := by
  dsimp only
  rw [ip_eq]
  have he := runOps_rename (ipσ n S p q dst) (headIPN ++ tailIPN) E
    (fun op hop => ip_inj hA (ipN_out op hop))
  exact (congrArg₂ Prod.mk (congrFun he 6) (congrArg₂ Prod.mk (congrFun he 7) (congrFun he 8))).trans
    (ip_values (fun i => E (ipσ n S p q dst i)) h2 h3)

theorem ipσ_mem (n : Nat) (S : RcbSlots) (p q : Pt) (dst i : Nat) :
    ipσ n S p q dst i ∈ ipW S p ++ ipR n S q dst :=
  getD_append_mem (List.mem_cons_self ..) i

theorem ipσ_out (n : Nat) (S : RcbSlots) (p q : Pt) (dst : Nat) {i : Nat} (hi : i < 9) :
    ipσ n S p q dst i ∈ ipW S p := by
  rw [ipσ, getD_append_left (by simp [ipW]; omega_using [hi])]
  exact List.getElem_mem _

end VG.Proof.Weierstrass.X86_64.CachedJac

end

end


/-!
# The odd window method on x86-64: an iteration

`JacWinCfg.stepO`: `rbx = j - 1`, `R = 32 R` (`dblsO_ok`), digit `j - 1`'s
entry in `T` (`jentryO_ok`), and `R = R + T` in place (`caddO_ok`): `R` then
represents `[S_{j-1}]P` for an odd `k < n` (`jstepO_point`), as no addition
is exceptional (`OddWin.loop_noexc`), and some point of the curve for any
`k` (`jstepO_pt`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

variable {K : JacWinCfg} {size : Nat} {C : Curve}

/-! ## The addition in place -/

/-- What `R = R + T` writes and reads are apart as `ipσ` numbers them. -/
theorem JacWinLay.ipApart (hL : JacWinLay K size) : CachedJac.IPApart K.M.n K.S K.R K.E K.z2 := by
  have hgW : ∀ c < 5, jg K (80 + c) ∉ rcbW K.S K.R := by
    intro c hc hw
    simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] at hw
    have g := fun x (hx : x ∈ jwOther K) => hL.jg_ne (List.mem_append_right _ hx) (i := 80 + c) (by omega_using [hc])
    rcases hw with h | h | h | h | h | h | h | h | h <;> exact g _ (by jw_mem) h.symm
  refine ⟨hL.rcbW_R, fun x hx => ?_⟩
  simp only [CachedJac.ipR, List.mem_cons, List.not_mem_nil, or_false] at hx
  show x ∉ rcbW K.S K.R
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro hw
    exact hL.ro K.S.a (by jw_mem) (by
      simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with h | h | h | h | h | h | h | h | h <;> rw [h] <;> jw_mem)
  · intro hw
    exact hL.ro K.S.b3 (by jw_mem) (by
      simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with h | h | h | h | h | h | h | h | h <;> rw [h] <;> jw_mem)
  · rw [hL.Tx]; exact hgW 0 (by decide)
  · rw [hL.Ty]; exact hgW 1 (by decide)
  · rw [hL.Tz]; exact hgW 2 (by decide)
  · rw [hL.Tz2]; exact hgW 3 (by decide)
  · rw [hL.Tz3]; exact hgW 4 (by decide)

/-- `R = R + T` in place, with `T`'s cached `Z²` and `Z³`. -/
theorem caddO_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {base : Addr}
    {V : List Nat} {E : Nat → Fe C} {s : State} (hI : Inv K.M base size C.p (· ∈ jwSlots K) V E s)
    (hV : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.z2, K.z2 + 8 * K.M.n], x ∈ V)
    (h2 : E K.z2 = E K.E.z * E K.E.z) (h3 : E (K.z2 + 8 * K.M.n) = E K.z2 * E K.E.z) :
    WP isa (ForwardField.programB K.M K.addOpsO).inline s fun t =>
      ProgKeep K.M base (rcbW K.S K.R) s t ∧ ∃ E' : Nat → Fe C,
        Inv K.M base size C.p (· ∈ jwSlots K) ([K.R.x, K.R.y, K.R.z] ++ V) E' t ∧
        (E' K.R.x, E' K.R.y, E' K.R.z) =
          jacAddF (E K.R.x) (E K.R.y) (E K.R.z) (E K.E.x) (E K.E.y) (E K.E.z) := by
  have hA := hL.ipApart
  have hSl : ∀ x ∈ CachedJac.ipW K.S K.R ++ CachedJac.ipR K.M.n K.S K.E K.z2, x ∈ jwSlots K := by
    intro x hx
    simp only [CachedJac.ipW, CachedJac.ipR, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rw [hL.Tz3, hL.Tx, hL.Ty, hL.Tz, hL.Tz2] at hx
    rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h]
    all_goals first
      | exact jg_mem (by decide) | jw_mem
  have hr : readsOk K.addOpsO V = true := by
    rw [JacWinCfg.addOpsO, CachedJac.ip_eq]
    refine readsOk_mono (readsOk_rename (CachedJac.ipσ K.M.n K.S K.R K.E K.z2)
      (show readsOk (CachedJac.headIPN ++ CachedJac.tailIPN) [6, 7, 8, 11, 12, 13, 14, 15] = true by decide))
      fun x hx => hV x ?_
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with h | h | h | h | h | h | h | h <;> rw [h] <;>
      simp [CachedJac.ipσ, CachedJac.ipW, CachedJac.ipR]
  have hs : ∀ op ∈ K.addOpsO, ∀ x ∈ op.out :: op.ins, x ∈ jwSlots K := by
    rw [JacWinCfg.addOpsO, CachedJac.ip_eq]
    intro op hop x hx
    obtain ⟨op', _, rfl⟩ := List.mem_map.mp hop
    refine hSl x ?_
    cases op' <;> simp only [FOp.rename, FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil,
      or_false] at hx <;> rcases hx with rfl | rfl | rfl <;> exact CachedJac.ipσ_mem ..
  refine WP.mono (ForwardField.programB_ok hL.lay hp _ hI hs hr) fun t ⟨kt, it⟩ =>
    ⟨kt.mono ?_, _, it.sub fun x hx => ?_, CachedJac.ip_run hA E h2 h3⟩
  · intro x hx
    obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hx
    rw [JacWinCfg.addOpsO, CachedJac.ip_eq] at hop
    obtain ⟨op', hop', rfl⟩ := List.mem_map.mp hop
    rw [FOp.out_rename]
    exact CachedJac.ipσ_out _ _ _ _ _ (CachedJac.ipN_out op' hop')
  · rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · right
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [JacWinCfg.addOpsO, jacTail, FOp.out]
    · exact Or.inl hx

/-! ## The point -/

/-- The iteration's sum for an odd `k < n`: a triple of `[S_i]P`. -/
theorem jstepO_point (hC : Law C) (hM3 : AM3 C) (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true)
    (hP0 : P ≠ .infinity) (hn2 : C.n % 2 = 1) (hn64 : C.n % 64 < 33) (hnb : 128 ≤ C.n) {k J i : Nat}
    (hk : k % 2 = 1) (hkn : k < C.n) (hi : i + 1 < J) {X1 Y1 Z1 X2 Y2 Z2 : Fe C}
    (h1 : InvJ C X1 Y1 Z1 (mul (32 * OddWin.oS J k (i + 1)) P))
    (h2 : InvJ C X2 Y2 Z2 (OddWin.oddPt C P J k i)) (z2 : Z2 ≠ 0) :
    InvJ C (jacAddF X1 Y1 Z1 X2 Y2 Z2).1 (jacAddF X1 Y1 Z1 X2 Y2 Z2).2.1 (jacAddF X1 Y1 Z1 X2 Y2 Z2).2.2
      (mul (OddWin.oS J k i) P) := by
  obtain ⟨ne0, ne1, ne2⟩ := OddWin.loop_noexc hC hO hP hP0 hn2 hn64 hnb hk hkn hi
  rw [← OddWin.win_add hC hP hk (by omega_using [hi])]
  have hQ := hC.onCurve_mul hP (32 * OddWin.oS J k (i + 1))
  have hW := OddWin.onCurve_oddPt hC hP J k i
  have hz : Z1 ≠ 0 := fun h => ne0 ((h1.z_zero_iff hC).mp h)
  have hh : X2 * (Z1 * Z1) - X1 * (Z2 * Z2) ≠ 0 := by
    intro hx
    by_cases hy : Y2 * Z1 * (Z1 * Z1) - Y1 * Z2 * (Z2 * Z2) = 0
    · exact ne1 (h1.same hC h2 hz z2 hx hy)
    · exact ne2 (h1.opposite hC hQ hW h2 hz z2 hx hy)
  exact h1.add_ne hC hM3 hQ hW h2 hz z2 hh

/-- The iteration's sum for any `k`: a triple of a point of the curve, which
is `[S_i]P` for an odd `k < n` (`jstepO_point`). Beyond it an addition may
be exceptional or start from `O`: then `Z = 0`, a triple of `O`. -/
theorem jstepO_pt (hC : Law C) (hM3 : AM3 C) (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true)
    (hP0 : P ≠ .infinity) (hn2 : C.n % 2 = 1) (hn64 : C.n % 64 < 33) (hnb : 128 ≤ C.n) {k J i : Nat}
    (hi : i + 1 < J) {X1 Y1 Z1 X2 Y2 Z2 : Fe C} {Q1 : Point C} (hQ1 : onCurve C Q1 = true)
    (hQ1e : k % 2 = 1 ∧ k < C.n → Q1 = mul (32 * OddWin.oS J k (i + 1)) P)
    (h1 : InvJ C X1 Y1 Z1 Q1) (h2 : InvJ C X2 Y2 Z2 (OddWin.oddPt C P J k i)) (z2 : Z2 ≠ 0) :
    ∃ Q : Point C, onCurve C Q = true ∧ (k % 2 = 1 ∧ k < C.n → Q = mul (OddWin.oS J k i) P) ∧
      InvJ C (jacAddF X1 Y1 Z1 X2 Y2 Z2).1 (jacAddF X1 Y1 Z1 X2 Y2 Z2).2.1
        (jacAddF X1 Y1 Z1 X2 Y2 Z2).2.2 Q := by
  by_cases hk : k % 2 = 1 ∧ k < C.n
  · refine ⟨_, hC.onCurve_mul hP _, fun _ => rfl, ?_⟩
    rw [hQ1e hk] at h1
    exact jstepO_point hC hM3 hO hP hP0 hn2 hn64 hnb hk.1 hk.2 hi h1 h2 z2
  have nk : ∀ Q : Point C, k % 2 = 1 ∧ k < C.n → Q = mul (OddWin.oS J k i) P := fun _ h' => absurd h' hk
  have hW := OddWin.onCurve_oddPt hC hP J k i
  have zO : (jacAddF X1 Y1 Z1 X2 Y2 Z2).2.2 = Z1 * Z2 * (X2 * (Z1 * Z1) - X1 * (Z2 * Z2)) := rfl
  by_cases hz : Z1 = 0
  · refine ⟨.infinity, rfl, nk _, Or.inl ⟨rfl, ?_⟩⟩
    rw [zO, hz]; grind
  · by_cases hh : X2 * (Z1 * Z1) - X1 * (Z2 * Z2) = 0
    · refine ⟨.infinity, rfl, nk _, Or.inl ⟨rfl, ?_⟩⟩
      rw [zO, hh]; grind
    · exact ⟨_, hC.onCurve_add hQ1 hW, nk _, h1.add_ne hC hM3 hQ1 hW h2 hz z2 hh⟩

end VG.Proof.Weierstrass.X86_64

end

end

/-!
# Scalar multiplication by odd 5-bit windows in Jacobian coordinates on x86-64

`JacWinCfg.windowO K dbl` (`Impl/Weierstrass/X86_64/WinJacOdd.lean`) leaves
`R` representing `[k]P` in projective coordinates (`winJacO_ok`), for an odd
`k < n`, `k ≤ 2 · 32^(J-1)`, on a curve of prime order `n` with
`n mod 64 < 33` (as P-256's), whose table at `K.bits` holds the bits of
`oq J k`, with any doubling `dbl` that doubles a Jacobian triple in place
(`DblOk`): the table `[1]P, [3]P, …, [31]P` (`jbuildO_ok`), `R = P` for the
top digit 1 (`jfirstO_ok`), and `J - 1` iterations `R = 32 R + [d_j]P`
(`jstepO_ok`), whose additions are never exceptional (`OddWin.loop_noexc`),
then `R = (XZ : Y : Z³)` with `Y = 1` for `O`. For any other `k` the code
runs the same way and writes the same places, and `R` is a triple of some
point of the curve.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

variable {K : JacWinCfg} {size : Nat} {C : Curve}

/-- The odd loop's invariant at `rbx = j`: `R` is a triple of a point of the
curve, `[S_j]P` for an odd `k < n`. -/
structure JInvO (K : JacWinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ : State)
    (k : Nat) (j : Nat) (s : State) : Prop where
  st : ∃ Q : Point C, onCurve C Q = true ∧
    (k % 2 = 1 ∧ k < C.n → Q = mul (OddWin.oS K.J k j) P) ∧ RStO K C base size P s₀ Q s
  rbx : s.gpr .rbx = BitVec.ofNat 64 j

/-- An iteration, `1 ≤ j < J`: `R = 32 R + [d_{j-1}]P`. -/
theorem jstepO_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C)
    (hO : PrimeOrder C) {dbl : Pt → Prog isa} (hD : DblOk K.M K.S C dbl) {P : Point C}
    (hP : onCurve C P = true) (hP0 : P ≠ .infinity) (hn2 : C.n % 2 = 1) (hn64 : C.n % 64 < 33)
    (hnb : 128 ≤ C.n) {base : Addr} {s₀ : State} {k : Nat} (hF : JacWinFixedO K C base s₀ P k) {j : Nat}
    (hj1 : 1 ≤ j) (hjJ : j < K.J) {s : State} (hI : JInvO K C base size P s₀ k j s) :
    WP isa (K.stepO dbl).inline s fun s' => JInvO K C base size P s₀ k (j - 1) s' ∧
      s'.zf = some (decide (j - 1 = 0)) := by
  obtain ⟨Q, hQ, hQe, R₀⟩ := hI.st
  have hn := R₀.fr.scr.nowrap
  have hJ := hL.J
  obtain ⟨tx, ty, tz, t2, t3⟩ := hL.TS_eq
  obtain ⟨mx, my, mz, m2, m3⟩ := hL.T_mem
  rw [JacWinCfg.stepO]
  simp only [Code.inline]
  refine WP.seq (WP.mono (decRbx_ok s hj1 (by omega_arith) hI.rbx) fun s₁ ⟨b₁, k₁⟩ => ?_)
  obtain R₁ := R₀.rbxKeeps hL k₁
  rw [← mul_one_pt Q] at R₁
  refine WP.seq (WP.mono (dblsO_ok hL hC hD hQ (j := j - 1) (by omega_arith) b₁ R₁) fun s₂ ⟨R₂, b₂, _⟩ => ?_)
  refine WP.seq (WP.mono (jentryO_ok hL hF (j := j - 1) (by omega_arith) R₂.fr R₂.tbl b₂) fun s₃ h₃ =>
    WP.seq (WP.mono h₃ fun s₄ E₄ => ?_))
  -- `R` is not written by the entry.
  obtain hRe : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₄.mem base x K.M.n = wordsVal s₂.mem base x K.M.n := by
    intro x hx
    obtain hxo : x ∈ jwOther K := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl <;> jw_mem
    refine E₄.unch.wordsVal (fun w hw => ?_) (by have := hL.le (other_mem hxo); omega_arith)
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw
      exact hL.jg_apart (List.mem_append_right _ hxo) (by have := List.mem_range.mp hc; omega_arith)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact hL.ap_oth (i := 0) (j := 6) (by decide) (by decide) (by decide)
        · exact hL.ap_oth (i := 1) (j := 6) (by decide) (by decide) (by decide)
        · exact hL.ap_oth (i := 2) (j := 6) (by decide) (by decide) (by decide)
      · exact hL.lay.tmp x (other_mem hxo)
  obtain U₄ : Unch base (jwLoopW K) s₂.mem s₄.mem := E₄.unch.mono (jent_loopW K)
  -- `R = R + T`.
  obtain V₄ : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.z2, K.z2 + 8 * K.M.n],
      x ∈ jwSlots K ∧ wordsVal s₄.mem base x K.M.n < C.p := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by jw_mem, by rw [hRe _ (by simp)]; exact R₂.lt _ (by simp)⟩
    · exact ⟨by jw_mem, by rw [hRe _ (by simp)]; exact R₂.lt _ (by simp)⟩
    · exact ⟨by jw_mem, by rw [hRe _ (by simp)]; exact R₂.lt _ (by simp)⟩
    · exact ⟨mx, by rw [← tx]; exact E₄.ent.lt 0 (by decide)⟩
    · exact ⟨my, by rw [← ty]; exact E₄.ent.lt 1 (by decide)⟩
    · exact ⟨mz, by rw [← tz]; exact E₄.ent.lt 2 (by decide)⟩
    · exact ⟨m2, by rw [← t2]; exact E₄.ent.lt 3 (by decide)⟩
    · exact ⟨m3, by rw [← t3]; exact E₄.ent.lt 4 (by decide)⟩
  obtain I₄ : Inv K.M base size C.p (· ∈ jwSlots K) [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.z2,
      K.z2 + 8 * K.M.n] (tmv C K.M.n base s₄) s₄ :=
    ⟨E₄.fr.scr, E₄.fr.mod, fun x hx => (V₄ x hx).1, fun x hx => (V₄ x hx).2, fun _ _ => rfl⟩
  obtain h2 := E₄.ent.z2; have h3 := E₄.ent.z3
  rw [t2, tz] at h2; rw [t3, t2, tz] at h3
  refine WP.seq (WP.mono (caddO_ok hL hp I₄ (fun x hx => hx) h2 h3) fun s₅ ⟨k₅, E₅, I₅, v₅⟩ => ?_)
  obtain U₅ : Unch base (jwLoopW K) s₄.mem s₅.mem := k₅.loopW (rcbW_loopW (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact other_loopW (by jw_mem)))
  obtain F₅ := E₄.fr.next hL (k₅.scr E₄.fr.scr) k₅.regs U₅ (jwLoopW_sub K)
  obtain hb₅ : s₅.gpr .rbx = BitVec.ofNat 64 (j - 1) := by
    rw [k₅.gpr _ (rbx_not_clob _), E₄.keep.gpr _ (rbx_not_clob _), b₂]
  refine WP.mono (testRbx_ok s₅ (by omega_arith) hb₅) fun s₆ ⟨z₆, k₆⟩ => ?_
  have m₆ : s₆.mem = s₅.mem := k₆.2.1
  obtain F₆ := F₅.next hL (F₅.scr.of_keeps k₆ (by decide)) ((Keeps.regs k₆).mono (by simp)) (W := [])
    (by rw [m₆]; exact Unch.refl _ _ _) (by simp)
  obtain tR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], tmv C K.M.n base s₄ x = tmv C K.M.n base s₂ x := fun x hx => by
    show toM _ _ _ = toM _ _ _; rw [hRe x hx]
  rw [tR _ (by simp), tR _ (by simp), tR _ (by simp)] at v₅
  obtain Rv : ∀ x ∈ [K.R.x, K.R.y, K.R.z], tmv C K.M.n base s₆ x = E₅ x ∧
      wordsVal s₆.mem base x K.M.n < C.p := fun x hx => by
    obtain hm : x ∈ [K.R.x, K.R.y, K.R.z] ++ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.z2,
        K.z2 + 8 * K.M.n] := List.mem_append_left _ hx
    exact ⟨by show toM _ _ _ = _; rw [m₆]; exact I₅.val x hm, by rw [m₆]; exact I₅.lt x hm⟩
  obtain hR := jstepO_pt hC hM3 hO hP hP0 hn2 hn64 hnb (k := k) (i := j - 1) (J := K.J) (by omega_arith)
    (hC.onCurve_mul hQ 32) (fun hk => by
      rw [hQe hk, Window5.mul_mul hC hP, show j - 1 + 1 = j by omega_arith]) R₂.rep
    (Z2 := tmv C K.M.n base s₄ K.E.z) (X2 := tmv C K.M.n base s₄ K.E.x) (Y2 := tmv C K.M.n base s₄ K.E.y)
    (by have J := E₄.ent.jac; rw [tx, ty, tz] at J; exact J) (by have J := E₄.ent.z; rw [tz] at J; exact J)
  obtain ⟨Q', hQ', hQe', hR⟩ := hR
  obtain vx := congrArg Prod.fst v₅
  obtain vy := congrArg (fun p => p.2.1) v₅
  obtain vz := congrArg (fun p => p.2.2) v₅
  dsimp only at vx vy vz
  refine ⟨⟨⟨Q', hQ', hQe', F₆,
    ((R₂.tbl.loopW hL U₄ hn (by decide)).loopW hL U₅ hn (by decide)).loopW hL
      (by rw [m₆]; exact Unch.refl _ _ _) hn (by decide),
    fun x hx => (Rv x hx).2, ?_⟩, by rw [k₆.1 _ (by simp), hb₅]⟩, z₆⟩
  rw [(Rv _ (by simp)).1, (Rv _ (by simp)).1, (Rv _ (by simp)).1, vx, vy, vz]
  exact hR

/-- `rbx = J - 1` and `R = P`: a triple of `[S_{J-1}]P = [1]P`. -/
theorem jfirstO_ok (hL : JacWinLay K size) {base : Addr} {P : Point C} (hP : onCurve C P = true)
    {s₀ s : State} {k : Nat} (hF : JacWinFixedO K C base s₀ P k) (hJ1 : 1 ≤ K.J)
    (hkJ : k ≤ 2 * 32 ^ (K.J - 1)) (hf : JFrame K C base size s₀ s) (hT : JTblOkO K C base P 16 s) :
    WP isa (.block K.firstO) s fun t => JInvO K C base size P s₀ k (K.J - 1) t := by
  have hn := hf.scr.nowrap
  have hJ := hL.J
  rw [JacWinCfg.firstO, WP.block_append_iff]
  refine WP.mono (mov32Rbx_ok s (j := K.J - 1) (by omega_arith)) fun s₁ ⟨b₁, k₁⟩ => ?_
  obtain hs₁ := hf.scr.of_keeps k₁ (by decide)
  have m₁ : s₁.mem = s.mem := k₁.2.1
  obtain F₁ := hf.next hL hs₁ ((Keeps.regs k₁).mono (sub_powClob (by decide))) (W := [])
    (by rw [m₁]; exact Unch.refl _ _ _) (by simp)
  obtain hR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ jwOther K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> jw_mem
  obtain hPro : ∀ x ∈ [K.P.x, K.P.y, K.P.z], x ∈ jwRo K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> jw_mem
  obtain hRP : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.P.x, K.P.y, K.P.z], x ∈ jwSlots K := by
    intro x hx
    rcases List.mem_append.mp (show x ∈ [K.R.x, K.R.y, K.R.z] ++ [K.P.x, K.P.y, K.P.z] by simpa using hx)
      with hx | hx
    · exact other_mem (hR x hx)
    · exact ro_mem (hPro x hx)
  obtain hne : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∉ [K.P.x, K.P.y, K.P.z] := fun x hx hy =>
    hL.ro x (hPro x hy) (List.mem_append_left _ (hR x hx))
  obtain o := fun i j hi hj h => hL.oth_ne (K := K) (i := i) (j := j) hi hj h
  refine WP.mono (copyPt_ok hs₁ (n := K.M.n) (o := K.R) (a := K.P) (fun x hx => hL.le (hRP x hx))
    (fun x hx y hy hxy => hL.ap (hRP x (List.mem_append_left [K.P.x, K.P.y, K.P.z] hx)) (hRP y hy) hxy) hne
    ⟨o 0 1 (by decide) (by decide) (by decide), o 0 2 (by decide) (by decide) (by decide),
      o 1 2 (by decide) (by decide) (by decide)⟩) fun s₂ ⟨ex, ey, ez, k₂, U₂⟩ => ?_
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  obtain UL : Unch base (jwLoopW K) s₁.mem s₂.mem := U₂.mono fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> exact other_loopW (hR _ (by simp))
  obtain F₂ := F₁.next hL hs₂ (k₂.mono (sub_powClob (by decide))) UL (jwLoopW_sub K)
  obtain T₁ : JTblOkO K C base P 16 s₁ := fun m h1 hm => (hT m h1 hm).congr fun c _ => by rw [m₁]
  obtain tv : ∀ {x y : Nat}, wordsVal s₂.mem base x K.M.n = wordsVal s₁.mem base y K.M.n →
      tmv C K.M.n base s₂ x = tmv C K.M.n base s₁ y := fun h => by show toM _ _ _ = toM _ _ _; rw [h]
  obtain J₁ := hF.jac hL F₁
  obtain lt₁ := hF.lt hL F₁
  obtain hz : tmv C K.M.n base s₁ K.P.z = 1 := by rw [F₁.ro_tmv hL (by jw_mem)]; exact hF.pz
  refine ⟨⟨P, hP, fun hk => ?_, ⟨F₂, T₁.loopW hL UL hn (by decide), fun x hx => ?_, ?_⟩⟩,
    by rw [k₂.gpr _ (by decide), b₁]⟩
  · rw [(OddWin.oe_top hk.1 hJ1 hkJ).2, mul_one_pt]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [ex]; exact lt₁ _ (by simp)
    · rw [ey]; exact lt₁ _ (by simp)
    · rw [ez]; exact lt₁ _ (by simp)
  · rw [tv ex, tv ey, tv ez, hz]; exact J₁

/-- The end of the window method, from `rbx = 0`: `R = (XZ : Y : Z³)` with
`Y = 1` for `O`, a triple of `[k]P` for an odd `k < n`. -/
theorem jfinO_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C)
    (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p) (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1)
    {P : Point C} {k : Nat} {base : Addr} {s s₃ : State}
    (hF : JacWinFixedO K C base s P k) (I₃ : JInvO K C base size P s k 0 s₃) :
    WP isa (Code.seq (.block K.tc.outFix) (ForwardField.programB K.M K.tc.outOps).inline) s₃ fun s' =>
      KeepRegs (powClob K.M.n) s s' ∧
      Unch base (jwW K) s.mem s'.mem ∧ ModOkW K.M size C.p s'.mem base ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      (k % 2 = 1 ∧ k < C.n → Rep C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y)
        (tmv C K.M.n base s' K.R.z) (mul k P)) := by
  have hJ := hL.J
  obtain ⟨Q, -, hQe', R₃⟩ := I₃.st
  obtain hQe : k % 2 = 1 ∧ k < C.n → Q = mul k P := fun hk => by
    rw [hQe' hk, OddWin.oS_zero hk.1 (by omega_arith)]
  -- `Y = 1` where `Z = 0`.
  have hs₃ := R₃.fr.scr
  have hn := hs₃.nowrap
  obtain hz₃ : wordsVal s₃.mem base K.zero K.M.n = 0 := by rw [R₃.fr.ro hL (by jw_mem)]; exact hF.zero
  obtain ayz : K.R.y + 8 * K.M.n ≤ K.zero ∨ K.zero + 8 * K.M.n ≤ K.R.y :=
    hL.ap (by jw_mem) (by jw_mem) (fun e => hL.ro K.zero (by jw_mem) (by rw [← e]; jw_mem))
  refine WP.seq (WP.mono (outFix_ok K.tc hs₃ hL.n0 (Nat.lt_trans hone_lt hpn)
    (show K.R.y + 8 * K.M.n ≤ size from hL.le (by jw_mem)) (show K.R.z + 8 * K.M.n ≤ size from hL.le (by jw_mem))
    (show K.zero + 8 * K.M.n ≤ size from hL.le (by jw_mem)) ayz hz₃) fun s₄ ⟨ey₄', k₄, O₄'⟩ => ?_)
  have ey₄ : wordsVal s₄.mem base K.R.y K.M.n = if wordsVal s₃.mem base K.R.z K.M.n = 0 then K.one
      else wordsVal s₃.mem base K.R.y K.M.n := ey₄'
  have O₄ : Outside base K.R.y (8 * K.M.n) s₃.mem s₄.mem := O₄'
  obtain hs₄ := hs₃.of_keepRegs k₄ (by decide)
  obtain b64 : ∀ x ∈ jwSlots K, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by have := hL.le hx; omega_arith
  obtain ex₄ : wordsVal s₄.mem base K.R.x K.M.n = wordsVal s₃.mem base K.R.x K.M.n :=
    O₄.wordsVal (hL.ap_oth (i := 0) (j := 1) (by decide) (by decide) (by decide)) (b64 _ (by jw_mem))
  obtain ez₄ : wordsVal s₄.mem base K.R.z K.M.n = wordsVal s₃.mem base K.R.z K.M.n :=
    O₄.wordsVal (hL.ap_oth (i := 2) (j := 1) (by decide) (by decide) (by decide)) (b64 _ (by jw_mem))
  obtain U₄ : Unch base (jwLoopW K) s₃.mem s₄.mem := O₄.unch.mono fun w hw => by
    rw [List.mem_singleton.mp hw]; exact other_loopW (by jw_mem)
  obtain F₄ := R₃.fr.next hL hs₄ (k₄.mono (sub_powClob (by decide))) U₄ (jwLoopW_sub K)
  obtain hlt₄ : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₄.mem base x K.M.n < C.p := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [ex₄]; exact R₃.lt _ (by simp)
    · rw [ey₄]; split
      · exact hone_lt
      · exact R₃.lt _ (by simp)
    · rw [ez₄]; exact R₃.lt _ (by simp)
  obtain hSlR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ jwSlots K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> jw_mem
  obtain I₄ : Inv K.M base size C.p (· ∈ jwSlots K) [K.R.x, K.R.y, K.R.z] (tmv C K.M.n base s₄) s₄ :=
    ⟨hs₄, F₄.mod, hSlR, hlt₄, fun _ _ => rfl⟩
  obtain hS : ∀ op ∈ K.tc.outOps, ∀ x ∈ op.out :: op.ins, x ∈ jwSlots K := by
    intro op hop x hx
    simp only [TCombCfg.outOps, JacWinCfg.tc, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl <;>
      simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false] at hx <;>
      rcases hx with rfl | rfl | rfl <;> jw_mem
  obtain hR : readsOk K.tc.outOps [K.R.x, K.R.y, K.R.z] = true := by
    simp [readsOk, TCombCfg.outOps, FOp.ins, FOp.out, JacWinCfg.tc]
  refine WP.mono (ForwardField.programB_ok hL.lay hp _ I₄ hS hR) fun s₅ ⟨P₅, I₅⟩ => ?_
  obtain hval : ∀ x ∈ [K.R.x, K.R.y, K.R.z], toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₅.mem base x K.M.n) =
      runOps K.tc.outOps (tmv C K.M.n base s₄) x ∧ wordsVal s₅.mem base x K.M.n < C.p := fun x hx => by
    obtain hm : x ∈ validAfter K.tc.outOps [K.R.x, K.R.y, K.R.z] := (mem_validAfter _ _).mpr (Or.inl hx)
    exact ⟨I₅.val x hm, I₅.lt x hm⟩
  obtain U₅ : Unch base (jwLoopW K) s₄.mem s₅.mem := P₅.loopW (by
    intro x hx
    simp only [TCombCfg.outOps, JacWinCfg.tc, FOp.out, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact other_loopW (by jw_mem))
  obtain F₅ := F₄.next hL (P₅.scr hs₄) P₅.regs U₅ (jwLoopW_sub K)
  refine ⟨F₅.keep, F₅.unch, F₅.mod, fun x hx => (hval x hx).2, fun hk => ?_⟩
  obtain e : ∀ x ∈ [K.R.x, K.R.y, K.R.z], tmv C K.M.n base s₅ x = runOps K.tc.outOps (tmv C K.M.n base s₄) x :=
    fun x hx => (hval x hx).1
  rw [e _ (by simp), e _ (by simp), e _ (by simp)]
  obtain hxt : K.R.x ≠ K.S.t0 := hL.oth_ne (i := 0) (j := 7) (by decide) (by decide) (by decide)
  obtain hzt : K.R.z ≠ K.S.t0 := hL.oth_ne (i := 2) (j := 7) (by decide) (by decide) (by decide)
  obtain hxz : K.R.x ≠ K.R.z := hL.oth_ne (i := 0) (j := 2) (by decide) (by decide) (by decide)
  obtain hxy : K.R.x ≠ K.R.y := hL.oth_ne (i := 0) (j := 1) (by decide) (by decide) (by decide)
  obtain hyt : K.R.y ≠ K.S.t0 := hL.oth_ne (i := 1) (j := 7) (by decide) (by decide) (by decide)
  obtain hyz : K.R.y ≠ K.R.z := hL.oth_ne (i := 1) (j := 2) (by decide) (by decide) (by decide)
  simp only [TCombCfg.outOps, JacWinCfg.tc, runOps, List.foldl_cons, List.foldl_nil, FOp.run,
    Function.update_apply, hxt, hzt, hxz, hyt, hyz, hxz.symm, hxt.symm, hxy.symm, ite_true, ite_false]
  obtain hy : tmv C K.M.n base s₄ K.R.y = if tmv C K.M.n base s₃ K.R.z = 0 then 1
      else tmv C K.M.n base s₃ K.R.y := by
    show toM _ _ _ = _
    rw [ey₄]
    by_cases h : wordsVal s₃.mem base K.R.z K.M.n = 0
    · have h' : tmv C K.M.n base s₃ K.R.z = 0 := by show toM _ _ _ = 0; rw [h]; exact toM_zero _ _
      simp only [h, h', ↓reduceIte]; exact hone
    · have h' : tmv C K.M.n base s₃ K.R.z ≠ 0 := fun h0 =>
        h ((toM_eq_zero_iff hp (R₃.lt _ (by simp))).mp h0)
      simp only [h, h', ↓reduceIte]
  obtain ex : tmv C K.M.n base s₄ K.R.x = tmv C K.M.n base s₃ K.R.x := by
    show toM _ _ _ = toM _ _ _; rw [ex₄]
  obtain ez : tmv C K.M.n base s₄ K.R.z = tmv C K.M.n base s₃ K.R.z := by
    show toM _ _ _ = toM _ _ _; rw [ez₄]
  rw [hy, ex, ez, ← hQe hk]
  exact InvJ.out hC R₃.rep


/-- `[k]P` into `R`, in projective coordinates, for `k` whose `oq J k` is the
table of bits at `K.bits`, if `k` is odd and below `n`; only `powClob` and
`jwW` change. -/
theorem winJacO_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C)
    (hM3 : AM3 C) (hO : PrimeOrder C) {dbl : Pt → Prog isa} (hD : DblOk K.M K.S C dbl)
    (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p) (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1)
    (hn2 : C.n % 2 = 1) (hn64 : C.n % 64 < 33) (hnb : 128 ≤ C.n) {P : Point C} (hP : onCurve C P = true)
    {k : Nat} (hkJ : k ≤ 2 * 32 ^ (K.J - 1)) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkW K.M size C.p s.mem base) (hF : JacWinFixedO K C base s P k) :
    WP isa (K.windowO dbl).inline s fun s' => KeepRegs (powClob K.M.n) s s' ∧
      Unch base (jwW K) s.mem s'.mem ∧ ModOkW K.M size C.p s'.mem base ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      (k % 2 = 1 ∧ k < C.n → Rep C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y)
        (tmv C K.M.n base s' K.R.z) (mul k P)) := by
  have hn := hs.nowrap
  have hJ := hL.J
  obtain hP0 := hF.ne_infinity hC
  rw [JacWinCfg.windowO]
  simp only [Code.inline]
  refine WP.seq (WP.mono (jbuildO_ok hL hp hC hM3 hO hP hP0 (by omega_arith) hs hM hF.toJacWinPt)
    fun s₁ ⟨F₁, T₁⟩ => ?_)
  refine WP.seq (WP.mono (jfirstO_ok hL hP hF (by omega_arith) hkJ F₁ T₁) fun s₂ I₂ => ?_)
  refine WP.seq (WP.mono (countLoop_ok (Q := fun t => JInvO K C base size P s k 0 t)
    (Inv := fun j t => JInvO K C base size P s k j t) (n := K.J - 1)
    (fun j t h1 h2 hi => jstepO_ok hL hp hC hM3 hO hD hP hP0 hn2 hn64 hnb hF h1 (by omega_arith) hi)
    (fun _ h => h) (by omega_arith) I₂) fun s₃ I₃ => ?_)
  exact jfinO_ok hL hp hC hpn hone_lt hone hF I₃

end VG.Proof.Weierstrass.X86_64
