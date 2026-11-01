module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacOddState
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacBuild
public import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacOdd
import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacStore
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacState
import VerifiedGarbage.Proof.Weierstrass.X86_64.Unch
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
import VerifiedGarbage.Proof.Weierstrass.WinJacMath
import VerifiedGarbage.Proof.Framework.Block

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
  have o := fun i j hi hj h => hL.oth_ne (K := K) (i := i) (j := j) hi hj h
  have hPs : ∀ x ∈ [K.P.x, K.P.y, K.P.z], x ∈ jwSlots K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact ro_mem (by jw_mem)
  have I0 : Inv K.M base size C.p (· ∈ jwSlots K) [K.P.x, K.P.y, K.P.z] (tmv C K.M.n base s) s :=
    ⟨hs, hI.fr.mod, hPs, hF.lt hL hI.fr, fun _ _ => rfl⟩
  rw [dblu_eq]
  refine WP.mono (tblProg_ok hL hp dbluN_out dbluN_reads I0 (fun i hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · rw [σ13]; simp
    · rw [σ14]; simp
    · rw [σ15]; simp)) fun s₁ ⟨k₁, I₁, v₁⟩ => ?_
  have F₁ := hI.fr.next hL (k₁.scr hs) k₁.regs (k₁.loopW (tblW_loopW hL)) (jwLoopW_sub K)
  have val := fun {i : Nat} (h : i ∈ dbluN.map FOp.out) => tbl_val I₁ v₁ h
  -- The points.
  have h15 : tmv C K.M.n base s (tblσ K 15) = 1 := by rw [σ15, hI.fr.ro_tmv hL (by jw_mem)]; exact hF.pz
  obtain ⟨hT, h11, h12, h5, h4⟩ := dbluN_run (fun y => tmv C K.M.n base s (tblσ K y)) h15
  generalize runOps dbluN (fun y => tmv C K.M.n base s (tblσ K y)) = r at val hT h11 h12 h5 h4
  have JP := hF.jac hL hI.fr
  rw [← σ13, ← σ14] at JP
  have J2 := InvJ.dbl' hC hM3 hP JP hT
  rw [show Spec.Weierstrass.add P P = mul 2 P by
    rw [show Spec.Weierstrass.add P P = Spec.Weierstrass.add (mul 1 P) (mul 1 P) by rw [mul_one_pt],
      hC.add_mul_mul hP]] at J2
  have hz : r 10 ≠ 0 := fun h =>
    Window5.mul_ne_infinity hO hP hP0 (m := 2) (by decide) (by omega_arith) ((J2.z_zero_iff hC).mp h)
  have JD : InvJ C (r 5) (r 4) (r 10) P := JP.rescale hC hz hC.one_ne_zero h5 h4 (by grind)
  -- The values at `s₁`.
  have v4 := val (i := 4) (by decide); have v5 := val (i := 5) (by decide)
  have v8 := val (i := 8) (by decide); have v9 := val (i := 9) (by decide)
  have v10 := val (i := 10) (by decide); have v11 := val (i := 11) (by decide)
  have v12 := val (i := 12) (by decide)
  rw [σ4] at v4; rw [σ5] at v5; rw [σ8] at v8; rw [σ9] at v9; rw [σ10] at v10; rw [σ11] at v11
  rw [σ12] at v12
  have I₁' : Inv K.M base size C.p (· ∈ jwSlots K) [K.S.t2, K.S.t3, K.E.x, K.E.y, K.E.z, K.z2,
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
  have hs₂ := k₂.scr F₁.scr; have hs₃ := k₃.scr hs₂; have hs₄ := k₄.scr hs₃; have hs₅ := k₅.scr hs₄
  have F₅ := (((F₁.next hL hs₂ k₂.regs (k₂.loopW (other_loopW (by jw_mem))) (jwLoopW_sub K)).next hL
    hs₃ k₃.regs (k₃.loopW (other_loopW (by jw_mem))) (jwLoopW_sub K)).next hL
    hs₄ k₄.regs (k₄.loopW hL.T_lw.1) (jwLoopW_sub K)).next hL
    hs₅ k₅.regs (k₅.loopW hL.T_lw.2.1) (jwLoopW_sub K)
  -- The slots apart.
  have gx : ∀ x ∈ jwOther K, ∀ c < 5, jg K (80 + c) ≠ x := fun x hx c hc e =>
    hL.jg_ne (List.mem_append_right _ hx) (i := 80 + c) (by omega_arith) e.symm
  have dxEx : K.D.x ≠ K.E.x := by rw [hL.Tx]; exact (gx _ (by jw_mem) 0 (by decide)).symm
  have dxEy : K.D.x ≠ K.E.y := by rw [hL.Ty]; exact (gx _ (by jw_mem) 1 (by decide)).symm
  have dyEx : K.D.y ≠ K.E.x := by rw [hL.Tx]; exact (gx _ (by jw_mem) 0 (by decide)).symm
  have dyEy : K.D.y ≠ K.E.y := by rw [hL.Ty]; exact (gx _ (by jw_mem) 1 (by decide)).symm
  have dyx : K.D.y ≠ K.D.x := o 4 3 (by decide) (by decide) (by decide)
  have t3Ex : K.S.t3 ≠ K.E.x := by rw [hL.Tx]; exact (gx _ (by jw_mem) 0 (by decide)).symm
  have t2Ex : K.S.t2 ≠ K.E.x := by rw [hL.Tx]; exact (gx _ (by jw_mem) 0 (by decide)).symm
  have t2Ey : K.S.t2 ≠ K.E.y := by rw [hL.Ty]; exact (gx _ (by jw_mem) 1 (by decide)).symm
  have t3dx : K.S.t3 ≠ K.D.x := o 10 3 (by decide) (by decide) (by decide)
  have t3dy : K.S.t3 ≠ K.D.y := o 10 4 (by decide) (by decide) (by decide)
  have t2dx : K.S.t2 ≠ K.D.x := o 9 3 (by decide) (by decide) (by decide)
  have t2dy : K.S.t2 ≠ K.D.y := o 9 4 (by decide) (by decide) (by decide)
  have ExEy : K.E.x ≠ K.E.y := (jw_T_ne hL).1
  have jne : ∀ {i j : Nat}, i ≠ j → jg K i ≠ jg K j := fun h e => by
    have := jg_apart K h; rw [e] at this; have := hL.n0; omega_arith
  have hT4 : ∀ c, 2 ≤ c → c < 5 → TS K c ≠ K.D.x ∧ TS K c ≠ K.D.y ∧ TS K c ≠ K.E.x ∧ TS K c ≠ K.E.y :=
    fun c h2 hc => ⟨gx _ (by jw_mem) c hc, gx _ (by jw_mem) c hc,
      by rw [hL.Tx]; exact jne (by omega_arith), by rw [hL.Ty]; exact jne (by omega_arith)⟩
  -- The values at `s₅`.
  have val₅ := fun x (hx : x ∈ K.E.y :: K.E.x :: K.D.y :: K.D.x :: [K.S.t2, K.S.t3, K.E.x, K.E.y, K.E.z,
      K.z2, K.z2 + 8 * K.M.n]) =>
    And.intro (show tmv C K.M.n base s₅ x = _ from I₅.val x hx) (I₅.lt x hx)
  have dx₅ := val₅ K.D.x (by simp)
  rw [Function.update_of_ne dxEy, Function.update_of_ne dxEx, Function.update_of_ne dyx.symm,
    Function.update_self] at dx₅
  have dy₅ := val₅ K.D.y (by simp)
  rw [Function.update_of_ne dyEy, Function.update_of_ne dyEx, Function.update_self,
    Function.update_of_ne dxEy.symm] at dy₅
  have ex₅ := val₅ K.E.x (by simp)
  rw [Function.update_of_ne ExEy, Function.update_self, Function.update_of_ne t3dy,
    Function.update_of_ne t3dx] at ex₅
  have ey₅ := val₅ K.E.y (by simp)
  rw [Function.update_self, Function.update_of_ne t2Ex, Function.update_of_ne t2dy,
    Function.update_of_ne t2dx] at ey₅
  have eT : ∀ c, 2 ≤ c → c < 5 → tmv C K.M.n base s₅ (TS K c) = tmv C K.M.n base s₁ (TS K c) ∧
      wordsVal s₅.mem base (TS K c) K.M.n < C.p := fun c h2 hc => by
    have hx : TS K c ∈ K.E.y :: K.E.x :: K.D.y :: K.D.x :: [K.S.t2, K.S.t3, K.E.x, K.E.y, K.E.z,
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
  have e2 := eT 2 (by decide) (by decide); have e3 := eT 3 (by decide) (by decide)
  have e4 := eT 4 (by decide) (by decide)
  rw [tz] at e2; rw [t2] at e3; rw [t3] at e4
  -- `T = P` with `Z = Z(2P)`.
  have J₅ : JPt C K.M.n base s₅ (TS K) (mul (2 * 1 - 1) P) := by
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
  have T₅ : JTblOkO K C base P 1 s₅ := by
    have T₁ := (hI.tbl.loopW hL (k₁.loopW (tblW_loopW hL)) hn (by decide))
    have U : Unch base (jwLoopW K) s₁.mem s₅.mem :=
      (((k₂.loopW (other_loopW (by jw_mem))).trans (k₃.loopW (other_loopW (by jw_mem)))).trans
        ((k₄.loopW hL.T_lw.1).trans (k₅.loopW hL.T_lw.2.1))).mono fun w hw => by
          simp only [List.mem_append] at hw; rcases hw with ((h | h) | (h | h)) <;> exact h
    intro m h1 hm
    obtain rfl : m = 1 := by omega_arith
    exact ((T₁.loopW hL U hn (by decide)) 1 (Nat.le_refl _) (Nat.le_refl _))
  have hb : s₅.gpr .rbx = BitVec.ofNat 64 1 := by
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
  have hx' : X1 * (Z * Z) - X2 * (Z * Z) = 0 := by
    have e : X1 * (Z * Z) - X2 * (Z * Z) = (X1 - X2) * (Z * Z) := by grind
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
  have hs₁ := hs.of_keeps k₁ (by decide)
  have m₁ : s₁.mem = s.mem := k₁.2.1
  have F₁ := hI.fr.next hL hs₁ ((Keeps.regs k₁).mono (sub_powClob (by decide))) (W := [])
    (by rw [m₁]; exact Unch.refl _ _ _) (by simp)
  have tv₁ : ∀ x, tmv C K.M.n base s₁ x = tmv C K.M.n base s x := fun x => by
    show toM _ _ _ = toM _ _ _; rw [m₁]
  obtain ⟨mx, my, mz, m2, -⟩ := hL.T_mem
  have I₁ : Inv K.M base size C.p (· ∈ jwSlots K) [K.D.x, K.D.y, K.E.x, K.E.y, K.E.z, K.z2]
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
  have F₂ := F₁.next hL (k₂.scr hs₁) k₂.regs (k₂.loopW (tblW_loopW hL)) (jwLoopW_sub K)
  have val := fun {i : Nat} (h : i ∈ zadduN.map FOp.out) => tbl_val I₂ v₂ h
  obtain ⟨hZ, h11, h12⟩ := zadduN_run (fun y => tmv C K.M.n base s₁ (tblσ K y))
  generalize runOps zadduN (fun y => tmv C K.M.n base s₁ (tblσ K y)) = r at val hZ h11 h12
  simp only [σ0, σ1, σ8, σ9, σ10, σ11, tv₁] at hZ h11
  -- The point.
  have JT : InvJ C (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z)
      (mul (2 * m - 1) P) := by
    rw [← tx, ← ty, ← tz]; exact hI.T.jac
  have hz : tmv C K.M.n base s K.E.z ≠ 0 := by rw [← tz]; exact hI.T.z
  have hx := zadduO_x hC hO hP hP0 hn h1 h15 hI.d JT hz
  obtain ⟨JS, JD⟩ := InvJ.zaddu hC hM3 (hC.onCurve_mul hP 2) (hC.onCurve_mul hP _) hI.d JT hz hx
  rw [← hZ] at JS JD
  rw [hC.add_mul_mul hP, show 2 * m - 1 + 2 = 2 * (m + 1) - 1 by omega_arith] at JS
  have h11' := h11 (by rw [← tz, ← t2]; exact hI.T.z2)
  have v0 := val (i := 0) (by decide); have v1 := val (i := 1) (by decide)
  have v8 := val (i := 8) (by decide); have v9 := val (i := 9) (by decide)
  have v10 := val (i := 10) (by decide); have v11 := val (i := 11) (by decide)
  have v12 := val (i := 12) (by decide)
  rw [σ0] at v0; rw [σ1] at v1; rw [σ8] at v8; rw [σ9] at v9; rw [σ10] at v10; rw [σ11] at v11
  rw [σ12] at v12
  have hm1 : mul (2 * (m + 1) - 1) P ≠ .infinity :=
    Window5.mul_ne_infinity hO hP hP0 (by omega_arith) (by omega_arith)
  have J₂ : JPt C K.M.n base s₂ (TS K) (mul (2 * (m + 1) - 1) P) := by
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
  have T₂ : JTblOkO K C base P m s₂ :=
    (hI.tbl.loopW hL (by rw [m₁]; exact Unch.refl _ _ _) hn' (by omega_arith)).loopW hL
      (k₂.loopW (tblW_loopW hL)) hn' (by omega_arith)
  -- The entry.
  have hb₂ : s₂.gpr .rbx = BitVec.ofNat 64 (m + 1) := by rw [k₂.gpr _ (rbx_not_clob _), b₁]
  rw [WP.block_append_iff]
  refine WP.mono (jstoreEntry_ok hL F₂.scr hb₂ (by omega_arith) (by omega_arith)) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have K₃ := dz_store hL (e := m + 1) (by omega_arith) (by omega_arith) O₃ hn'
  rw [Nat.add_sub_cancel] at e₃ O₃
  have hs₃ := F₂.scr.of_keepRegs k₃ (by decide)
  refine WP.mono (cmpRbxJ_ok s₃ (j := m + 1) (i := 16) (by decide) (by omega_arith)
    (by rw [k₃.gpr _ (by decide), hb₂])) fun s₄ ⟨z₄, k₄⟩ => ?_
  have m₄ : s₄.mem = s₃.mem := k₄.2.1
  have F₄ := (F₂.next hL hs₃ (k₃.mono (sub_powClob (by decide))) (outside_grid5 O₃)
    (grid5_jwW (by omega_arith))).next hL (hs₃.of_keeps k₄ (by decide)) ((Keeps.regs k₄).mono (by simp))
    (W := []) (by rw [m₄]; exact Unch.refl _ _ _) (by simp)
  have tv₄ : ∀ x ∈ [K.D.x, K.D.y, K.E.z], tmv C K.M.n base s₄ x = tmv C K.M.n base s₂ x := fun x hx => by
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
