module

-- separate module: its proofs (about 10 s, the window method's loop in vectors) are not checked again when `Proof/Ecdh/X86_64/VerifiedIfma.lean`'s literal or analyses change

public import VerifiedGarbage.Proof.P256.X86_64.Ifma.Window
public import VerifiedGarbage.Impl.P256.X86_64.Ifma.Ecdh
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacOddWin
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacOddStep
public import VerifiedGarbage.Proof.Weierstrass.OddWin
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacOddEntry
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacOddBuild
import VerifiedGarbage.Proof.Weierstrass.X86_64.Unch
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.Offset

/-!
# P-256 on x86-64 with AVX512_IFMA: the odd window method with the loop in vectors

`vwindowO_ok`: `vwindowO` computes what `JacWinCfg.windowO` does (`winJacO_ok`), writing the vectors'
part of the working space too.

The accumulator's triple `(4 xn, 4 un, 2 z)` is that of a point of the curve (`Ainv`), which is
`[S_j]P` for an odd scalar below `n`, as the window method's `R` is (`JInvO`): the blocks compute the
doubling's and the addition's formulas whatever the points (`dbl_ok`, `add_ok`), and those are the
sums where the window method's are (`jstepO_pt`).
-/

@[expose] public section

namespace VG.Proof.P256.X86_64.Ifma

open VG VG.X86_64 VG.Impl.P256.X86_64.Ifma
open Spec.Weierstrass VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Impl.Rsa.X86_64.CrtIfma (vreg)
open VG.Impl.Mont.X86_64 (sc)
open VG.Impl.Mont (Mod)

/-! ### The accumulator's point -/

/-- The accumulator's triple is that of `A`. -/
def Ainv (xn un z : Fe Cv) (A : Point Cv) : Prop := InvJ Cv (4 * xn) (4 * un) (2 * z) A

/-- A doubling. -/
theorem ainv_dbl (hC : Law Cv) (ha : AM3 Cv) {xn un z : Fe Cv} {A : Point Cv} (hA : onCurve Cv A = true)
    (h : Ainv xn un z A) : Ainv (fX3 xn un z) (fU xn un z) (fZ3 un z) (Spec.Weierstrass.add A A) := by
  have h' := InvJ.dbl hC ha hA h
  have e := dbl_jac xn un z
  simp only [Prod.mk.injEq] at e
  exact h'.rescale hC two_ne one_ne (by grind) (by grind) (by grind)

/-- The entry of the triple `(X, Y, Z)` of `B`, as the accumulator. -/
theorem ainv_set (hC : Law Cv) {X Y Z : Fe Cv} {B : Point Cv} (h : InvJ Cv X Y Z B) :
    Ainv (entQ X Y Z false 0 0 0).ex (entQ X Y Z false 0 0 0).ey (entQ X Y Z false 0 0 0).ez B := by
  obtain ⟨hi, hy⟩ := entQ_inv hC h false 0 0 0
  exact hi.rescale hC two_ne one_ne (by grind) (by rw [hy]; grind) (by grind)

/-- An entry's `Z` is not zero if its point's is not. -/
theorem entQ_ez_ne (hC : Law Cv) {X Y Z : Fe Cv} (hZ : Z ≠ 0) (neg : Bool) (xn un z : Fe Cv) :
    (entQ X Y Z neg xn un z).ez ≠ 0 := by
  have k16 := kapC16
  have h8 : (8 : Fe Cv) * kapC ≠ 0 := fun h8 =>
    one_ne (by rw [← k16, show (16 : Fe Cv) * kapC = 2 * (8 * kapC) by grind, h8]; grind)
  exact hC.mul_ne_zero h8 hZ

/-- An iteration's addition, of digit `i`'s point to the accumulator's, which is `[32 S_{i+1}]P` for
an odd scalar below `n`: the sum is `[S_i]P` then (`jstepO_pt`). -/
theorem ainv_stepO (hC : Law Cv) (ha : AM3 Cv) (hO : PrimeOrder Cv) {P : Point Cv} (hP : onCurve Cv P = true)
    (hP0 : P ≠ .infinity) (hn2 : Cv.n % 2 = 1) (hn64 : Cv.n % 64 < 33) (hnb : 128 ≤ Cv.n) {k J i : Nat}
    (hi : i + 1 < J) {xn un z X Y Z : Fe Cv} {Q1 : Point Cv} (hQ1 : onCurve Cv Q1 = true)
    (hQ1e : k % 2 = 1 ∧ k < Cv.n → Q1 = mul (32 * OddWin.oS J k (i + 1)) P) (h1 : Ainv xn un z Q1)
    (h2 : InvJ Cv X Y Z (OddWin.oddPt Cv P J k i)) (hZ : Z ≠ 0) :
    ∃ Q : Point Cv, onCurve Cv Q = true ∧ (k % 2 = 1 ∧ k < Cv.n → Q = mul (OddWin.oS J k i) P) ∧
      Ainv (entQ X Y Z false xn un z).X3 (entQ X Y Z false xn un z).Un (entQ X Y Z false xn un z).Z3 Q := by
  obtain ⟨he, hy⟩ := entQ_inv hC h2 false xn un z
  obtain ⟨Q, hQ, hQe, hj⟩ := jstepO_pt hC ha hO hP hP0 hn2 hn64 hnb hi hQ1 hQ1e h1 he
    (entQ_ez_ne hC hZ false xn un z)
  have e := add_jac (entQ X Y Z false xn un z) (2 * kapC * Y) hy (entQ_zz X Y Z false xn un z)
    (entQ_zzz X Y Z false xn un z)
  have hneg : (entQ X Y Z false xn un z).neg = false := rfl
  simp only [hneg, Bool.false_eq_true, ↓reduceIte] at e
  have hxn : (entQ X Y Z false xn un z).xn = xn := rfl
  have hun : (entQ X Y Z false xn un z).un = un := rfl
  have hz : (entQ X Y Z false xn un z).z = z := rfl
  rw [hxn, hun, hz] at e
  rw [e] at hj
  exact ⟨Q, hQ, hQe, hj.rescale hC one_ne two_ne (by grind) (by grind) (by grind)⟩

/-! ### The accumulator in the slots, across the selection -/

/-- The first twenty slots. -/
def slots20 : List Loc := (List.range 20).map .slot

/-- Field vector `j` of the first twenty slots. -/
abbrev slv (j : Nat) : F5 T := (leaves slots20).getD j zero5

theorem sv_chk : chkSegW 640 saveAcc stT stSeg slots20 = true := by decide +kernel

theorem sv_iv : ivWithin stB (segT stSeg stT) stBT = true := by decide +kernel

theorem sv_ov : ovOk stBT stBT [] = true := by decide +kernel

theorem ld_chk : chkSegW 640 loadAcc (leaves slots20) stSeg regs20 = true := by decide +kernel

theorem ld_iv : ivWithin (bndsOf slots20 stBT) (segT stSeg (leaves slots20)) stBT = true := by decide +kernel

/-- What is known of the accumulator goes with its limbs. -/
theorem AccOk.same {E E' : Env} {xs ys : List (F5 T)} (h : Same stBT E' ys E xs) {xn un z : Fin pN}
    (ha : AccOk E (xs.getD 0 zero5) (xs.getD 1 zero5) (xs.getD 2 zero5) (xs.getD 3 zero5) xn un z) :
    AccOk E' (ys.getD 0 zero5) (ys.getD 1 zero5) (ys.getD 2 zero5) (ys.getD 3 zero5) xn un z := by
  have e := h.vI (j := 0) (k := 0) (by decide) rfl
  exact ⟨by rw [e]; exact ha.ul, by rw [e]; exact ha.uh, by rw [e]; exact ha.du,
    h.car 1 1 (by decide) rfl rfl ha.zn, h.car 2 1 (by decide) rfl rfl ha.a, h.car 2 3 (by decide) rfl rfl ha.x,
    h.raw 3 1 (by decide) rfl rfl ha.aa, h.raw 3 3 (by decide) rfl rfl ha.xx⟩

/-- The accumulator into the slots. -/
theorem saveAcc_ok {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ stB) {xn un z : Fin pN}
    (h : AccOk (envOf s₀) (t5 0) (t5 5) (t5 10) (t5 15) xn un z) :
    WP isa (.block saveAcc) s₀ fun s =>
      Ctx par s ∧ KeptW 640 s₀ s ∧ EnvOK s (bndsOf slots20 stBT) ∧
        AccOk (envOf s) (slv 0) (slv 1) (slv 2) (slv 3) xn un z :=
  WP.mono (cut_step' sv_chk hc hB sv_iv sv_ov (rs := stT) rfl rfl (Nat.le_of_eq rfl) (fun _ _ hm => nomatch hm))
    fun _ ⟨c, k, b, hS⟩ => ⟨c, k, b, AccOk.same hS h⟩

/-- The accumulator from the slots. -/
theorem loadAcc_ok {s₀ : State} (hc : Ctx par s₀) (hB : EnvOK s₀ (bndsOf slots20 stBT)) {xn un z : Fin pN}
    (h : AccOk (envOf s₀) (slv 0) (slv 1) (slv 2) (slv 3) xn un z) :
    WP isa (.block loadAcc) s₀ fun s =>
      Ctx par s ∧ KeptW 640 s₀ s ∧ EnvOK s stB ∧ AccOk (envOf s) (t5 0) (t5 5) (t5 10) (t5 15) xn un z :=
  WP.mono (cut_step' ld_chk hc hB ld_iv sv_ov (rs := leaves slots20) rfl rfl (Nat.le_of_eq rfl)
    (fun _ _ hm => nomatch hm)) fun _ ⟨c, k, b, hS⟩ => ⟨c, k, b, AccOk.same hS h⟩

theorem slot_idx : ∀ n, n < 20 → uBase .rdi = false ∧
    (slotAt (slotOff n)).bind (fun i => locIdx slots20 (.slot i)) = some n := by decide

theorem stBT_lt : ∀ j k, k < 4 → ∀ b, stBT.get j k = some b → j < 4 := by
  intro j k hk b hb
  by_contra hj
  have e : stBT.getD j [] = [] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show stBT.length ≤ j by
      rw [show stBT.length = 4 from rfl]; omega_using [hj])]
    rfl
  rw [BT.get, e] at hb
  exact nomatch hb

theorem slots20_get {n : Nat} {l : Loc} (h : slots20[n]? = some l) : n < 20 ∧ l = .slot n := by
  simp only [slots20, List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨m, hm, rfl⟩ := h
  obtain ⟨hlt, e⟩ := List.getElem?_eq_some_iff.mp hm
  rw [List.length_range] at hlt
  rw [List.getElem_range] at e
  exact ⟨hlt, by rw [e]⟩

/-- What is known of the accumulator in the slots holds wherever the slots hold the same. -/
theorem slots_gap {a b : State} (hm : ∀ n, n < 20 → ∀ k, k < 4 → ints b (.slot n) k = ints a (.slot n) k)
    (hB : EnvOK a (bndsOf slots20 stBT)) {xn un z : Fin pN}
    (h : AccOk (envOf a) (slv 0) (slv 1) (slv 2) (slv 3) xn un z) :
    EnvOK b (bndsOf slots20 stBT) ∧ AccOk (envOf b) (slv 0) (slv 1) (slv 2) (slv 3) xn un z := by
  have hS : Same stBT (envOf b) (leaves slots20) (envOf a) (leaves slots20) := by
    intro j k bb hk hb i hi
    have hj := stBT_lt j k hk bb hb
    have hlen : 5 * j + 5 ≤ slots20.length := by simp only [slots20, List.length_map, List.length_range]; omega_using [hj]
    rw [tab_leaves b slots20 hi hlen, tab_leaves a slots20 hi hlen]
    have e : slots20.getD (5 * j + i) (.reg 0) = .slot (5 * j + i) := by
      simp only [slots20]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega_using [hi, hj])]
      rfl
    rw [e]
    exact hm _ (by omega_using [hi, hj]) k hk
  refine ⟨envOK_of fun n l hl k hk bb hb => ?_, AccOk.same hS h⟩
  obtain ⟨hn, rfl⟩ := slots20_get hl
  rw [hm n hn k hk]
  have hb' := hB.m .rdi (slotOff n) k hk
  obtain ⟨hu, hi⟩ := slot_idx n hn
  simp only [bndsOf, hu, Bool.false_eq_true, ite_false, ite_true, hi, bndAt, hb, Option.getD_some] at hb'
  exact hb'

/-! ### The vectors' part of the working space -/

theorem kb0 : 32 * poolLit.idxOf (K4.lanes (if false = true then 3 else 0)) + 32 ≤ 8 * par.cst.length := by
  decide +kernel

/-- The blocks may run with `rdi` moved by `EO`: their slots are above the window method's part of
the working space, and so are their constants, at `r10`; `rcx` and `rdx` are at an entry's words, and
`r9` at the mask of an entry that is not negated. -/
theorem ectx {t : State} {base : Addr} {size : Nat} (hwr : (⟨base, size⟩ : Region) ∈ t.wr)
    (hnw : base.toNat + size ≤ 2 ^ 64) (hsz : 8192 ≤ size) (hdi : t.gpr .rdi = base + BitVec.ofNat 64 EO)
    (h10 : t.gpr .r10 = base + BitVec.ofNat 64 EKB) {x₀ z₀ : Nat} (hcx : t.gpr .rcx = base + BitVec.ofNat 64 x₀)
    (hx₀ : x₀ + 96 ≤ 5504) (hdx : t.gpr .rdx = base + BitVec.ofNat 64 z₀) (hz₀ : z₀ + 64 ≤ 5504)
    (h9 : t.gpr .r9 = t.gpr .r10 + BitVec.ofNat 64 (32 * poolLit.idxOf (K4.lanes (if false = true then 3 else 0))))
    (hk : ∀ i, i < 220 → t.mem.readW (base + BitVec.ofNat 64 (EKB + 8 * i)) 64 = kwords.getD i 0) : Ctx par t := by
  have hlo : par.lo = 5056 := rfl
  have hwin : par.win = 5920 := rfl
  have hreg (d n : Nat) (hd : d + n ≤ size) (hn : 0 < n) :
      InRegions (t.rd ++ t.wr) (base + BitVec.ofNat 64 d) n :=
    ⟨⟨base, size⟩, List.mem_append_right _ hwr, Offset.contains_base base hd (by omega_using [hnw, hd, hn])⟩
  have k0 := kb0
  rw [par_cst_length] at k0
  refine ⟨fun d hd => ?_, by decide, fun b d _ _ hd => ?_, fun b d _ _ hd => ?_, fun d hd => ?_, fun d hd => ?_,
    fun i hi => ?_, by decide⟩
  · rw [hdi, Offset.add_add]
    exact ⟨⟨base, size⟩, hwr, Offset.contains_base base (by simp only [EO]; omega_using [hsz, hwin, hd]) (by simp only [EO]; omega_using [hwin, hd])⟩
  · by_cases h1 : b = .rcx
    · subst h1
      have hd' : d + 32 ≤ 96 := hd
      rw [hcx, Offset.add_add]; exact hreg _ _ (by omega_using [hsz, hx₀, hd']) (by decide)
    by_cases h2 : b = .rdx
    · subst h2
      have hd' : d + 32 ≤ 64 := hd
      rw [hdx, Offset.add_add]; exact hreg _ _ (by omega_using [hsz, hz₀, hd']) (by decide)
    by_cases h3 : b = .r9
    · subst h3
      have hd' : d + 32 ≤ 32 := hd
      rw [h9, h10, Offset.add_add, Offset.add_add]; exact hreg _ _ (by simp only [EKB]; omega_using [hsz, k0, hd']) (by decide)
    rw [lim_other h1 h2 h3] at hd; omega
  · rw [hdi, Offset.add_add, hlo, hwin]
    by_cases h1 : b = .rcx
    · subst h1
      have hd' : d + 32 ≤ 96 := hd
      rw [hcx, Offset.add_add]
      exact Offset.sep base (Or.inl (by simp only [EO]; omega_using [hx₀, hd'])) (by omega_using [hx₀, hd']) (by simp only [EO]; omega_using [])
    by_cases h2 : b = .rdx
    · subst h2
      have hd' : d + 32 ≤ 64 := hd
      rw [hdx, Offset.add_add]
      exact Offset.sep base (Or.inl (by simp only [EO]; omega_using [hz₀, hd'])) (by omega_using [hz₀, hd']) (by simp only [EO]; omega_using [])
    by_cases h3 : b = .r9
    · subst h3
      have hd' : d + 32 ≤ 32 := hd
      rw [h9, h10, Offset.add_add, Offset.add_add]
      exact Offset.sep base (Or.inr (by simp only [EO, EKB]; omega_using [])) (by simp only [EKB]; omega_using [k0, hd'])
        (by simp only [EO]; omega_using [])
    rw [lim_other h1 h2 h3] at hd; omega
  · rw [par_cst_length] at hd
    show InRegions _ (t.gpr .r10 + _) 32
    rw [h10, Offset.add_add]; exact hreg _ _ (by simp only [EKB]; omega_using [hsz, hd]) (by decide)
  · rw [par_cst_length] at hd
    show Mem.Sep (t.gpr .r10 + _) 32 _ _
    rw [h10, hdi, Offset.add_add, Offset.add_add, hlo, hwin]
    exact Offset.sep base (Or.inr (by simp only [EO, EKB]; omega_using [])) (by simp only [EKB]; omega_using [hd])
      (by simp only [EO]; omega_using [])
  · rw [par_cst_length] at hi
    show t.mem.readW (t.gpr .r10 + _) 64 = _
    rw [h10, Offset.add_add, hk i hi, kwords_eq, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getD_eq_getElem?_getD]
    cases par.cst[i]? <;> rfl

/-- An entry in `ymm20`–`ymm29`, not negated, from the words of a Jacobian triple at `rcx` and of its
`Z²` and `Z³` at `rdx`. -/
theorem eConv_ok {e : State} {base : Addr} {x₀ z₀ : Nat} (hc : Ctx par e) (hB : EnvOK e stB)
    (hcx : e.gpr .rcx = off base x₀) (hdx : e.gpr .rdx = off base z₀)
    (h9 : e.gpr .r9 = e.gpr .r10 + BitVec.ofNat 64 (32 * poolLit.idxOf (K4.lanes (if false = true then 3 else 0))))
    {X Y Z : Fin pN} (hx : toM pN (2 ^ 256) (wordsVal e.mem base (x₀ + 0) 4) = X)
    (hy : toM pN (2 ^ 256) (wordsVal e.mem base (x₀ + 32) 4) = Y)
    (hz : toM pN (2 ^ 256) (wordsVal e.mem base (x₀ + 64) 4) = Z)
    (hzz : toM pN (2 ^ 256) (wordsVal e.mem base (z₀ + 0) 4) = Z * Z)
    (hzzz : toM pN (2 ^ 256) (wordsVal e.mem base (z₀ + 32) 4) = Z * Z * Z) :
    WP isa (.block convQPieces.flatten) e fun t =>
      Ctx par t ∧ Kept e t ∧ EnvOK t addB ∧ SgnOk (envOf t) sgnT.l0 false ∧
        (∀ xn un z, AccOk (envOf e) (t5 0) (t5 5) (t5 10) (t5 15) xn un z →
          AccOk (envOf t) (t5 0) (t5 5) (t5 10) (t5 15) xn un z) ∧
        (∀ xn un z, EntOk (envOf t) (t5 20) (t5 25) (entQN X Y Z false xn un z)) := by
  refine WP.mono (convQ_ok hc hB) fun t ⟨hct, kt, hEt, hacc, c0, c1, c2, c3, cb⟩ => ?_
  have w (r : Reg) (hr : uBase r = true) (d x : Nat) (hx : e.gpr r = off base x) :
      wv (envOf e) (.ld r d) = (wordsVal e.mem base (x + d) 4 : Nat) := by
    rw [wv_ld e r hr d, hx, wordsVal_off]
  have t9 : t.gpr .r9 = t.gpr .r10 +
      BitVec.ofNat 64 (32 * poolLit.idxOf (K4.lanes (if false = true then 3 else 0))) := by
    rw [kt.gpr, h9]
  have hm := sgn_m hct false t9
  exact ⟨hct, kt, envOK_sgn hEt hm, sgnOk_of hm, hacc,
    fun xn un z => entOk_Q c0 c1 c2 c3 cb (w .rcx rfl 0 _ hcx) (w .rcx rfl 32 _ hcx) (w .rcx rfl 64 _ hcx)
      (w .rdx rfl 0 _ hdx) (w .rdx rfl 32 _ hdx) hx hy hz hzz hzzz _ xn un z⟩

/-! ### The window method's part of the working space -/

/-- Memory kept but in a range from an address `e` past `base`, as a range from `base`. -/
theorem unch_shift {base : Addr} {e lo n : Nat} {m m' : Mem} (he : lo + e + n ≤ 2 ^ 64)
    (h : Unch (base + BitVec.ofNat 64 e) [(lo, n)] m m') : Unch base [(lo + e, n)] m m' := by
  intro x hx
  apply h
  intro w hw
  rw [List.mem_singleton] at hw
  subst hw
  have hx' := hx (lo + e, n) (List.mem_singleton_self _)
  dsimp only at hx' ⊢
  simp only [ofs] at hx' ⊢
  have k1 := Offset.lt_iff x base (d := e) (n := lo) (by omega_using [he])
  have k2 := Offset.lt_iff x base (d := e) (n := lo + n) (by omega_using [he])
  have := (x - base).isLt
  by_cases h1 : (x - (base + BitVec.ofNat 64 e)).toNat < lo
  · exact Or.inl h1
  · by_cases h2 : (x - (base + BitVec.ofNat 64 e)).toNat < lo + n
    · have a := k2.mp h2
      have b : ¬(e ≤ (x - base).toNat ∧ (x - base).toNat < e + lo) := fun hh => h1 (k1.mpr hh)
      omega_using [hx', k1, k2]
    · exact Or.inr (by omega_using [hx', k1, k2, h1])

/-- What the vectors' code may write of the working space: MXCSR, its slots and its constants. -/
def eV : List (Nat × Nat) := [(5472, 2720)]

/-- The window method's working space leaves the vectors' part: what it reads and writes is below
`5472`, in a working space of `8192` bytes at least, for four words. -/
structure EVLay (K : JacWinCfg) (size : Nat) : Prop where
  lay : JacWinLay K size
  n4 : K.M.n = 4
  sz : 8192 ≤ size
  below : ∀ w ∈ jwW K, w.1 + w.2 ≤ 5472
  ro : ∀ x ∈ jwRo K, x + 32 ≤ 5472
  bits : K.bits + 5 * K.J ≤ 5472
  mo : K.M.mo + 32 ≤ 5472
  T : K.T + 160 ≤ 5472

/-- What the window method reads and never writes is kept where memory changes apart from it. -/
theorem fixedO_unch {K : JacWinCfg} {size : Nat} (hL : JacWinLay K size) {base : Addr} {s s' : State}
    {P : Point Cv} {k : Nat} (hF : JacWinFixedO K Cv base s P k) {W : List (Nat × Nat)}
    (hU : Unch base W s.mem s'.mem) (hn : base.toNat + size ≤ 2 ^ 64)
    (hro : ∀ x ∈ jwRo K, ∀ w ∈ W, x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x)
    (hb : ∀ w ∈ W, K.bits + 5 * K.J ≤ w.1 ∨ w.1 + w.2 ≤ K.bits) : JacWinFixedO K Cv base s' P k := by
  have ro : ∀ x ∈ jwRo K, wordsVal s'.mem base x K.M.n = wordsVal s.mem base x K.M.n := fun x hx =>
    hU.wordsVal (hro x hx) (by have := hL.le (ro_mem hx); omega_using [hn, this])
  have tv : ∀ x ∈ jwRo K, tmv Cv K.M.n base s' x = tmv Cv K.M.n base s x := fun x hx => by
    show toM _ _ _ = toM _ _ _; rw [ro x hx]
  refine ⟨⟨by rw [ro _ (by jw_mem)]; exact hF.zero, fun x hx => ?_, ?_, ?_⟩, fun t ht => ?_⟩
  · have hx' : x ∈ jwRo K := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> jw_mem
    rw [ro x hx']; exact hF.ro_lt x hx
  · rw [tv _ (by jw_mem), tv _ (by jw_mem), tv _ (by jw_mem)]; exact hF.pt
  · rw [tv _ (by jw_mem)]; exact hF.pz
  · have hbl := hL.bits
    rw [hU.byte (fun w hw => by have := hb w hw; omega_using [ht, this]) (by omega_using [hn, ht, hbl])]
    exact hF.bits t ht

/-- What the loop needs of memory, wherever `rdi` is: the working space, the modulus, what the window
method reads, its table, and the blocks' constants. -/
structure EMem (K : JacWinCfg) (base : Addr) (size : Nat) (P : Point Cv) (k : Nat) (t : State) : Prop where
  wr : (⟨base, size⟩ : Region) ∈ t.wr
  nw : base.toNat + size ≤ 2 ^ 64
  mod : ModOkW K.M size Cv.p t.mem base
  fix : JacWinFixedO K Cv base t P k
  tbl : JTblOkO K Cv base P 16 t
  pool : ∀ i, i < 220 → t.mem.readW (base + BitVec.ofNat 64 (EKB + 8 * i)) 64 = kwords.getD i 0

/-- The vectors' code keeps it: it writes only its slots and MXCSR's. -/
theorem EMem.vec {K : JacWinCfg} {size : Nat} (hV : EVLay K size) {base : Addr} {P : Point Cv} {k : Nat}
    {s t : State} (h : EMem K base size P k s) (hwr : t.wr = s.wr) {lo n : Nat} (hlo : 5472 ≤ lo)
    (hhi : lo + n ≤ 6400) (hU : Unch base [(lo, n)] s.mem t.mem) : EMem K base size P k t := by
  have hL := hV.lay
  have hn4 := hV.n4
  have hnw := h.nw
  have hsz := hV.sz
  refine ⟨hwr ▸ h.wr, hnw, h.mod.unch hU (fun w hw => ?_) hnw,
    fixedO_unch hL h.fix hU hnw (fun x hx w hw => ?_) (fun w hw => ?_),
    h.tbl.unch hL hU hnw (Nat.le_refl _) (fun w hw i hi => ?_), fun i hi => ?_⟩
  · rw [List.mem_singleton] at hw; subst hw
    have := hV.mo; rw [hn4]; dsimp only; omega_using [hlo, this]
  · rw [List.mem_singleton] at hw; subst hw
    have := hV.ro x hx; rw [hn4]; dsimp only; omega_using [hlo, this]
  · rw [List.mem_singleton] at hw; subst hw
    have := hV.bits; dsimp only; omega_using [hlo, this]
  · rw [List.mem_singleton] at hw; subst hw
    have := hV.below (jg K i, 8 * K.M.n) (mem_jwW_ws (jg_ws (by omega_using [hi])))
    dsimp only at this ⊢; omega_using [hlo, this]
  · have e : Mont.word t.mem base (EKB + 8 * i) = Mont.word s.mem base (EKB + 8 * i) :=
      hU.word (fun w hw => by
        rw [List.mem_singleton] at hw; subst hw
        dsimp only; simp only [EKB]; omega_using [hhi]) (by simp only [EKB]; omega_using [hi])
    exact e.trans (h.pool i hi)

/-! ### The loop's scalar instructions -/

section
open VG.Proof.X25519.X86_64 (Keeps)

/-- The iteration's counters. -/
theorem hdr_ok (s : State) {j : Nat} (hj : 1 ≤ j) (hj' : j < 2 ^ 64) (hb : s.gpr .rbx = BitVec.ofNat 64 j) :
    WP isa (.block [.alu .sub .rbx (.imm 1), .mov32 .r11 (.imm 5)]) s fun t =>
      (t.gpr .rbx = BitVec.ofNat 64 (j - 1) ∧ t.gpr .r11 = BitVec.ofNat 64 5) ∧ Keeps [.rbx, .r11] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32, State.setReg32,
    Option.bind_some, Option.map_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left', hb]
  refine ⟨⟨?_, rfl⟩, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e1 : (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 := by decide
    rw [e1]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt hj', Nat.mod_eq_of_lt (by omega_using [hj'] : j - 1 < 2 ^ 64)]
    omega_using [hj, hj']
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]

/-- The doublings' counter. -/
theorem decR11_ok (s : State) {i : Nat} (hi : 1 ≤ i) (hi' : i ≤ 5) (hb : s.gpr .r11 = BitVec.ofNat 64 i) :
    WP isa (.block [.alu .sub .r11 (.imm 1)]) s fun t =>
      (t.gpr .r11 = BitVec.ofNat 64 (i - 1) ∧ t.zf = some (decide (i - 1 = 0))) ∧ Keeps [.r11] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true, Option.some.injEq, exists_eq_left', hb]
  have e1 : (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 := by decide
  have e : BitVec.ofNat 64 i - BitVec.ofNat 64 1 = BitVec.ofNat 64 (i - 1) := by
    rcases (by omega_using [hi, hi'] : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl <;> decide
  rw [e1, e]
  refine ⟨⟨rfl, ?_⟩, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [RegUpd.zf_setReg, RegUpd.zf_arithFlags]
    rcases (by omega_using [hi, hi'] : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- `rdi` to the vectors' slots. -/
theorem adjUp_ok (s : State) :
    WP isa (.block adjUp) s fun t => t.gpr .rdi = s.gpr .rdi + BitVec.ofNat 64 EO ∧ Keeps [.rdi] s t := by
  apply WP.of_runBlock
  have e : (BitVec.ofNat 32 EO).signExtend 64 = BitVec.ofNat 64 EO := by decide
  simp only [adjUp, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true, Option.some.injEq, exists_eq_left', e]
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- `rdi` back to the working space. -/
theorem adjDn_ok (s : State) {base : Addr} (hdi : s.gpr .rdi = base + BitVec.ofNat 64 EO) :
    WP isa (.block adjDn) s fun t => t.gpr .rdi = base ∧ Keeps [.rdi] s t := by
  apply WP.of_runBlock
  have e : (BitVec.ofNat 32 EO).signExtend 64 = BitVec.ofNat 64 EO := by decide
  simp only [adjDn, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true, Option.some.injEq, exists_eq_left', e, hdi]
  refine ⟨BitVec.add_sub_cancel _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- The registers the blocks read through. -/
theorem ptrs_ok (s : State) {e z : Nat} (he : e < 2 ^ 31) (hz : z < 2 ^ 31) :
    WP isa (.block (ptrs e z)) s fun t =>
      (t.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 EKB ∧
        t.gpr .r9 = t.gpr .r10 + BitVec.ofNat 64 (32 * poolLit.idxOf (K4.lanes (if false = true then 3 else 0))) ∧
        t.gpr .rcx = s.gpr .rdi + BitVec.ofNat 64 e ∧ t.gpr .rdx = s.gpr .rdi + BitVec.ofNat 64 z) ∧
      Keeps [.r10, .r9, .rcx, .rdx] s t := by
  have ht : (BitVec.ofNat 32 (32 * poolLit.idxOf (K4.lanes 0))).signExtend 64 =
      BitVec.ofNat 64 (32 * poolLit.idxOf (K4.lanes 0)) := by decide +kernel
  have ek : (BitVec.ofNat 32 EKB).signExtend 64 = BitVec.ofNat 64 EKB := by decide
  apply WP.of_runBlock
  simp only [ptrs, signPtr, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, execAlu, imm32_sext he, imm32_sext hz, ek, ht, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    Option.map_some, Option.bind_some, ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left',
    Bool.false_eq_true]
  refine ⟨⟨trivial, trivial, trivial, trivial⟩, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

end

/-! ### The doublings -/

/-- Five doublings of the accumulator. -/
theorem vdbls_ok (hC : Law Cv) (ha : AM3 Cv) {s : State} (hc : Ctx par s) (hB : EnvOK s stB)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 5) {xn un z : Fin pN}
    (h : AccOk (envOf s) (t5 0) (t5 5) (t5 10) (t5 15) xn un z) {Q : Point Cv} (hQ : onCurve Cv Q = true) {e : Nat}
    (hA : Ainv xn un z (mul e Q)) :
    WP isa (.loop (.block (dblPieces.flatten ++ ([.alu .sub .r11 (.imm 1)] : List Instr))) .ne) s fun t =>
      Ctx par t ∧ EnvOK t stB ∧ LKeep s t ∧
        ∃ xn' un' z' : Fin pN, AccOk (envOf t) (t5 0) (t5 5) (t5 10) (t5 15) xn' un' z' ∧
          Ainv xn' un' z' (mul (32 * e) Q) := by
  refine countLoop_ok (n := 5) (Inv := fun i t => Ctx par t ∧ EnvOK t stB ∧ LKeep s t ∧
      t.gpr .r11 = BitVec.ofNat 64 i ∧ ∃ xn' un' z' : Fin pN,
        AccOk (envOf t) (t5 0) (t5 5) (t5 10) (t5 15) xn' un' z' ∧ Ainv xn' un' z' (mul (2 ^ (5 - i) * e) Q))
    (fun i a h1 h5 ⟨ca, ba, ka, ra, x1, u1, z1, ha1, pa⟩ => ?_)
    (fun t ⟨ct, bt, kt, _, x1, u1, z1, ha1, pa⟩ => ⟨ct, bt, kt, x1, u1, z1, ha1, pa⟩) (by decide)
    ⟨hc, hB, LKeep.refl s, h11, xn, un, z, h, by rw [show 2 ^ (5 - 5) * e = e by omega_using []]; exact hA⟩
  rw [WP.block_append_iff]
  refine WP.mono (dbl_ok ca ba ha1) fun b ⟨cb, kb, bb, hb⟩ => ?_
  refine WP.mono (WP.skeep rfl (decR11_ok b h1 h5 (by rw [kb.gpr]; exact ra))) fun t ⟨⟨rt, zt⟩, kt⟩ => ?_
  refine ⟨⟨ctx_skeep cb kt (by decide) (by decide) fun r d hr hd => ?_, envOK_skeep kt (by decide) bb,
    (ka.trans (LKeep.of_kept kb)).trans (LKeep.of_skeep kt), rt, _, _, _, hb.congr kt.v, ?_⟩, zt⟩
  · rw [List.mem_singleton] at hr
    subst hr
    rw [lim_other (by decide) (by decide) (by decide)] at hd
    omega
  · have hq := hC.onCurve_mul hQ (2 ^ (5 - i) * e)
    have := ainv_dbl hC ha hq pa
    rwa [hC.add_mul_mul hQ, show 2 ^ (5 - i) * e + 2 ^ (5 - i) * e = 2 ^ (5 - (i - 1)) * e by
      rw [show 5 - (i - 1) = 5 - i + 1 by omega_using [h1, h5], Nat.pow_succ]; grind] at this

/-- Five doublings of the accumulator, whose point is `[e]P` where `v` holds. -/
theorem vdbls_pt (hC : Law Cv) (ha : AM3 Cv) {s : State} (hc : Ctx par s) (hB : EnvOK s stB)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 5) {xn un z : Fin pN}
    (h : AccOk (envOf s) (t5 0) (t5 5) (t5 10) (t5 15) xn un z) {P Q : Point Cv} (hP : onCurve Cv P = true)
    (hQ : onCurve Cv Q = true) {v : Prop} {e : Nat} (hQe : v → Q = mul e P) (hA : Ainv xn un z Q) :
    WP isa (.loop (.block (dblPieces.flatten ++ ([.alu .sub .r11 (.imm 1)] : List Instr))) .ne) s fun t =>
      Ctx par t ∧ EnvOK t stB ∧ LKeep s t ∧
        ∃ (xn' un' z' : Fin pN) (Q' : Point Cv), AccOk (envOf t) (t5 0) (t5 5) (t5 10) (t5 15) xn' un' z' ∧
          onCurve Cv Q' = true ∧ (v → Q' = mul (32 * e) P) ∧ Ainv xn' un' z' Q' := by
  by_cases hv : v
  · have hA' : Ainv xn un z (mul e P) := by rw [← hQe hv]; exact hA
    exact WP.mono (vdbls_ok hC ha hc hB h11 h hP hA') fun t ⟨ct, bt, kt, x1, u1, z1, h1, p1⟩ =>
      ⟨ct, bt, kt, x1, u1, z1, _, h1, hC.onCurve_mul hP _, fun _ => rfl, p1⟩
  · have hA' : Ainv xn un z (mul 1 Q) := by rw [mul_one_pt]; exact hA
    exact WP.mono (vdbls_ok hC ha hc hB h11 h hQ hA') fun t ⟨ct, bt, kt, x1, u1, z1, h1, p1⟩ =>
      ⟨ct, bt, kt, x1, u1, z1, _, h1, hC.onCurve_mul hQ _, fun h' => absurd h' hv, p1⟩

/-! ### An iteration -/

/-- The vectors' slots, from the working space. -/
abbrev eS : Nat × Nat := (cfg.sbase + EO, 640)

/-- What the blocks keep of memory, from the working space. -/
theorem kept_unch {s t : State} {base : Addr} {w : Nat} (hdi : s.gpr .rdi = base + BitVec.ofNat 64 EO)
    (h : Unch (s.gpr .rdi) [(cfg.sbase, w)] s.mem t.mem) (hw : w ≤ 640 := by decide) : Unch base [eS] s.mem t.mem :=
  (unch_shift (by have : cfg.sbase = 5056 := rfl; simp only [EO]; omega_using [hw, this]) (hdi ▸ h)).cover fun x hx => by
    rw [List.mem_singleton] at hx; subst hx
    exact ⟨_, List.mem_singleton_self _, Nat.le_refl _, by dsimp only; omega_using [hw]⟩

/-- The loop's invariant at `rbx = j`, with `rdi` at the vectors' slots, from the state `s₀`: the
accumulator's triple is that of a point of the curve, `[S_j]P` for an odd scalar below `n`. -/
structure EInv (K : JacWinCfg) (base : Addr) (size : Nat) (P : Point Cv) (k : Nat) (s₀ : State) (j : Nat)
    (t : State) : Prop where
  mem : EMem K base size P k t
  ctx : Ctx par t
  env : EnvOK t stB
  rdi : t.gpr .rdi = base + BitVec.ofNat 64 EO
  rbx : t.gpr .rbx = BitVec.ofNat 64 j
  keep : ∀ r ∈ [Reg.rsi, .rsp, .r12], t.gpr r = s₀.gpr r
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  unch : Unch base (jwW K ++ eV) s₀.mem t.mem
  acc : ∃ (xn un z : Fin pN) (Q : Point Cv), AccOk (envOf t) (t5 0) (t5 5) (t5 10) (t5 15) xn un z ∧
    onCurve Cv Q = true ∧ (k % 2 = 1 ∧ k < Cv.n → Q = mul (OddWin.oS K.J k j) P) ∧ Ainv xn un z Q

/-- An iteration, `1 ≤ j < J`: five doublings and digit `j - 1`'s point added. -/
theorem vstepO_ok {K : JacWinCfg} {size : Nat} (hV : EVLay K size) (hC : Law Cv) (ha : AM3 Cv) (hO : PrimeOrder Cv)
    {P : Point Cv} (hP : onCurve Cv P = true) (hP0 : P ≠ .infinity) (hn2 : Cv.n % 2 = 1) (hn64 : Cv.n % 64 < 33)
    (hnb : 128 ≤ Cv.n)
    (h12a : ∀ i ∈ instrs (Code.block (C := Cond) (K.digitO ++ K.select)), Taint.clobbers i .r12 = false)
    (h12b : ∀ i ∈ instrs (Code.block (C := Cond) K.tc.negY), Taint.clobbers i .r12 = false)
    {base : Addr} {k : Nat} {s₀ : State} {j : Nat} (hj1 : 1 ≤ j) (hjJ : j < K.J) {s : State}
    (hI : EInv K base size P k s₀ j s) :
    WP isa (vstepO K) s fun t => EInv K base size P k s₀ (j - 1) t ∧ t.zf = some (decide (j - 1 = 0)) := by
  obtain ⟨xn, un, z, Q, hacc, hQ, hQe, hA⟩ := hI.acc
  have hL := hV.lay
  have hn4 := hV.n4
  have hJ := hL.J
  have hnw := hI.mem.nw
  have hsz := hV.sz
  have hT := hV.T
  obtain ⟨tx, ty, tz, t2, t3⟩ := hL.TS_eq
  have eEy : K.E.y = K.E.x + 32 := by show K.T + 8 * K.M.n = K.T + 32; rw [hn4]
  have eEz : K.E.z = K.E.x + 64 := by show K.T + 16 * K.M.n = K.T + 64; rw [hn4]
  have eZ2 : K.z2 = K.E.x + 96 := by show K.T + 24 * K.M.n = K.T + 96; rw [hn4]
  have eEx : K.E.x = K.T := rfl
  rw [vstepO]
  -- the counters
  apply WP.seq
  refine WP.mono (WP.skeep rfl (hdr_ok s hj1 (by omega_using [hjJ, hJ]) hI.rbx)) fun a ⟨⟨ab, a11⟩, ka⟩ => ?_
  have ca : Ctx par a := ctx_skeep hI.ctx ka (by decide) (by decide) fun r d hr hd => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (rw [lim_other (by decide) (by decide) (by decide)] at hd; omega)
  have adi : a.gpr .rdi = base + BitVec.ofNat 64 EO := (ka.gpr .rdi (by decide)).trans hI.rdi
  -- the doublings
  apply WP.seq
  refine WP.mono (vdbls_pt hC ha ca (envOK_skeep ka (by decide) hI.env) a11 (hacc.congr ka.v) hP hQ hQe hA)
    fun b ⟨cb, bb, kb, x1, u1, z1, Q1, hb, hQ1, hQ1e, pb⟩ => ?_
  have bdi : b.gpr .rdi = base + BitVec.ofNat 64 EO := (kb.gpr .rdi (by decide)).trans adi
  -- the accumulator into the slots, and `rdi` back
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (saveAcc_ok cb bb hb) fun c ⟨_, kc, bc, hc⟩ => ?_
  have cdi : c.gpr .rdi = base + BitVec.ofNat 64 EO := by rw [kc.gpr]; exact bdi
  refine WP.mono (adjDn_ok c cdi) fun d ⟨ddi, kd⟩ => ?_
  have Usd : Unch base [eS] s.mem d.mem := by
    rw [kd.2.1, ← ka.mem]
    exact ((kept_unch adi kb.mem).trans (kept_unch bdi kc.mem)).mono (by decide)
  have wsd : d.wr = s.wr := by rw [kd.2.2.2, kc.wr, kb.wr, ka.wr]
  have rsd : d.rd = s.rd := by rw [kd.2.2.1, kc.rd, kb.rd, ka.rd]
  have md : EMem K base size P k d := hI.mem.vec hV wsd (lo := eS.1) (n := eS.2) (by decide) (by decide) Usd
  have hsd : Scr d base size := ⟨ddi, md.wr, hnw⟩
  have gsd : ∀ r, r ∉ [Reg.rax, .rcx, .rdx, .rbp, .r8, .r9, .r11, .rbx, .rdi] → d.gpr r = s.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [kd.1 r (by simp [hr]), kc.gpr, kb.gpr r (by simp [hr]), ka.gpr r (by simp [hr])]
  have dbx : d.gpr .rbx = BitVec.ofNat 64 (j - 1) := by
    rw [kd.1 .rbx (by decide), kc.gpr, kb.gpr .rbx (by decide)]; exact ab
  -- the digit's entry
  apply WP.seq
  refine WP.mono (WP.gpr (jentryO_ok hL md.fix (j := j - 1) (by omega_using [hjJ]) (JFrame.refl hsd md.mod) md.tbl dbx) h12a)
    fun e ⟨he, e12⟩ => ?_
  apply WP.seq
  refine WP.mono (WP.gpr he h12b) fun f ⟨ent, f12⟩ => ?_
  have hsf := ent.fr.scr
  have ncl : ∀ r ∈ [Reg.rsi, .rsp, .rdi, .rbx], r ∉ clob K.M.n := by rw [hn4]; decide
  have fbx : f.gpr .rbx = BitVec.ofNat 64 (j - 1) := (ent.keep.gpr .rbx (ncl _ (by decide))).trans dbx
  have below : ∀ w ∈ jwW K, w.1 + w.2 ≤ 5472 := hV.below
  have mf : EMem K base size P k f := by
    refine ⟨hsf.wr, hnw, ent.fr.mod, fixedO_unch hL md.fix ent.fr.unch hnw (fun x hx => hL.ro_w hx) hL.bits_w,
      md.tbl.loopW hL (ent.unch.mono fun w hw => ?_) hnw (Nat.le_refl _), fun i hi => ?_⟩
    · simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with ⟨c', hc', rfl⟩ | rfl | rfl
      · exact T_loopW K hc'
      · exact other_loopW (by jw_mem)
      · exact tmp_loopW
    · have e' : Mont.word f.mem base (EKB + 8 * i) = Mont.word d.mem base (EKB + 8 * i) :=
        ent.fr.unch.word (fun w hw => by have := below w hw; simp only [EKB]; omega_using [this]) (by simp only [EKB]; omega_using [hi])
      exact e'.trans (md.pool i hi)
  -- the registers the blocks read through, and `rdi` to the slots
  rw [WP.block_append_iff]
  refine WP.mono (ptrs_ok f (e := K.E.x) (z := K.z2) (by omega_using [hT, eEx]) (by omega_using [hT, eZ2, eEx])) fun g ⟨⟨g10, g9, gcx, gdx⟩, kg⟩ => ?_
  rw [hsf.rdi] at g10 gcx gdx
  rw [WP.block_append_iff]
  refine WP.mono (adjUp_ok g) fun h ⟨hdi, kh⟩ => ?_
  rw [kg.1 .rdi (by decide), hsf.rdi] at hdi
  have hmem : h.mem = f.mem := kh.2.1.trans kg.2.1
  have ch : Ctx par h := ectx (by rw [kh.2.2.2, kg.2.2.2]; exact hsf.wr) hnw hsz hdi
    (by rw [kh.1 .r10 (by decide)]; exact g10) (x₀ := K.E.x) (by rw [kh.1 .rcx (by decide)]; exact gcx) (by omega_using [hT, eEx])
    (z₀ := K.z2) (by rw [kh.1 .rdx (by decide)]; exact gdx) (by omega_using [hT, eZ2, eEx])
    (by rw [kh.1 .r9 (by decide), kh.1 .r10 (by decide)]; exact g9)
    (fun i hi => by rw [hmem]; exact mf.pool i hi)
  have hm : ∀ n, n < 20 → ∀ k', k' < 4 → ints h (.slot n) k' = ints c (.slot n) k' := by
    intro n hn k' hk'
    show (h.mem.readW (h.gpr .rdi + BitVec.ofNat 64 (slotOff n + 8 * k')) 64).toInt =
      (c.mem.readW (c.gpr .rdi + BitVec.ofNat 64 (slotOff n + 8 * k')) 64).toInt
    rw [hdi, cdi, Offset.add_add, hmem, ← kd.2.1]
    have e' : Mont.word f.mem base (EO + (slotOff n + 8 * k')) = Mont.word d.mem base (EO + (slotOff n + 8 * k')) :=
      ent.fr.unch.word (fun w hw => by
        have := below w hw; simp only [EO, slotOff, show cfg.sbase = 5056 from rfl]; omega_using [this])
        (by simp only [EO, slotOff, show cfg.sbase = 5056 from rfl]; omega_using [hn, hk'])
    exact congrArg BitVec.toInt e'
  obtain ⟨bh, hh⟩ := slots_gap hm bc hc
  rw [WP.block_append_iff]
  refine WP.mono (loadAcc_ok ch bh hh) fun i ⟨ci, ki, bi, hi⟩ => ?_
  have idi : i.gpr .rdi = base + BitVec.ofNat 64 EO := by rw [ki.gpr]; exact hdi
  have Ufi : Unch base [eS] f.mem i.mem := by rw [← hmem]; exact kept_unch hdi ki.mem
  have wi (x : Nat) (hx : x + 32 ≤ 5472) : wordsVal i.mem base x 4 = wordsVal f.mem base x 4 :=
    Ufi.wordsVal (fun w hw => by
      rw [List.mem_singleton] at hw; subst hw
      exact Or.inl (by show x + 8 * 4 ≤ 5056 + 448; omega_using [hx])) (by omega_using [hx])
  have tm (x : Nat) : tmv Cv K.M.n base f x = toM pN (2 ^ 256) (wordsVal f.mem base x 4) := by rw [hn4]; rfl
  have jp := ent.ent
  rw [WP.block_append_iff]
  refine WP.mono (eConv_ok ci bi (x₀ := K.E.x) (z₀ := K.z2)
    (by rw [ki.gpr, kh.1 .rcx (by decide)]; exact gcx) (by rw [ki.gpr, kh.1 .rdx (by decide)]; exact gdx)
    (by rw [ki.gpr, kh.1 .r9 (by decide), kh.1 .r10 (by decide)]; exact g9)
    (X := tmv Cv K.M.n base f (TS K 0)) (Y := tmv Cv K.M.n base f (TS K 1)) (Z := tmv Cv K.M.n base f (TS K 2))
    (by rw [Nat.add_zero, wi _ (by omega_using [hT, eEx]), tm, tx])
    (by rw [wi _ (by omega_using [hT, eEx]), tm, ty, eEy])
    (by rw [wi _ (by omega_using [hT, eEx]), tm, tz, eEz])
    (by rw [Nat.add_zero, wi _ (by omega_using [hT, eZ2, eEx]), ← tm, ← t2]; exact jp.z2)
    (by rw [wi _ (by omega_using [hT, eZ2, eEx]), ← tm, show K.z2 + 32 = K.z2 + 8 * K.M.n by rw [hn4], ← t3, jp.z3, jp.z2]; rfl))
    fun l ⟨cl, kl, bl, sl, accl, entl⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (add_ok cl bl (p := entQN (tmv Cv K.M.n base f (TS K 0)) (tmv Cv K.M.n base f (TS K 1))
    (tmv Cv K.M.n base f (TS K 2)) false x1 u1 z1) (accl _ _ _ hi) (entl _ _ _) sl) fun m ⟨cm, km, bm, hm'⟩ => ?_
  refine WP.mono (WP.skeep rfl (test_ok m .rbx)) fun t ⟨tz', kt⟩ => ?_
  -- the frames
  have Uft : Unch base [eS] f.mem t.mem := by
    rw [kt.mem]
    have ldi : l.gpr .rdi = base + BitVec.ofNat 64 EO := by rw [kl.gpr]; exact idi
    exact ((Ufi.trans (kept_unch idi kl.mem)).trans (kept_unch ldi km.mem)).mono (by decide)
  have wft : t.wr = f.wr := by rw [kt.wr, km.wr, kl.wr, ki.wr, kh.2.2.2, kg.2.2.2]
  have rft : t.rd = f.rd := by rw [kt.rd, km.rd, kl.rd, ki.rd, kh.2.2.1, kg.2.2.1]
  have gft : ∀ r, r ∉ [Reg.r10, .r9, .rcx, .rdx, .rdi] → t.gpr r = f.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [kt.gpr r List.not_mem_nil, km.gpr, kl.gpr, ki.gpr, kh.1 r (by simp [hr]), kg.1 r (by simp [hr])]
  have tdi : t.gpr .rdi = base + BitVec.ofNat 64 EO := by
    rw [kt.gpr .rdi List.not_mem_nil, km.gpr, kl.gpr]; exact idi
  have tbx : t.gpr .rbx = BitVec.ofNat 64 (j - 1) := (gft .rbx (by decide)).trans fbx
  obtain ⟨Q', hQ', hQ'e, pQ'⟩ := ainv_stepO hC ha hO hP hP0 hn2 hn64 hnb (k := k) (J := K.J) (i := j - 1)
    (by omega_using [hj1, hjJ]) hQ1 (fun hv => by rw [hQ1e hv, show j - 1 + 1 = j by omega_using [hj1]]) pb jp.jac jp.z
  refine ⟨⟨mf.vec hV wft (lo := eS.1) (n := eS.2) (by decide) (by decide) Uft,
    ctx_skeep cm kt (by decide) (by decide) (fun _ _ hr => absurd hr List.not_mem_nil),
    envOK_skeep kt (by decide) bm, tdi, tbx, ?_, ?_, ?_, ?_, _, _, _, Q', hm'.congr kt.v, hQ', hQ'e, pQ'⟩, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [gft .rsi (by decide), ent.keep.gpr .rsi (ncl _ (by decide)), gsd .rsi (by decide)]
      exact hI.keep _ (by decide)
    · rw [gft .rsp (by decide), ent.keep.gpr .rsp (ncl _ (by decide)), gsd .rsp (by decide)]
      exact hI.keep _ (by decide)
    · rw [gft .r12 (by decide), f12, e12, gsd .r12 (by decide)]
      exact hI.keep _ (by decide)
  · rw [rft, ent.keep.rd, rsd]; exact hI.rd
  · rw [wft, ent.keep.wr, wsd]; exact hI.wr
  · refine (hI.unch.trans ((Usd.trans ent.fr.unch).trans Uft)).cover fun w hw => ?_
    simp only [List.mem_append, List.mem_singleton] at hw
    rcases hw with (hw | hw) | (rfl | hw) | rfl
    · exact ⟨w, List.mem_append_left _ hw, Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨w, List.mem_append_right _ hw, Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨(5472, 2720), List.mem_append_right _ (List.mem_singleton_self _), by decide, by decide⟩
    · exact ⟨w, List.mem_append_left _ hw, Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨(5472, 2720), List.mem_append_right _ (List.mem_singleton_self _), by decide, by decide⟩
  · rw [tz', (kt.gpr .rbx List.not_mem_nil).symm.trans tbx]
    have hlt : j - 1 < 2 ^ 64 := by omega_using [hjJ, hJ]
    by_cases h0 : j - 1 = 0
    · rw [h0]; rfl
    · simp only [h0, decide_false]
      congr 1
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro hz
      have := congrArg BitVec.toNat hz
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at this
      exact h0 this

/-! ### The loop -/

/-- What the window method needs of memory is kept where only the vectors' part changes. -/
theorem pre_unch {K : JacWinCfg} {size : Nat} (hV : EVLay K size) {base : Addr} {P : Point Cv} {k : Nat}
    {s t : State} (hM : ModOkW K.M size Cv.p s.mem base) (hF : JacWinFixedO K Cv base s P k)
    (hT : JTblOkO K Cv base P 16 s) (hnw : base.toNat + size ≤ 2 ^ 64) {lo n : Nat} (hlo : 5472 ≤ lo)
    (hU : Unch base [(lo, n)] s.mem t.mem) :
    ModOkW K.M size Cv.p t.mem base ∧ JacWinFixedO K Cv base t P k ∧ JTblOkO K Cv base P 16 t := by
  have hL := hV.lay
  have hn4 := hV.n4
  refine ⟨hM.unch hU (fun w hw => ?_) hnw,
    fixedO_unch hL hF hU hnw (fun x hx w hw => ?_) (fun w hw => ?_),
    hT.unch hL hU hnw (Nat.le_refl _) (fun w hw i hi => ?_)⟩
  · rw [List.mem_singleton] at hw; subst hw
    have := hV.mo; rw [hn4]; dsimp only; omega_using [hlo, this]
  · rw [List.mem_singleton] at hw; subst hw
    have := hV.ro x hx; rw [hn4]; dsimp only; omega_using [hlo, this]
  · rw [List.mem_singleton] at hw; subst hw
    have := hV.bits; dsimp only; omega_using [hlo, this]
  · rw [List.mem_singleton] at hw; subst hw
    have := hV.below (jg K i, 8 * K.M.n) (mem_jwW_ws (jg_ws (by omega_using [hi])))
    dsimp only at this ⊢; omega_using [hlo, this]

/-- Changes in the vectors' part of the working space. -/
theorem unch_vec (K : JacWinCfg) {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (h : Unch base W m m')
    (hW : ∀ w ∈ W, 5472 ≤ w.1 ∧ w.1 + w.2 ≤ 8192) : Unch base (jwW K ++ eV) m m' :=
  h.cover fun w hw => ⟨(5472, 2720), List.mem_append_right _ (List.mem_singleton_self _), (hW w hw).1, (hW w hw).2⟩

theorem unch_jw {K : JacWinCfg} {base : Addr} {m m' : Mem} (h : Unch base (jwW K) m m') :
    Unch base (jwW K ++ eV) m m' := h.mono fun _ hw => List.mem_append_left _ hw

theorem eU_trans {K : JacWinCfg} {base : Addr} {a b c : Mem} (h₁ : Unch base (jwW K ++ eV) a b)
    (h₂ : Unch base (jwW K ++ eV) b c) : Unch base (jwW K ++ eV) a c :=
  (h₁.trans h₂).mono fun _ hw => (List.mem_append.mp hw).elim id id

/-- The loop's start: the constants, and the table's first entry, `P`, as the accumulator. -/
theorem vinitO_ok {K : JacWinCfg} {size : Nat} (hV : EVLay K size) (hC : Law Cv) {P : Point Cv}
    (hP : onCurve Cv P = true) {base : Addr} {k : Nat} (hkJ : k ≤ 2 * 32 ^ (K.J - 1)) {s : State}
    (hs : Scr s base size) (hM : ModOkW K.M size Cv.p s.mem base) (hF : JacWinFixedO K Cv base s P k)
    (hT : JTblOkO K Cv base P 16 s) :
    WP isa (.block (fill kwords EKB ++ (ptrs K.tbl (K.tbl + 24 * K.M.n) ++
      (([.mov32 .rbx (.imm (BitVec.ofNat 32 (K.J - 1)))] : List Instr) ++ (adjUp ++ (zeroAcc ++
        (convQPieces.flatten ++ setPieces.flatten))))))) s fun t => EInv K base size P k s (K.J - 1) t := by
  have hL := hV.lay
  have hn4 := hV.n4
  have hnw := hs.nowrap
  have hsz := hV.sz
  have hJ := hL.J
  have tb : K.tbl + 160 ≤ 5472 := by
    have := hV.below (jg K 4, 8 * K.M.n) (mem_jwW_ws (jg_ws (by omega_using [])))
    unfold jg at this
    rw [hn4] at this
    dsimp only at this
    omega_using [this]
  rw [WP.block_append_iff]
  refine WP.mono (fill_ok kwords hs (o := EKB) (by rw [kwords_length]; simp only [EKB]; omega_using [hsz]))
    fun f ⟨fw, kf, Of⟩ => ?_
  rw [kwords_length] at fw Of
  have hsf : Scr f base size := hs.of_keepRegs kf (by decide)
  have Uf : Unch base [(EKB, 8 * 220)] s.mem f.mem := Of.unch
  obtain ⟨Mf, Ff, Tf⟩ := pre_unch hV hM hF hT hnw (by decide) Uf
  have mf : EMem K base size P k f := ⟨hsf.wr, hnw, Mf, Ff, Tf, fw⟩
  rw [WP.block_append_iff]
  refine WP.mono (ptrs_ok f (e := K.tbl) (z := K.tbl + 24 * K.M.n) (by omega_using [tb]) (by rw [hn4]; omega_using [tb]))
    fun g ⟨⟨g10, g9, gcx, gdx⟩, kg⟩ => ?_
  rw [hsf.rdi] at g10 gcx gdx
  rw [WP.block_append_iff]
  refine WP.mono (mov32Rbx_ok g (j := K.J - 1) (by omega_using [hJ])) fun h ⟨hbx, kh⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (adjUp_ok h) fun i ⟨idi, ki⟩ => ?_
  rw [kh.1 .rdi (by decide), kg.1 .rdi (by decide), hsf.rdi] at idi
  have imem : i.mem = f.mem := ki.2.1.trans (kh.2.1.trans kg.2.1)
  have iwr : i.wr = f.wr := ki.2.2.2.trans (kh.2.2.2.trans kg.2.2.2)
  have ird : i.rd = f.rd := ki.2.2.1.trans (kh.2.2.1.trans kg.2.2.1)
  have ci : Ctx par i := ectx (by rw [iwr]; exact hsf.wr) hnw hsz idi
    (by rw [ki.1 .r10 (by decide), kh.1 .r10 (by decide)]; exact g10) (x₀ := K.tbl)
    (by rw [ki.1 .rcx (by decide), kh.1 .rcx (by decide)]; exact gcx) (by omega_using [tb])
    (z₀ := K.tbl + 24 * K.M.n) (by rw [ki.1 .rdx (by decide), kh.1 .rdx (by decide)]; exact gdx)
    (by rw [hn4]; omega_using [tb])
    (by rw [ki.1 .r9 (by decide), ki.1 .r10 (by decide), kh.1 .r9 (by decide), kh.1 .r10 (by decide)]; exact g9)
    (fun n hn => by rw [imem]; exact fw n hn)
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok 20 i) fun l ⟨lz, lg, lm, lrd, lwr⟩ => ?_
  have cl := ctx_congr ci lg lm lrd lwr
  have bl := envOK_zero lz
  have ldi : l.gpr .rdi = base + BitVec.ofNat 64 EO := by rw [lg]; exact idi
  have wl (x : Nat) (hx : x + 32 ≤ 5472) : wordsVal l.mem base x 4 = wordsVal s.mem base x 4 := by
    rw [lm, imem]
    exact Uf.wordsVal (fun w hw => by
      rw [List.mem_singleton] at hw; subst hw
      exact Or.inl (by show x + 8 * 4 ≤ EKB; simp only [EKB]; omega_using [hx])) (by omega_using [hx])
  have tm (x : Nat) : tmv Cv K.M.n base s x = toM pN (2 ^ 256) (wordsVal s.mem base x 4) := by rw [hn4]; rfl
  have e0 : entS K 1 0 = K.tbl + 0 := by show K.tbl + 8 * K.M.n * (5 * (1 - 1) + 0) = _; rw [hn4]
  have e1 : entS K 1 1 = K.tbl + 32 := by show K.tbl + 8 * K.M.n * (5 * (1 - 1) + 1) = _; rw [hn4]
  have e2 : entS K 1 2 = K.tbl + 64 := by show K.tbl + 8 * K.M.n * (5 * (1 - 1) + 2) = _; rw [hn4]
  have e3 : entS K 1 3 = K.tbl + 24 * K.M.n + 0 := by
    show K.tbl + 8 * K.M.n * (5 * (1 - 1) + 3) = _; rw [hn4]
  have e4 : entS K 1 4 = K.tbl + 24 * K.M.n + 32 := by
    show K.tbl + 8 * K.M.n * (5 * (1 - 1) + 4) = _; rw [hn4]
  have jp := hT 1 (by decide) (by decide)
  have hj := jp.jac
  have z2 := jp.z2
  have z3 := jp.z3
  rw [show 2 * 1 - 1 = 1 from rfl, mul_one_pt] at hj
  obtain ⟨X, hX⟩ : ∃ X : Fin pN, tmv Cv K.M.n base s (entS K 1 0) = X := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : Fin pN, tmv Cv K.M.n base s (entS K 1 1) = Y := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : Fin pN, tmv Cv K.M.n base s (entS K 1 2) = Z := ⟨_, rfl⟩
  rw [hX, hY, hZ] at hj
  rw [hZ] at z2 z3
  rw [WP.block_append_iff]
  refine WP.mono (eConv_ok cl bl (x₀ := K.tbl) (z₀ := K.tbl + 24 * K.M.n)
    (by rw [lg, ki.1 .rcx (by decide), kh.1 .rcx (by decide)]; exact gcx)
    (by rw [lg, ki.1 .rdx (by decide), kh.1 .rdx (by decide)]; exact gdx)
    (by rw [lg, ki.1 .r9 (by decide), ki.1 .r10 (by decide), kh.1 .r9 (by decide), kh.1 .r10 (by decide)]; exact g9)
    (X := X) (Y := Y) (Z := Z)
    (by rw [wl _ (by omega_using [tb]), ← tm, ← e0]; exact hX)
    (by rw [wl _ (by omega_using [tb]), ← tm, ← e1]; exact hY)
    (by rw [wl _ (by omega_using [tb]), ← tm, ← e2]; exact hZ)
    (by rw [wl _ (by rw [hn4]; omega_using [tb]), ← tm, ← e3]; exact z2)
    (by rw [wl _ (by rw [hn4]; omega_using [tb]), ← tm, ← e4]; exact z3.trans (congrArg (· * Z) z2)))
    fun m ⟨cm, km, bm, sm, _, entm⟩ => ?_
  have mdi : m.gpr .rdi = base + BitVec.ofNat 64 EO := by rw [km.gpr]; exact ldi
  refine WP.mono (set_ok cm bm (p := entQN X Y Z false 0 0 0)
    (by have h := (entm 0 0 0).zz; rw [entQN_zz] at h; exact h) (entm 0 0 0).x (entm 0 0 0).z (entm 0 0 0).y sm)
    fun t ⟨ct, kt, bt, ht⟩ => ?_
  rw [ite_eq_right (show ¬ ((entQN X Y Z false 0 0 0).neg = true) from Bool.false_ne_true), entQN_eq] at ht
  have Uft : Unch base [eS] f.mem t.mem := by
    have h1 : Unch base [eS] l.mem m.mem := kept_unch ldi km.mem
    have h2 : Unch base [eS] m.mem t.mem := kept_unch mdi kt.mem
    rw [← imem, ← lm]
    exact (h1.trans h2).mono (by decide)
  have wft : t.wr = f.wr := by rw [kt.wr, km.wr, lwr, iwr]
  have gst : ∀ r, r ∉ [Reg.rax, .r10, .r9, .rcx, .rdx, .rbx, .rdi] → t.gpr r = s.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [kt.gpr, km.gpr, lg, ki.1 r (by simp [hr]), kh.1 r (by simp [hr]), kg.1 r (by simp [hr]),
      kf.gpr r (by simp [hr])]
  refine ⟨mf.vec hV wft (lo := eS.1) (n := eS.2) (by decide) (by decide) Uft, ct, bt,
    by rw [kt.gpr]; exact mdi, by rw [kt.gpr, km.gpr, lg, ki.1 .rbx (by decide)]; exact hbx, ?_,
    by rw [kt.rd, km.rd, lrd, ird, kf.rd], by rw [wft, kf.wr],
    eU_trans (unch_vec K Uf (by decide)) (unch_vec K Uft (by decide)), (entQ X Y Z false 0 0 0).ex,
    (entQ X Y Z false 0 0 0).ey, (entQ X Y Z false 0 0 0).ez, P, ht, hP, fun hv => ?_, ainv_set hC hj⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact gst _ (by decide)
  · rw [(OddWin.oe_top hv.1 (by omega_using [hJ]) hkJ).2, mul_one_pt]

/-- What the loop leaves, `rdi` back at the working space: the rows of the accumulator's triple in the
vectors' first five slots, carried, as a state `r` with `rdi` at the slots reads them. -/
structure EOut (K : JacWinCfg) (base : Addr) (size : Nat) (P : Point Cv) (k : Nat) (s t : State) : Prop where
  scr : Scr t base size
  mem : EMem K base size P k t
  rbx : t.gpr .rbx = BitVec.ofNat 64 0
  keep : ∀ r ∈ [Reg.rsi, .rsp, .r12], t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  unch : Unch base (jwW K ++ eV) s.mem t.mem
  out : ∃ (xn un z : Fin pN) (Q : Point Cv) (r : State), onCurve Cv Q = true ∧
    (k % 2 = 1 ∧ k < Cv.n → Q = mul (OddWin.oS K.J k 0) P) ∧ Ainv xn un z Q ∧
    r.gpr .rdi = base + BitVec.ofNat 64 EO ∧ r.mem = t.mem ∧
    Car3 (envOf r) sl5 (un * D (c4R : Nat)) (z * D (c2R : Nat)) (xn * D (c4R : Nat))

/-- The loop in vectors, from the table. -/
theorem vloopO_ok {K : JacWinCfg} {size : Nat} (hV : EVLay K size) (hC : Law Cv) (ha : AM3 Cv) (hO : PrimeOrder Cv)
    {P : Point Cv} (hP : onCurve Cv P = true) (hP0 : P ≠ .infinity) (hn2 : Cv.n % 2 = 1) (hn64 : Cv.n % 64 < 33)
    (hnb : 128 ≤ Cv.n)
    (h12a : ∀ i ∈ instrs (Code.block (C := Cond) (K.digitO ++ K.select)), Taint.clobbers i .r12 = false)
    (h12b : ∀ i ∈ instrs (Code.block (C := Cond) K.tc.negY), Taint.clobbers i .r12 = false)
    {base : Addr} {k : Nat} (hkJ : k ≤ 2 * 32 ^ (K.J - 1)) {s : State} (hs : Scr s base size)
    (hM : ModOkW K.M size Cv.p s.mem base) (hF : JacWinFixedO K Cv base s P k) (hT : JTblOkO K Cv base P 16 s) :
    WP isa (vloopO K) s fun t => EOut K base size P k s t := by
  have hJ := hV.lay.J
  rw [vloopO]
  apply WP.seq
  refine WP.mono (vinitO_ok hV hC hP hkJ hs hM hF hT) fun a ia => ?_
  apply WP.seq
  refine WP.mono (countLoop_ok (Q := fun t => EInv K base size P k s 0 t)
    (Inv := fun j t => EInv K base size P k s j t) (n := K.J - 1)
    (fun j t h1 h2 hi => vstepO_ok hV hC ha hO hP hP0 hn2 hn64 hnb h12a h12b h1 (by omega_using [hJ, h2]) hi)
    (fun _ h => h) (by omega_using [hJ]) ia) fun b ib => ?_
  obtain ⟨xn, un, z, Q, hacc, hQ, hQe, hA⟩ := ib.acc
  rw [WP.block_append_iff]
  refine WP.mono (out_ok ib.ctx ib.env hacc) fun c ⟨cc, kc, bc, hc⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (storeOut_ok cc bc hc) fun d ⟨kd, hd⟩ => ?_
  have cdi : c.gpr .rdi = base + BitVec.ofNat 64 EO := by rw [kc.gpr]; exact ib.rdi
  have ddi : d.gpr .rdi = base + BitVec.ofNat 64 EO := by rw [kd.gpr]; exact cdi
  rw [WP.block_append_iff]
  refine WP.mono (adjDn_ok d ddi) fun e ⟨edi, ke⟩ => ?_
  refine WP.mono (vzu_ok e) fun t ⟨tg, tm, trd, twr⟩ => ?_
  have Ubt : Unch base [eS] b.mem t.mem := by
    rw [tm, ke.2.1]
    exact ((kept_unch ib.rdi kc.mem).trans (kept_unch cdi kd.mem)).mono (by decide)
  have wbt : t.wr = b.wr := by rw [twr, ke.2.2.2, kd.wr, kc.wr]
  have gbt : ∀ r, r ≠ .rdi → t.gpr r = b.gpr r := fun r hr => by
    rw [tg, ke.1 r (by simpa using hr), kd.gpr, kc.gpr]
  have mt := ib.mem.vec hV wbt (lo := eS.1) (n := eS.2) (by decide) (by decide) Ubt
  refine ⟨⟨by rw [tg]; exact edi, mt.wr, mt.nw⟩, mt, (gbt .rbx (by decide)).trans ib.rbx, fun r hr => ?_,
    by rw [trd, ke.2.2.1, kd.rd, kc.rd]; exact ib.rd, wbt.trans ib.wr,
    eU_trans ib.unch (unch_vec K Ubt (by decide)), xn, un, z, Q, d, hQ, hQe, hA, ddi, by rw [tm, ke.2.1], hd⟩
  refine (gbt r ?_).trans (ib.keep r hr)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> decide

/-! ### Into `R` -/

/-- A lane of the vectors' first five slots, carried as the state `r` with `rdi` at the slots reads
them, reduced into the words at `dst`. -/
theorem elane_ok {M : Mod} {s r : State} {base : Addr} {size m : Nat} (hs : Scr s base size) (hbig : 8192 ≤ size)
    (hn : M.n = 4) (hmo : M.mo + 8 * M.n ≤ size) (hm : wordsVal s.mem base M.mo M.n = m) (hm2 : Nb ≤ 2 * (m : Int))
    {l dst : Nat} (hl : l < 4) (hdst : dst + 32 ≤ size) (hr : r.gpr .rdi = base + BitVec.ofNat 64 EO)
    (hsame : ∀ i, i < 5 → Mont.word s.mem base (SL + EO + 32 * i + 8 * l) =
      Mont.word r.mem base (SL + EO + 32 * i + 8 * l)) {x : Fin pN} (hc : Car (envOf r) l sl5 x) :
    WP isa (.block (packLaneAt (SL + EO) M l dst)) s fun t =>
      wordsVal t.mem base dst 4 = (vI (envOf r) l sl5).toNat % m ∧
      KeepRegs [.rax, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12] s t ∧ Outside base dst 32 s.mem t.mem := by
  have key (i : Nat) (hi : i < 5) :
      (0 ≤ (s.mem.readW (base + BitVec.ofNat 64 (SL + EO + 32 * i + 8 * l)) 64).toInt ∧
        (s.mem.readW (base + BitVec.ofNat 64 (SL + EO + 32 * i + 8 * l)) 64).toInt < 2 ^ 52) ∧
      (sl5.get i).int (envOf r) l =
        (s.mem.readW (base + BitVec.ofNat 64 (SL + EO + 32 * i + 8 * l)) 64).toInt := by
    have e := sl5_limb r l i hi
    have b := hc.c.get hi
    rw [hr, Offset.add_add, show EO + (SL + 32 * i + 8 * l) = SL + EO + 32 * i + 8 * l by omega_using []] at e
    have e' : (sl5.get i).int (envOf r) l =
        (s.mem.readW (base + BitVec.ofNat 64 (SL + EO + 32 * i + 8 * l)) 64).toInt :=
      e.trans (congrArg BitVec.toInt (hsame i hi).symm)
    rw [e'] at b
    exact ⟨b, e'⟩
  have ev : vI (envOf r) l sl5 =
      val5 (s.mem.readW (base + BitVec.ofNat 64 (SL + EO + 32 * 0 + 8 * l)) 64).toInt
      (s.mem.readW (base + BitVec.ofNat 64 (SL + EO + 32 * 1 + 8 * l)) 64).toInt
      (s.mem.readW (base + BitVec.ofNat 64 (SL + EO + 32 * 2 + 8 * l)) 64).toInt
      (s.mem.readW (base + BitVec.ofNat 64 (SL + EO + 32 * 3 + 8 * l)) 64).toInt
      (s.mem.readW (base + BitVec.ofNat 64 (SL + EO + 32 * 4 + 8 * l)) 64).toInt := by
    rw [vI_get, (key 0 (by decide)).2, (key 1 (by decide)).2, (key 2 (by decide)).2, (key 3 (by decide)).2,
      (key 4 (by decide)).2]
  rw [ev]
  exact packLaneAt_ok hs (by simp only [SL, EO]; omega_using [hbig]) hn hmo hm hm2 hl hdst (fun i hi => (key i hi).1)
    (by rw [← ev]; exact hc.hi)

theorem vloopO_inline (K : JacWinCfg) : (vloopO K).inline = vloopO K := rfl

theorem notPow4 : ∀ r : Reg, r ∉ powClob 4 → r = .rsi ∨ r = .rdi ∨ r = .rsp := by
  intro r; cases r <;> decide

/-- `[k]P` into `R`, in projective coordinates, as `windowO` (`winJacO_ok`), with the loop in vectors:
the vectors' part of the working space is written too. -/
theorem vwindowO_ok {K : JacWinCfg} {size : Nat} (hV : EVLay K size) (hp : UnitMod Cv.p (2 ^ (64 * K.M.n)))
    (hC : Law Cv) (hM3 : AM3 Cv) (hO : PrimeOrder Cv) (hpn : Cv.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < Cv.p)
    (hone : toM Cv.p (2 ^ (64 * K.M.n)) K.one = 1) (hn2 : Cv.n % 2 = 1) (hn64 : Cv.n % 64 < 33) (hnb : 128 ≤ Cv.n)
    (h12a : ∀ i ∈ instrs (Code.block (C := Cond) (K.digitO ++ K.select)), Taint.clobbers i .r12 = false)
    (h12b : ∀ i ∈ instrs (Code.block (C := Cond) K.tc.negY), Taint.clobbers i .r12 = false)
    {P : Point Cv} (hP : onCurve Cv P = true) {k : Nat} (hkJ : k ≤ 2 * 32 ^ (K.J - 1)) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkW K.M size Cv.p s.mem base) (hF : JacWinFixedO K Cv base s P k) :
    WP isa (vwindowO K).inline s fun s' => KeepRegs (powClob K.M.n) s s' ∧
      Unch base (jwW K ++ eV) s.mem s'.mem ∧ ModOkW K.M size Cv.p s'.mem base ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < Cv.p) ∧
      (k % 2 = 1 ∧ k < Cv.n → Rep Cv (tmv Cv K.M.n base s' K.R.x) (tmv Cv K.M.n base s' K.R.y)
        (tmv Cv K.M.n base s' K.R.z) (mul k P)) := by
  have hL := hV.lay
  have hn4 := hV.n4
  have hnw := hs.nowrap
  have hsz := hV.sz
  have hJ := hL.J
  have hP0 := hF.ne_infinity hC
  rw [vwindowO, region, regionAt]
  simp only [Code.inline]
  rw [vloopO_inline]
  refine WP.seq (WP.mono (jbuildO_ok hL hp hC hM3 hO hP hP0 (by omega_arith) hs hM hF.toJacWinPt)
    fun s₁ ⟨F₁, T₁⟩ => ?_)
  have hs₁ := F₁.scr
  have hF₁ := fixedO_unch hL hF F₁.unch hnw (fun x hx => hL.ro_w hx) hL.bits_w
  -- MXCSR
  apply WP.seq
  refine WP.seq (WP.mono (mxSave_ok hs₁ (by simp only [MX]; omega_using [hsz])) fun s₂ ⟨⟨m₂, r₂⟩, k₂⟩ => ?_)
  have hs₂ : Scr s₂ base size := ⟨(k₂.1 .rdi (by decide)).trans hs₁.rdi, k₂.2.2 ▸ hs₁.wr, hnw⟩
  have U₂ : Unch base [(5472, 8)] s₁.mem s₂.mem := by
    rw [m₂]; exact unch_write32 (d := MX) _ base _ (by decide) (by decide) (by decide)
  obtain ⟨M₂, F₂, T₂⟩ := pre_unch hV F₁.mod hF₁ T₁ hnw (Nat.le_refl _) U₂
  refine WP.seq (WP.seq (WP.mono (mxSet_ok hs₂ (by simp only [MX]; omega_using [hsz])) fun s₃ ⟨m₃, k₃⟩ => ?_))
  have hs₃ : Scr s₃ base size := ⟨(k₃.1 .rdi (by decide)).trans hs₂.rdi, k₃.2.2 ▸ hs₂.wr, hnw⟩
  have U₃ : Unch base [(5472, 8)] s₂.mem s₃.mem := by
    rw [m₃]; exact unch_write32 (d := MX + 4) _ base _ (by decide) (by decide) (by decide)
  obtain ⟨M₃, F₃, T₃⟩ := pre_unch hV M₂ F₂ T₂ hnw (Nat.le_refl _) U₃
  -- the loop
  refine WP.seq (WP.mono (vloopO_ok hV hC hM3 hO hP hP0 hn2 hn64 hnb h12a h12b hkJ hs₃ M₃ F₃ T₃) fun s₄ o₄ => ?_)
  rw [WP.block_cons_iff]
  refine ⟨s₄, rfl, WP.block_nil ?_⟩
  have hv : s₄.gpr .r12 = (s₁.mxcsr &&& 0xFFFF).setWidth 64 :=
    (o₄.keep .r12 (by decide)).trans ((k₃.1 .r12 (by decide)).trans r₂)
  refine WP.mono (mxRestore_ok o₄.scr (by simp only [MX]; omega_using [hsz]) hv) fun s₅ ⟨m₅, g₅, rd₅, wr₅⟩ => ?_
  have U₅ : Unch base [(5472, 8)] s₄.mem s₅.mem := by
    rw [m₅]; exact unch_write32 (d := MX) _ base _ (by decide) (by decide) (by decide)
  have e₅ := o₄.mem.vec hV wr₅ (lo := 5472) (n := 8) (by decide) (by decide) U₅
  have hs₅ : Scr s₅ base size := ⟨by rw [g₅]; exact o₄.scr.rdi, e₅.wr, hnw⟩
  obtain ⟨xn, un, z, Q, r, hQ, hQe, hA, rdi, rmem, c3⟩ := o₄.out
  have same₅ : ∀ i, i < 5 → ∀ l, l < 4 → Mont.word s₅.mem base (SL + EO + 32 * i + 8 * l) =
      Mont.word r.mem base (SL + EO + 32 * i + 8 * l) := fun i hi l hl => by
    rw [rmem]
    exact U₅.word (fun w hw => by
      rw [List.mem_singleton] at hw; subst hw
      exact Or.inr (by simp only [SL, EO]; omega_using [])) (by simp only [SL, EO]; omega_using [hi, hl])
  -- the accumulator's rows into `R`
  have mR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ jwOther K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> jw_mem
  have lw : ∀ x ∈ [K.R.x, K.R.y, K.R.z], (x, 8 * K.M.n) ∈ jwLoopW K := fun x hx => other_loopW (mR x hx)
  have dR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x + 32 ≤ 5472 := fun x hx => by
    have := hV.below _ (jwLoopW_sub K _ (lw x hx))
    rw [hn4] at this
    exact this
  have hm2 : Nb ≤ 2 * ((Cv.p : Nat) : Int) := by decide +kernel
  have far : ∀ {a b : Mem} {x : Nat}, x ∈ [K.R.x, K.R.y, K.R.z] → Outside base x 32 a b →
      ∀ i, i < 5 → ∀ l, l < 4 → Mont.word b base (SL + EO + 32 * i + 8 * l) =
        Mont.word a base (SL + EO + 32 * i + 8 * l) := fun hx O i hi l hl =>
    O.unch.word (fun w hw => by
      rw [List.mem_singleton] at hw; subst hw
      exact Or.inr (by have := dR _ hx; simp only [SL, EO]; omega_using [this])) (by simp only [SL, EO]; omega_using [hi, hl])
  have toL : ∀ {a b : Mem} {x : Nat}, x ∈ [K.R.x, K.R.y, K.R.z] → Outside base x 32 a b →
      Unch base (jwLoopW K) a b := fun hx O => O.unch.mono fun w hw => by
    rw [List.mem_singleton.mp hw, show (32 : Nat) = 8 * K.M.n by rw [hn4]]; exact lw _ hx
  have kP : ∀ {a b : State}, KeepRegs [.rax, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12] a b →
      KeepRegs (powClob K.M.n) a b := fun k => (k.mono (pk_regs hn4)).mono fun _ h => List.mem_cons_of_mem _ h
  have F₅ : JFrame K Cv base size s₅ s₅ := JFrame.refl hs₅ e₅.mod
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (elane_ok hs₅ hsz hn4 e₅.mod.mo e₅.mod.val hm2 (l := 3) (by decide)
    (by have := dR K.R.x (by simp); omega_using [hsz, this]) rdi (fun i hi => same₅ i hi 3 (by decide)) c3.x)
    fun s₆ ⟨v₆, k₆, O₆⟩ => ?_
  have hs₆ := hs₅.of_keepRegs k₆ (by decide)
  have F₆ := F₅.next hL hs₆ (kP k₆) (toL (by simp) O₆) (jwLoopW_sub K)
  rw [WP.block_append_iff]
  refine WP.mono (elane_ok hs₆ hsz hn4 F₆.mod.mo F₆.mod.val hm2 (l := 0) (by decide)
    (by have := dR K.R.y (by simp); omega_using [hsz, this]) rdi
    (fun i hi => (far (by simp) O₆ i hi 0 (by decide)).trans (same₅ i hi 0 (by decide))) c3.y)
    fun s₇ ⟨v₇, k₇, O₇⟩ => ?_
  have hs₇ := hs₆.of_keepRegs k₇ (by decide)
  have F₇ := F₆.next hL hs₇ (kP k₇) (toL (by simp) O₇) (jwLoopW_sub K)
  refine WP.mono (elane_ok hs₇ hsz hn4 F₇.mod.mo F₇.mod.val hm2 (l := 1) (by decide)
    (by have := dR K.R.z (by simp); omega_using [hsz, this]) rdi
    (fun i hi => ((far (by simp) O₇ i hi 1 (by decide)).trans (far (by simp) O₆ i hi 1 (by decide))).trans
      (same₅ i hi 1 (by decide))) c3.z) fun s₈ ⟨v₈, k₈, O₈⟩ => ?_
  have hs₈ := hs₇.of_keepRegs k₈ (by decide)
  have F₈ := F₇.next hL hs₈ (kP k₈) (toL (by simp) O₈) (jwLoopW_sub K)
  have T₈ : JTblOkO K Cv base P 16 s₈ :=
    ((e₅.tbl.loopW hL (toL (by simp) O₆) hnw (Nat.le_refl _)).loopW hL (toL (by simp) O₇) hnw
      (Nat.le_refl _)).loopW hL (toL (by simp) O₈) hnw (Nat.le_refl _)
  have hF₈ := fixedO_unch hL e₅.fix F₈.unch hnw (fun x hx => hL.ro_w hx) hL.bits_w
  have b64 : ∀ x ∈ jwSlots K, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by have := hL.le hx; omega_arith
  have O₇' : Outside base K.R.y (8 * K.M.n) s₆.mem s₇.mem := by rw [hn4]; exact O₇
  have O₈' : Outside base K.R.z (8 * K.M.n) s₇.mem s₈.mem := by rw [hn4]; exact O₈
  have x87 : wordsVal s₈.mem base K.R.x K.M.n = wordsVal s₇.mem base K.R.x K.M.n :=
    O₈'.wordsVal (hL.ap_oth (i := 0) (j := 2) (by decide) (by decide) (by decide)) (b64 _ (by jw_mem))
  have x76 : wordsVal s₇.mem base K.R.x K.M.n = wordsVal s₆.mem base K.R.x K.M.n :=
    O₇'.wordsVal (hL.ap_oth (i := 0) (j := 1) (by decide) (by decide) (by decide)) (b64 _ (by jw_mem))
  have y87 : wordsVal s₈.mem base K.R.y K.M.n = wordsVal s₇.mem base K.R.y K.M.n :=
    O₈'.wordsVal (hL.ap_oth (i := 1) (j := 2) (by decide) (by decide) (by decide)) (b64 _ (by jw_mem))
  have wx : wordsVal s₈.mem base K.R.x K.M.n = (vI (envOf r) 3 sl5).toNat % Cv.p := by
    rw [x87, x76, hn4]; exact v₆
  have wy : wordsVal s₈.mem base K.R.y K.M.n = (vI (envOf r) 0 sl5).toNat % Cv.p := by
    rw [y87, hn4]; exact v₇
  have wz : wordsVal s₈.mem base K.R.z K.M.n = (vI (envOf r) 1 sl5).toNat % Cv.p := by rw [hn4]; exact v₈
  have p0 : 0 < Cv.p := by decide
  have ex : tmv Cv K.M.n base s₈ K.R.x = (4 * xn : Fin pN) := by
    show toM Cv.p (2 ^ (64 * K.M.n)) _ = _
    rw [wx, hn4]; exact toM_car 4 c3.x
  have ey : tmv Cv K.M.n base s₈ K.R.y = (4 * un : Fin pN) := by
    show toM Cv.p (2 ^ (64 * K.M.n)) _ = _
    rw [wy, hn4]; exact toM_car 4 c3.y
  have ez : tmv Cv K.M.n base s₈ K.R.z = (2 * z : Fin pN) := by
    show toM Cv.p (2 ^ (64 * K.M.n)) _ = _
    rw [wz, hn4]; exact toM_car 2 c3.z
  have rbx₈ : s₈.gpr .rbx = BitVec.ofNat 64 0 := by
    rw [k₈.gpr .rbx (by decide), k₇.gpr .rbx (by decide), k₆.gpr .rbx (by decide), g₅]; exact o₄.rbx
  have I₈ : JInvO K Cv base size P s₈ k 0 s₈ := by
    refine ⟨⟨Q, hQ, hQe, JFrame.refl hs₈ F₈.mod, T₈, fun x hx => ?_, ?_⟩, rbx₈⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · rw [wx]; exact Nat.mod_lt _ p0
      · rw [wy]; exact Nat.mod_lt _ p0
      · rw [wz]; exact Nat.mod_lt _ p0
    · rw [ex, ey, ez]; exact hA
  refine WP.mono (jfinO_ok hL hp hC hpn hone_lt hone hF₈ I₈) fun s' ⟨K₉, U₉, M₉, L₉, R₉⟩ => ?_
  refine ⟨⟨fun x hx => ?_, ?_, ?_⟩, ?_, M₉, L₉, R₉⟩
  · rw [K₉.gpr x hx, F₈.keep.gpr x hx, g₅]
    rw [hn4] at hx
    rcases notPow4 x hx with rfl | rfl | rfl
    · rw [o₄.keep .rsi (by decide), k₃.1 .rsi (by decide), k₂.1 .rsi (by decide)]
      exact F₁.keep.gpr .rsi (by rw [hn4]; exact hx)
    · rw [o₄.scr.rdi, hs.rdi]
    · rw [o₄.keep .rsp (by decide), k₃.1 .rsp (by decide), k₂.1 .rsp (by decide)]
      exact F₁.keep.gpr .rsp (by rw [hn4]; exact hx)
  · rw [K₉.rd, F₈.keep.rd, rd₅, o₄.rd, k₃.2.1, k₂.2.1, F₁.keep.rd]
  · rw [K₉.wr, F₈.keep.wr, wr₅, o₄.wr, k₃.2.2, k₂.2.2, F₁.keep.wr]
  · exact eU_trans (unch_jw F₁.unch) (eU_trans (unch_vec K U₂ (by decide)) (eU_trans (unch_vec K U₃ (by decide))
      (eU_trans o₄.unch (eU_trans (unch_vec K U₅ (by decide)) (eU_trans (unch_jw F₈.unch) (unch_jw U₉))))))

end VG.Proof.P256.X86_64.Ifma
