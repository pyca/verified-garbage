module

public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Scalars
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.MulFn
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.PointFprog
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Copy
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Keep
import VerifiedGarbage.Proof.Mont.PPC64LE.Const
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Rep
import VerifiedGarbage.Proof.Weierstrass.Pow
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Stages

/-!
# ECDSA verification on PPC64LE: `[u]G + [v]Q`

As on 32-bit ARM (`Proof/Ecdsa/Verify/Arm/Points.lean`): `save_ok` copies
`R` to `U` and resets `R` to `O`; `sum_ok` is `R = U + R` by the complete
addition (`rcbR_ok` on the slots it names); `points_ok` is `[u]G` by the
signature's ladder, `save`, `[v]Q` by ECDH's, and the sum.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Weierstrass.PPC64LE.Point VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Weierstrass.PPC64LE.Point VG.Proof.Ecdsa.PPC64LE
  VG.Proof.Ecdh.PPC64LE VG.Spec.Weierstrass
open VG.Impl.Ecdh.PPC64LE (PX PY)
open VG.Impl.Ecdsa.Verify.PPC64LE (SM' EM' RM' UM VM U V UX UY UZ)

variable {c : Cfg}

/-- `[o] = x`, on numbered slots. -/
theorem setSl_ok (hc : CfgOk c) {s : State} {base : Addr} (hw : WsReg s base) {o x : Nat}
    (ho : o < 45) (hx : x < 2 ^ (64 * c.n)) :
    WP isa (.block (VG.Impl.Mont.PPC64LE.setConst c.n (c.sl o) x)) s fun s' =>
      sv c base s' o = x ∧ Kp [.r11] s s' ∧ Outside base (c.sl o) (8 * c.n) s.mem s'.mem := by
  have := sl_le c hc.n10 ho
  have hsz : size = 8192 := rfl
  refine WP.mono (setConst_ok (size := size) hw.ws hw.at3 (o := c.sl o) (by omega_arith) hx) fun s' ⟨O, e, k⟩ =>
    ⟨?_, k, O⟩
  show wordsVal _ _ _ _ = _
  rw [wordsVal_eq_val32]; exact e

/-- The slots `save` writes. -/
abbrev saveW : List Nat := [UX, UY, UZ, RX, RY, RZ]

theorem save_eq (c : Cfg) : Impl.Ecdsa.Verify.PPC64LE.Cfg.save c =
    copy c.n (c.sl UX) (c.sl RX) ++ (copy c.n (c.sl UY) (c.sl RY) ++
    (copy c.n (c.sl UZ) (c.sl RZ) ++ (VG.Impl.Mont.PPC64LE.setConst c.n (c.sl RX) 0 ++
    (VG.Impl.Mont.PPC64LE.setConst c.n (c.sl RY) (c.mont 1) ++
      VG.Impl.Mont.PPC64LE.setConst c.n (c.sl RZ) 0)))) := by
  simp only [Impl.Ecdsa.Verify.PPC64LE.Cfg.save, List.append_assoc]

/-- `U = R`, and `R = O`. -/
theorem save_ok (hc : CfgOk c) {s : State} {base : Addr} (hw : WsReg s base) :
    WP isa (.block (Impl.Ecdsa.Verify.PPC64LE.Cfg.save c)) s fun s' =>
      Kp [.r4, .r11] s s' ∧ Unch base (slW c saveW) s.mem s'.mem ∧
      sv c base s' UX = sv c base s RX ∧ sv c base s' UY = sv c base s RY ∧
      sv c base s' UZ = sv c base s RZ ∧ sv c base s' RX = 0 ∧ sv c base s' RY = c.mont 1 ∧
      sv c base s' RZ = 0 := by
  have h7 := hc.n10
  have hn := hw.nowrap
  have hp := hc.p_lt
  have hp3 := hc.p_ge
  have hm1 : c.mont 1 < 2 ^ (64 * c.n) := by
    have : c.mont 1 < c.C.p := Nat.mod_lt _ (by omega_arith)
    omega_arith
  rw [save_eq]
  refine wp_append (WP.mono (copySl_ok hc hw (o := UX) (a := RX) (by decide) (by decide) (by decide))
    fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
  have hw₁ := hw.of_kp k₁
  refine wp_append (WP.mono (copySl_ok hc hw₁ (o := UY) (a := RY) (by decide) (by decide) (by decide))
    fun s₂ ⟨e₂, k₂, O₂⟩ => ?_)
  have hw₂ := hw₁.of_kp k₂
  refine wp_append (WP.mono (copySl_ok hc hw₂ (o := UZ) (a := RZ) (by decide) (by decide) (by decide))
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_)
  have hw₃ := hw₂.of_kp k₃
  refine wp_append (WP.mono (setSl_ok hc hw₃ (o := RX) (x := 0) (by decide) (Nat.two_pow_pos _))
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_)
  have hw₄ := hw₃.of_kp k₄
  refine wp_append (WP.mono (setSl_ok hc hw₄ (o := RY) (by decide) hm1) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_)
  have hw₅ := hw₄.of_kp k₅
  refine WP.mono (setSl_ok hc hw₅ (o := RZ) (x := 0) (by decide) (Nat.two_pow_pos _))
    fun s₆ ⟨e₆, k₆, O₆⟩ => ?_
  have o : ∀ {s s' : State} {j i : Nat}, Outside base (c.sl j) (8 * c.n) s.mem s'.mem → i < 45 → i ≠ j →
      sv c base s' i = sv c base s i := fun {_ _ j _} O hi hij =>
    sv_unch O.unch h7 hn hi (apart_slW (c := c) (l := [j]) (by simpa using hij))
  refine ⟨(((((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans (k₃.mono (by decide))).trans
      (k₄.mono (by decide))).trans (k₅.mono (by decide))).trans (k₆.mono (by decide)), ?_,
    ?_, ?_, ?_, ?_, ?_, e₆⟩
  · have := O₁.unch.trans (O₂.unch.trans (O₃.unch.trans (O₄.unch.trans (O₅.unch.trans O₆.unch))))
    exact this.mono fun w hw => by simpa [saveW, slW] using hw
  · rw [o O₆ (by decide) (by decide), o O₅ (by decide) (by decide), o O₄ (by decide) (by decide),
      o O₃ (by decide) (by decide), o O₂ (by decide) (by decide), e₁]
  · rw [o O₆ (by decide) (by decide), o O₅ (by decide) (by decide), o O₄ (by decide) (by decide),
      o O₃ (by decide) (by decide), e₂, o O₁ (by decide) (by decide)]
  · rw [o O₆ (by decide) (by decide), o O₅ (by decide) (by decide), o O₄ (by decide) (by decide), e₃,
      o O₂ (by decide) (by decide), o O₁ (by decide) (by decide)]
  · rw [o O₆ (by decide) (by decide), o O₅ (by decide) (by decide), e₄]
  · rw [o O₆ (by decide) (by decide), e₅]

/-- The slots of `rcb`'s numbered operands in the sum: `D`, `U`, `R`, `a`,
`3b` and the temporaries. -/
def sumIdx : List Nat := [DX, DY, DZ, UX, UY, UZ, RX, RY, RZ, AP, B3P, T0, T1, T2, T3, T4, T5]

/-- The offsets of `rcb`'s numbered operands in the sum. -/
abbrev sumσ (c : Cfg) (i : Nat) : Nat := c.sl (sumIdx.getD i 0)

theorem sum_fprog (c : Cfg) : fprog c.SP (rcb c.rcbSlots (c.pt UX UY UZ) (c.pt RX RY RZ) (c.pt DX DY DZ)) =
    fprogR (sumσ c) c.SP (rcb sId pId qId oId) := rfl

theorem sumIdx_lt : ∀ i < 17, sumIdx.getD i 0 < 45 := by decide

theorem sumIdx_inj : ∀ i < 17, ∀ j < 17, sumIdx.getD i 0 = sumIdx.getD j 0 → i = j := by decide

theorem sumLay (h7 : c.n < 10) : LayR c.n 17 wIds (sumσ c) where
  le := fun x hx => sl_below_own c h7 (sumIdx_lt x hx)
  apart := fun w hw x hx hxw => sl_apart c fun h => hxw (sumIdx_inj x hx w (by
    simp only [wIds, List.mem_cons, List.not_mem_nil, or_false] at hw; omega_arith) h)

/-- The sum over any modulus `S` of `c.n` words, `m`. -/
theorem sum_core {S : Impl.Weierstrass.Mont.Modulus} {m : Nat} [NeZero m] (hkS : S.k = c.n) (hmS : S.m = m)
    (hM : ModOk c.n m) (h7 : c.n < 10) (hm : UnitMod m (2 ^ (64 * c.n))) {base : Addr} {s : State}
    (hw : WsReg s base) (hlt : ∀ x ∈ rIds, wordsVal s.mem base (sumσ c x) c.n < m) :
    WP isa (fprogR (sumσ c) S (rcb sId pId qId oId)) s fun s' =>
      KeepR c.n (sumσ c) base wIds s s' ∧
      InvR c.n 17 (sumσ c) base m (validAfter (rcb sId pId qId oId) rIds)
        (runOps (rcb sId pId qId oId) fun x => toM m (2 ^ (64 * c.n)) (wordsVal s.mem base (sumσ c x) c.n)) s' ∧
      (runOps (rcb sId pId qId oId) (fun x => toM m (2 ^ (64 * c.n)) (wordsVal s.mem base (sumσ c x) c.n)) 0,
        runOps (rcb sId pId qId oId) (fun x => toM m (2 ^ (64 * c.n)) (wordsVal s.mem base (sumσ c x) c.n)) 1,
        runOps (rcb sId pId qId oId) (fun x => toM m (2 ^ (64 * c.n)) (wordsVal s.mem base (sumσ c x) c.n)) 2) =
        VG.Proof.Weierstrass.rcbAdd
          (toM m (2 ^ (64 * c.n)) (wordsVal s.mem base (sumσ c 9) c.n))
          (toM m (2 ^ (64 * c.n)) (wordsVal s.mem base (sumσ c 10) c.n))
          (toM m (2 ^ (64 * c.n)) (wordsVal s.mem base (sumσ c 3) c.n))
          (toM m (2 ^ (64 * c.n)) (wordsVal s.mem base (sumσ c 4) c.n))
          (toM m (2 ^ (64 * c.n)) (wordsVal s.mem base (sumσ c 5) c.n))
          (toM m (2 ^ (64 * c.n)) (wordsVal s.mem base (sumσ c 6) c.n))
          (toM m (2 ^ (64 * c.n)) (wordsVal s.mem base (sumσ c 7) c.n))
          (toM m (2 ^ (64 * c.n)) (wordsVal s.mem base (sumσ c 8) c.n)) := by
  obtain ⟨cv, w, m', k', d⟩ := S
  dsimp only at hkS hmS
  subst hkS hmS
  exact rcbR_ok (S := ⟨cv, w, m', c.n, d⟩) hM rfl (sumLay h7) hm
    ⟨hw, by decide, hlt, fun _ _ => rfl⟩

/-- The slots `sum` writes. -/
abbrev sumW : List Nat := [DX, DY, DZ, T0, T1, T2, T3, T4, T5, RX, RY, RZ]

theorem sum_eq (c : Cfg) : Impl.Ecdsa.Verify.PPC64LE.Cfg.sum c =
    .seq (fprogR (sumσ c) c.SP (rcb sId pId qId oId))
      (.block (copy c.n (c.sl RX) (c.sl DX) ++ (copy c.n (c.sl RY) (c.sl DY) ++ copy c.n (c.sl RZ) (c.sl DZ)))) := by
  rw [Impl.Ecdsa.Verify.PPC64LE.Cfg.sum, sum_fprog, List.append_assoc]

/-- `R = U + R`, by the complete addition. -/
theorem sum_ok (hc : CfgOk c) {s₀ : State} {base : Addr} {s : State} (K₀ : Keep c s₀ base s)
    (hlt : ∀ i ∈ [AP, B3P, UX, UY, UZ, RX, RY, RZ], sv c base s i < c.C.p) :
    WP isa (Impl.Ecdsa.Verify.PPC64LE.Cfg.sum c) s fun s' =>
      Keep c s₀ base s' ∧ Unch base (slW c sumW ++ [(own c.n, 64 * c.n)]) s.mem s'.mem ∧
      sv c base s' RX < c.C.p ∧ sv c base s' RY < c.C.p ∧ sv c base s' RZ < c.C.p ∧
      (tmv c.C c.n base s' (c.sl RX), tmv c.C c.n base s' (c.sl RY), tmv c.C c.n base s' (c.sl RZ)) =
        rcbAdd (tmv c.C c.n base s (c.sl AP)) (tmv c.C c.n base s (c.sl B3P))
          (tmv c.C c.n base s (c.sl UX)) (tmv c.C c.n base s (c.sl UY)) (tmv c.C c.n base s (c.sl UZ))
          (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY)) (tmv c.C c.n base s (c.sl RZ)) := by
  have h7 := hc.n10
  have hn := K₀.ws.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hM : ModOk c.n c.C.p := by have := hc.fp; rw [hc.fpk, hc.fpm] at this; exact this
  rw [sum_eq]
  refine WP.seq (WP.mono (sum_core hc.fpk hc.fpm hM h7 hpR K₀.ws (fun x hx => ?_)) fun s₁ ⟨KR, I₁, t₁⟩ => ?_)
  · simp only [rIds, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hlt _ (by decide)
  have UR : Unch base (slW c [DX, DY, DZ, T0, T1, T2, T3, T4, T5] ++ [(own c.n, 64 * c.n)]) s.mem s₁.mem := KR.mem
  have K₁ := K₀.step h7 (rs := fnClob) ⟨KR.gpr, KR.rd, KR.wr, KR.sp⟩ (hU := UR)
    (hW := (fixedOk_slW (by decide)).append (fun w hw => by
      rw [List.mem_singleton.mp hw]
      exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_below_own c h7 (i := 12) (by decide)))))
    (hWs := le_append (slW_le h7 (by decide)) (fun w hw => by
      rw [List.mem_singleton.mp hw]; have := own_below_bits c h7 0; have := bitsAt_le c h7 (j := 0) (by decide)
      dsimp only; omega_arith))
  refine wp_append (WP.mono (copySl_ok hc K₁.ws (o := RX) (a := DX) (by decide) (by decide) (by decide))
    fun s₂ ⟨e₂, k₂, O₂⟩ => ?_)
  have hw₂ := K₁.ws.of_kp k₂
  refine wp_append (WP.mono (copySl_ok hc hw₂ (o := RY) (a := DY) (by decide) (by decide) (by decide))
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_)
  have hw₃ := hw₂.of_kp k₃
  refine WP.mono (copySl_ok hc hw₃ (o := RZ) (a := DZ) (by decide) (by decide) (by decide))
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  have o : ∀ {s s' : State} {j i : Nat}, Outside base (c.sl j) (8 * c.n) s.mem s'.mem → i < 45 → i ≠ j →
      sv c base s' i = sv c base s i := fun {_ _ j _} O hi hij =>
    sv_unch O.unch h7 hn hi (apart_slW (c := c) (l := [j]) (by simpa using hij))
  have x₄ : sv c base s₄ RX = sv c base s₁ DX := by
    rw [o O₄ (by decide) (by decide), o O₃ (by decide) (by decide), e₂]
  have y₄ : sv c base s₄ RY = sv c base s₁ DY := by
    rw [o O₄ (by decide) (by decide), e₃, o O₂ (by decide) (by decide)]
  have z₄ : sv c base s₄ RZ = sv c base s₁ DZ := by
    rw [e₄, o O₃ (by decide) (by decide), o O₂ (by decide) (by decide)]
  have U₄ : Unch base (slW c [RX, RY, RZ]) s₁.mem s₄.mem := by
    have := O₂.unch.trans (O₃.unch.trans O₄.unch)
    exact this.mono fun w hw => by simpa [slW] using hw
  have K₄ := K₁.step h7 ((k₂.trans (k₃.trans k₄)).rk (rs' := [.r4])) (hU := U₄)
    (hW := fixedOk_slW (by decide)) (hWs := slW_le h7 (by decide))
  have hD : ∀ i ∈ [0, 1, 2], i ∈ validAfter (rcb sId pId qId oId) rIds := by decide
  have l₀ := I₁.lt 0 (hD 0 (by decide))
  have l₁ := I₁.lt 1 (hD 1 (by decide))
  have l₂ := I₁.lt 2 (hD 2 (by decide))
  refine ⟨K₄, (UR.trans U₄).mono fun w hw => ?_, by rw [x₄]; exact l₀, by rw [y₄]; exact l₁,
    by rw [z₄]; exact l₂, ?_⟩
  · simp only [slW, List.map_cons, List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hw ⊢
    grind
  · show (toM _ _ (sv c base s₄ RX), toM _ _ (sv c base s₄ RY), toM _ _ (sv c base s₄ RZ)) = _
    rw [x₄, y₄, z₄]
    exact (congrArg₂ Prod.mk (I₁.val 0 (hD 0 (by decide)))
      (congrArg₂ Prod.mk (I₁.val 1 (hD 1 (by decide))) (I₁.val 2 (hD 2 (by decide))))).trans t₁

/-- After `[u]G + [v]Q`: `R` holds the complete addition of points that
represent `[u]G` and `[v]P`. -/
structure Pts (c : Cfg) (s₀ : State) (base : Addr) (u v : Nat) (P : Point c.C) (s : State) : Prop
    extends Keep c s₀ base s where
  t₁ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 1 + t)) = if (c.C.p - 2).testBit t then 1 else 0
  flag : flagW c base s =
    mask64 (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n))
  rm_lt : sv c base s RM' < c.C.n
  rm : toM c.C.n (2 ^ (64 * c.n)) (sv c base s RM') = Fin.ofNat c.C.n (sigR c s₀)
  rz_lt : sv c base s RZ < c.C.p
  pt : ∃ X1 Y1 Z1 X2 Y2 Z2 : Fe c.C, Rep c.C X1 Y1 Z1 (mul u (G c.C)) ∧ Rep c.C X2 Y2 Z2 (mul v P) ∧
    (tmv c.C c.n base s (c.sl RX), tmv c.C c.n base s (c.sl RY), tmv c.C c.n base s (c.sl RZ)) =
      rcbAdd (Fin.ofNat c.C.p c.C.a) (Fin.ofNat c.C.p (3 * c.C.b)) X1 Y1 Z1 X2 Y2 Z2

/-- What `scalarAt` writes: `K`'s slot (for `vg_<curve>_mul`) or the table
of bits. -/
abbrev scW (c : Cfg) : List (Nat × Nat) := slW c [K] ++ [(bitsAt c.n 0, 64 * c.n)]

theorem apart_scW (h7 : c.n < 10) {i : Nat} (hi : i < 45) (hK : i ≠ K) :
    ∀ w ∈ scW c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
  apart_append (apart_slW (by simpa using hK)) (apart_tbl h7 hi 0)

theorem fixedOk_scW (h7 : c.n < 10) : FixedOk c (scW c) :=
  (fixedOk_slW (by decide)).append (fixedOk_tbl h7 0)

theorem scW_le (h7 : c.n < 10) : ∀ w ∈ scW c, w.1 + w.2 ≤ size :=
  le_append (slW_le h7 (by decide)) fun w hw => by rw [List.mem_singleton.mp hw]; exact bitsAt_le c h7 (by decide)

theorem tbl_apart_scW (h7 : c.n < 10) {j t : Nat} (hj : j ≠ 0) (ht : t < 64 * c.n) :
    ∀ w ∈ scW c, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t :=
  apart_append (tbl_apart_slW h7 (by decide) j t) (tbl_apart_tbl hj ht)

/-- The scalar at slot `i` to where the multiplication reads it: `K`'s slot
for `vg_<curve>_mul`, else the table of its bits. -/
theorem scalarAt_ok (hc : CfgOk c) {s : State} {base : Addr} (hw : WsReg s base) {i : Nat} (hi : i < 45)
    (hK : i ≠ K) :
    WP isa (Impl.Ecdsa.Verify.PPC64LE.Cfg.scalarAt c i) s fun s' => Kp bitsClob s s' ∧
      Unch base (scW c) s.mem s'.mem ∧ (c.mul.isSome → sv c base s' K = sv c base s i) ∧
      (c.mul = none → ∀ t < 64 * c.n, s'.mem (off base (bitsAt c.n 0 + t)) =
        if (sv c base s i).testBit t then 1 else 0) := by
  unfold Impl.Ecdsa.Verify.PPC64LE.Cfg.scalarAt
  split
  · next C hC =>
    refine WP.mono (copySl_ok hc hw (o := K) (a := i) (by decide) hi (Ne.symm hK)) fun s' ⟨x, k, O⟩ =>
      ⟨k.mono, O.unch.mono fun w hw => List.mem_append_left _ (by simpa using hw), fun _ => x, fun h => ?_⟩
    rw [hC] at h; exact absurd h (by simp)
  · next hN =>
    refine WP.mono (tbl_bits_ok hc hw (i := i) (j := 0) hi (by decide)) fun s' ⟨b, k, O⟩ =>
      ⟨k, O.unch.mono fun w hw => List.mem_append_right _ hw, fun h => ?_, fun _ => b⟩
    rw [hN] at h; exact absurd h (by simp)

theorem points_eq (c : Cfg) : Impl.Ecdsa.Verify.PPC64LE.Cfg.points c =
    .seq (Impl.Ecdsa.Verify.PPC64LE.Cfg.scalarAt c U) (.seq (c.qMul GX GY)
      (.seq (.block (Impl.Ecdsa.Verify.PPC64LE.Cfg.save c)) (.seq (Impl.Ecdsa.Verify.PPC64LE.Cfg.scalarAt c V)
      (.seq (c.qMul PX PY) (Impl.Ecdsa.Verify.PPC64LE.Cfg.sum c))))) := rfl

/-- The slots the multiplications, `save` and the sum write. -/
abbrev ptsW : List Nat := [RX, RY, RZ, UX, UY, UZ, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ, TMP, K, ACC, PT]

/-- `[u]G + [v]Q`, into `R`. -/
theorem points_ok (hc : CfgOk c) (h3 : 3 ≤ c.n) (hC : Law c.C) {s₀ : State} {base : Addr}
    {s : State} (hM : Mid c s₀ base s) {P : Point c.C} (hP : onCurve c.C P = true)
    (hQ : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY)) (tmv c.C c.n base s (c.sl ONEP)) P)
    {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s', Pts c s₀ base (sv c base s U) (sv c base s V) P s' → WP isa rest s' Q) :
    WP isa (.seq (Impl.Ecdsa.Verify.PPC64LE.Cfg.points c) rest) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hM.ws.nowrap
  have hsz : size = 8192 := rfl
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_arith)
  have F := hM.fixed
  have ha : ∀ {t : State}, Fixed c base s₀.gpr s₀.lr t.mem → tmv c.C c.n base t (c.sl AP) = Fin.ofNat c.C.p c.C.a :=
    fun F => by show toM _ _ (wordsVal _ base (c.sl AP) c.n) = _; rw [F.ap]; exact toM_cmont hc _
  have hb : ∀ {t : State}, Fixed c base s₀.gpr s₀.lr t.mem →
      tmv c.C c.n base t (c.sl B3P) = Fin.ofNat c.C.p (3 * c.C.b) :=
    fun F => by show toM _ _ (wordsVal _ base (c.sl B3P) c.n) = _; rw [F.b3p]; exact toM_cmont hc _
  have hz : ∀ {t : State}, Fixed c base s₀.gpr s₀.lr t.mem → sv c base t ZERO = 0 := fun F => F.zero
  have h1 : ∀ {t : State}, Fixed c base s₀.gpr s₀.lr t.mem → sv c base t ONEP = c.mont 1 := fun F => by
    rw [show sv c base _ ONEP = 2 ^ (64 * c.n) % c.C.p from F.onep, Cfg.mont, Cfg.R, Nat.one_mul]
  -- `O`, as zero and one hold it, stands for `[k]P` for any `k` of `8 len` bits.
  have hO : ∀ {t : State} {k : Nat} {P : Point c.C}, Fixed c base s₀.gpr s₀.lr t.mem → k < 2 ^ (8 * c.C.len) →
      Rep c.C (tmv c.C c.n base t (c.sl ZERO)) (tmv c.C c.n base t (c.sl ONEP)) (tmv c.C c.n base t (c.sl ZERO))
        (mul (k >>> (8 * c.C.len)) P) := fun F hk => by
    show Rep c.C (toM _ _ (sv c base _ ZERO)) (toM _ _ (sv c base _ ONEP)) (toM _ _ (sv c base _ ZERO)) _
    rw [hz F, h1 F, toM_cmont hc, toM_zero, shiftRight_eq_zero hk, mul_zero_pt]
    exact rep_infinity' hC
  have hW : FixedOk c (ladWp (ladderAt c GX GY) ++ genX c) := (fixedOk_ladWp h3 h7 GX GY).append (fixedOk_genX h7)
  have hWs : ∀ w ∈ ladWp (ladderAt c GX GY) ++ genX c, w.1 + w.2 ≤ size :=
    le_append (ladWp_le h3 h7 GX GY) (genX_le h7)
  have apL : ∀ {gx gy i : Nat}, i < 45 → i ∉ ACC :: PT :: ladIx → ∀ w ∈ ladWp (ladderAt c gx gy) ++ genX c,
      c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := fun hi hl =>
    apart_append (apart_ladWp h3 h7 hi (nmem_of hl (by decide))) (apart_genX h7 hi (nmem_of hl (by decide)))
  have tbL : ∀ {gx gy j t : Nat}, j ≠ 0 → t < 64 * c.n → ∀ w ∈ ladWp (ladderAt c gx gy) ++ genX c,
      bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := fun hj ht =>
    apart_append (tbl_apart_ladWp h3 h7 _ _ _ _) (tbl_apart_genX h7 hj ht)
  rw [points_eq]
  refine WP.seq ?_
  -- `u` to where the multiplication reads it.
  refine WP.seq (WP.mono (scalarAt_ok hc hM.ws (i := U) (by decide) (by decide)) fun s₁ ⟨k₁, U₁, sk₁, b₁⟩ => ?_)
  have K₁ := hM.toKeep.step h7 (k₁.rk (rs' := bitsClob)) (hU := U₁) (hW := fixedOk_scW h7) (hWs := scW_le h7)
  have v₁ : ∀ {i}, i < 45 → i ≠ K → sv c base s₁ i = sv c base s i := fun hi hK =>
    sv_unch U₁ h7 hn hi (apart_scW h7 hi hK)
  -- `[u]G`.
  have hu : sv c base s U < 2 ^ (8 * c.C.len) := Nat.lt_trans hM.u_lt hc.n_enc
  have hG₁ : Rep c.C (tmv c.C c.n base s₁ (c.sl GX)) (tmv c.C c.n base s₁ (c.sl GY))
      (tmv c.C c.n base s₁ (c.sl ONEP)) (G c.C) := by
    show Rep c.C (toM _ _ (wordsVal s₁.mem _ (c.sl GX) c.n)) (toM _ _ (wordsVal s₁.mem _ (c.sl GY) c.n))
      (toM _ _ (wordsVal s₁.mem _ (c.sl ONEP) c.n)) (G c.C)
    rw [K₁.fixed.gx, K₁.fixed.gy, K₁.fixed.onep, toM_cmont hc, toM_cmont hc, toM_one hpR]
    exact rep_affine' hC _ _
  refine WP.seq (WP.mono (qMul_ok hc h3 hc.mulNf (gx := GX) (gy := GY) (by decide) (by decide) (by decide)
    (by decide) K₁.ws (lt_of_eq_of_lt K₁.fixed.ap (hmont _)) (lt_of_eq_of_lt K₁.fixed.b3p (hmont _))
    (by rw [h1 K₁.fixed]; exact hmont _) (by rw [hz K₁.fixed]; omega_arith)
    (lt_of_eq_of_lt K₁.fixed.gx (hmont _)) (lt_of_eq_of_lt K₁.fixed.gy (hmont _))
    (by rw [v₁ (by decide) (by decide), hM.rx]; omega_arith) (by rw [v₁ (by decide) (by decide), hM.ry]; exact hmont _)
    (by rw [v₁ (by decide) (by decide), hM.rz]; omega_arith) (k := sv c base s U)
    (step_rep' hC hc.onG (ha K₁.fixed) (hb K₁.fixed) hG₁
      (fun h => ⟨by
        simp only [Impl.Ecdsa.PPC64LE.Cfg.qA0, Bool.and_eq_true, beq_iff_eq] at h
        rw [h.2.1]; rfl, by
        show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₁.mem base (c.sl ONEP) c.n) = 1
        rw [K₁.fixed.onep]; exact toM_one (unitMod_pow_two hc.p_odd _)⟩))
    (by
      show Rep c.C (toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ RX)) (toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ RY))
        (toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ RZ)) (mul (sv c base s U >>> (8 * c.C.len)) (G c.C))
      rw [v₁ (by decide) (by decide), v₁ (by decide) (by decide), v₁ (by decide) (by decide), hM.rx, hM.ry,
        hM.rz, toM_cmont hc, toM_zero, shiftRight_eq_zero hu, mul_zero_pt]
      exact rep_infinity' hC)
    (hO K₁.fixed hu) sk₁ b₁) fun s₂ ⟨k₂, U₂, L₂, R₂⟩ => ?_)
  have K₂ := K₁.step h7 k₂ (hU := U₂) (hW := hW) (hWs := hWs)
  -- `U = [u]G`, `R = O`.
  refine WP.seq (WP.mono (save_ok hc K₂.ws) fun s₃ ⟨k₃, U₃, ux₃, uy₃, uz₃, rx₃, ry₃, rz₃⟩ => ?_)
  have K₃ := K₂.step h7 (k₃.rk (rs' := [.r4, .r11])) (hU := U₃) (hW := fixedOk_slW (by decide))
    (hWs := slW_le h7 (by decide))
  have W₃ : ∀ {i}, i < 45 → i ∉ ptsW → sv c base s₃ i = sv c base s i := fun hi hl =>
    (sv_unch U₃ h7 hn hi (apart_slW (nmem_of hl (by decide)))).trans
      ((sv_unch U₂ h7 hn hi (apL hi (nmem_of hl (by decide)))).trans (v₁ hi (ne_of_nmem hl (by decide))))
  -- `v` to where the multiplication reads it.
  refine WP.seq (WP.mono (scalarAt_ok hc K₃.ws (i := V) (by decide) (by decide)) fun s₄ ⟨k₄, U₄, sk₄, b₄⟩ => ?_)
  have K₄ := K₃.step h7 (k₄.rk (rs' := bitsClob)) (hU := U₄) (hW := fixedOk_scW h7) (hWs := scW_le h7)
  have v₄ : ∀ {i}, i < 45 → i ≠ K → sv c base s₄ i = sv c base s₃ i := fun hi hK =>
    sv_unch U₄ h7 hn hi (apart_scW h7 hi hK)
  have e₃V : sv c base s₃ V = sv c base s V := W₃ (by decide) (by decide)
  -- `[v]Q`.
  have hv : sv c base s V < 2 ^ (8 * c.C.len) := Nat.lt_trans hM.v_lt hc.n_enc
  have tv₄ : ∀ {i}, i < 45 → i ∉ ptsW → tmv c.C c.n base s₄ (c.sl i) = tmv c.C c.n base s (c.sl i) :=
    fun hi hl => by
      show toM _ _ (sv c base s₄ _) = toM _ _ (sv c base s _)
      rw [v₄ hi (ne_of_nmem hl (by decide)), W₃ hi hl]
  have hQ₄ : Rep c.C (tmv c.C c.n base s₄ (c.sl PX)) (tmv c.C c.n base s₄ (c.sl PY))
      (tmv c.C c.n base s₄ (c.sl ONEP)) P := by
    rw [tv₄ (by decide) (by decide), tv₄ (by decide) (by decide), tv₄ (by decide) (by decide)]; exact hQ
  refine WP.seq (WP.mono (qMul_ok hc h3 hc.mulNf (gx := PX) (gy := PY) (by decide) (by decide) (by decide)
    (by decide) K₄.ws (lt_of_eq_of_lt K₄.fixed.ap (hmont _)) (lt_of_eq_of_lt K₄.fixed.b3p (hmont _))
    (by rw [h1 K₄.fixed]; exact hmont _) (by rw [hz K₄.fixed]; omega_arith)
    (by rw [v₄ (by decide) (by decide), W₃ (by decide) (by decide)]; exact hM.px_lt)
    (by rw [v₄ (by decide) (by decide), W₃ (by decide) (by decide)]; exact hM.py_lt)
    (by rw [v₄ (by decide) (by decide), rx₃]; omega_arith) (by rw [v₄ (by decide) (by decide), ry₃]; exact hmont _)
    (by rw [v₄ (by decide) (by decide), rz₃]; omega_arith) (k := sv c base s V)
    (step_rep' hC hP (ha K₄.fixed) (hb K₄.fixed) hQ₄
      (fun h => ⟨by
        simp only [Impl.Ecdsa.PPC64LE.Cfg.qA0, Bool.and_eq_true, beq_iff_eq] at h
        rw [h.2.1]; rfl, by
        show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₄.mem base (c.sl ONEP) c.n) = 1
        rw [K₄.fixed.onep]; exact toM_one (unitMod_pow_two hc.p_odd _)⟩))
    (by
      show Rep c.C (toM c.C.p (2 ^ (64 * c.n)) (sv c base s₄ RX)) (toM c.C.p (2 ^ (64 * c.n)) (sv c base s₄ RY))
        (toM c.C.p (2 ^ (64 * c.n)) (sv c base s₄ RZ)) (mul (sv c base s V >>> (8 * c.C.len)) P)
      rw [v₄ (by decide) (by decide), v₄ (by decide) (by decide), v₄ (by decide) (by decide), rx₃, ry₃, rz₃,
        toM_cmont hc, toM_zero, shiftRight_eq_zero hv, mul_zero_pt]
      exact rep_infinity' hC)
    (hO K₄.fixed hv) (fun hs => by rw [sk₄ hs, e₃V]) (fun hN t ht => by rw [b₄ hN t ht, e₃V]))
    fun s₅ ⟨k₅, U₅, L₅, R₅⟩ => ?_)
  have K₅ := K₄.step h7 k₅ (hU := U₅) (hW := (fixedOk_ladWp h3 h7 PX PY).append (fixedOk_genX h7))
    (hWs := le_append (ladWp_le h3 h7 PX PY) (genX_le h7))
  have u₅ : ∀ {i}, i ∈ [UX, UY, UZ] → sv c base s₅ i = sv c base s₃ i := fun {i} hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;>
      exact (sv_unch U₅ h7 hn (by decide) (apL (by decide) (by decide))).trans (v₄ (by decide) (by decide))
  -- The sum.
  refine WP.mono (sum_ok hc K₅ (fun i hi => ?_)) fun s₆ ⟨K₆, U₆, _, _, rz₆, t₆⟩ => h s₆ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt K₅.fixed.ap (hmont _)
    · exact lt_of_eq_of_lt K₅.fixed.b3p (hmont _)
    · rw [u₅ (by decide), ux₃]; exact L₂ _ (List.mem_cons_self ..)
    · rw [u₅ (by decide), uy₃]; exact L₂ _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · rw [u₅ (by decide), uz₃]
      exact L₂ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    · exact L₅ _ (List.mem_cons_self ..)
    · exact L₅ _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · exact L₅ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  -- Facts kept from `s`.
  have W₆ : ∀ {i}, i < 45 → i ∉ ptsW → sv c base s₆ i = sv c base s i := fun hi hl =>
    (sv_unch U₆ h7 hn hi (apart_append (apart_slW (nmem_of hl (by decide))) (apart_own h7 hi))).trans
      ((sv_unch U₅ h7 hn hi (apL hi (nmem_of hl (by decide)))).trans
        ((v₄ hi (ne_of_nmem hl (by decide))).trans (W₃ hi hl)))
  have hFl := sl_le c h7 (i := FLAG) (by decide)
  have flagOk : ∀ {W : List (Nat × Nat)} {m m' : Mem}, Unch base W m m' →
      (∀ w ∈ W, c.sl FLAG + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG) →
      word m' base (c.sl FLAG) = word m base (c.sl FLAG) := fun U ap =>
    U.word (fun w hw => (ap w hw).imp (fun h => by omega_arith) id) (by omega_arith)
  have fl₆ : flagW c base s₆ = flagW c base s := by
    simp only [flagW]
    rw [flagOk U₆ (apart_append (apart_slW (by decide)) (apart_own h7 (by decide))),
      flagOk U₅ (apL (by decide) (by decide)), flagOk U₄ (apart_scW h7 (by decide) (by decide)),
      flagOk U₃ (apart_slW (by decide)), flagOk U₂ (apL (by decide) (by decide)),
      flagOk U₁ (apart_scW h7 (by decide) (by decide))]
  have rm₆ : sv c base s₆ RM' = sv c base s RM' := W₆ (by decide) (by decide)
  have tU : ∀ {i j}, i ∈ [UX, UY, UZ] → sv c base s₃ i = sv c base s₂ j →
      tmv c.C c.n base s₅ (c.sl i) = tmv c.C c.n base s₂ (c.sl j) := fun hi e => by
    show toM _ _ (sv c base s₅ _) = toM _ _ (sv c base s₂ _)
    rw [u₅ hi, e]
  refine ⟨K₆, fun t ht => ?_, by rw [fl₆]; exact hM.flag, by rw [rm₆]; exact hM.rm_lt, by rw [rm₆]; exact hM.rm,
    rz₆, ⟨_, _, _, _, _, _, by rw [Nat.shiftRight_zero] at R₂; exact R₂, by rw [Nat.shiftRight_zero] at R₅; exact R₅,
      by rw [t₆, ha K₅.fixed, hb K₅.fixed, tU (by decide) ux₃, tU (by decide) uy₃, tU (by decide) uz₃]⟩⟩
  rw [tbl_unch U₆ h7 (j := 1) (by decide) ht (apart_append (tbl_apart_slW h7 (by decide) 1 t) (tbl_apart_own h7 1 t)),
    tbl_unch U₅ h7 (j := 1) (by decide) ht (tbL (by decide) ht),
    tbl_unch U₄ h7 (j := 1) (by decide) ht (tbl_apart_scW h7 (by decide) ht),
    tbl_unch U₃ h7 (j := 1) (by decide) ht (tbl_apart_slW h7 (by decide) 1 t),
    tbl_unch U₂ h7 (j := 1) (by decide) ht (tbL (by decide) ht),
    tbl_unch U₁ h7 (j := 1) (by decide) ht (tbl_apart_scW h7 (by decide) ht)]
  exact hM.t₁ t ht

end VG.Proof.Ecdsa.Verify.PPC64LE
