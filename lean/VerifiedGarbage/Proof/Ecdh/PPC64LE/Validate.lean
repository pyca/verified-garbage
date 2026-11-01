module

import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Stages
public import VerifiedGarbage.Impl.Ecdh.PPC64LE
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.PointFprog
import VerifiedGarbage.Proof.Ecdh.PPC64LE.Peer
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.SlotOps
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Copy
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Keep
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Layout
public import VerifiedGarbage.Proof.Weierstrass.Law

/-!
# ECDH on PPC64LE: checking the peer's point

As on 32-bit ARM (`Proof/Ecdh/Arm/Validate.lean`): `mont_ok` puts the
peer's `x` and `y` into Montgomery's form, `curve_ok` computes
`y² - (x³ + a x + b)`, zero iff the point is on the curve, `select_ok` puts
the peer's point, or `G` if the flag is clear, where the ladder takes its
point from, and `validate_ok` is the three, with the mask of the curve's
equation anded into the flag.
-/

@[expose] public section

namespace VG.Proof.Ecdh.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Ecdsa.PPC64LE VG.Spec.Weierstrass
open VG.Impl.Ecdh.PPC64LE (QY R2P BP QXM QYM W0 W1 W2 W3 PX PY)

variable {c : Cfg}

/-! ## Montgomery's form -/

/-- What the two multiplications by `R² mod p` leave. -/
structure MontPost (c : Cfg) (base : Addr) (s s' : State) : Prop where
  ws : WsReg s' base
  rk : Rk fnClob s s'
  unch : Unch base (callW c QXM ++ callW c QYM) s.mem s'.mem
  x_lt : sv c base s' QXM < c.C.p
  x : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' QXM) = Fin.ofNat c.C.p (sv c base s E)
  y_lt : sv c base s' QYM < c.C.p
  y : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' QYM) = Fin.ofNat c.C.p (sv c base s QY)

theorem mont_ok (hc : CfgOk c) {base : Addr} {s : State} (hw : WsReg s base)
    (hr2 : sv c base s R2P = c.R * c.R % c.C.p)
    {rest : Prog isa} {Q : State → Prop} (h : ∀ s', MontPost c base s s' → WP isa rest s' Q) :
    WP isa (.seq (mulCall c.SP (c.sl QXM) (c.sl E) (c.sl R2P))
      (.seq (mulCall c.SP (c.sl QYM) (c.sl QY) (c.sl R2P)) rest)) s Q := by
  have h7 := hc.n10
  have hn := hw.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hr2' : sv c base s R2P = 2 ^ (64 * c.n) * 2 ^ (64 * c.n) % c.C.p := hr2
  refine WP.seq (WP.mono (slMul_ok hc.fp hc.fpk hc.fpm h7 hw (o := QXM) (a := E) (b := R2P) (by decide)
    (by decide) (by decide) (by rw [hr2']; exact Nat.mod_lt _ (by omega_arith))) fun s₁ ⟨k₁, U₁, lt₁, e₁⟩ => ?_)
  have hw₁ := hw.of_rk k₁
  have v₁ : ∀ {i}, i < 45 → i ≠ QXM → sv c base s₁ i = sv c base s i := fun hi h₁ =>
    sv_unch U₁ h7 hn hi (apart_callW h7 hi h₁)
  refine WP.seq (WP.mono (slMul_ok hc.fp hc.fpk hc.fpm h7 hw₁ (o := QYM) (a := QY) (b := R2P) (by decide)
    (by decide) (by decide) (by rw [v₁ (by decide) (by decide), hr2']; exact Nat.mod_lt _ (by omega_arith)))
    fun s₂ ⟨k₂, U₂, lt₂, e₂⟩ => h s₂ ?_)
  have x₂ : sv c base s₂ QXM = sv c base s₁ QXM := sv_unch U₂ h7 hn (by decide) (apart_callW h7 (by decide) (by decide))
  refine ⟨hw₁.of_rk k₂, k₁.trans k₂, U₁.trans U₂, by rw [x₂]; exact lt₁, ?_, lt₂, ?_⟩
  · rw [x₂]; exact toM_r2 hpR (by rw [e₁, hr2'])
  · exact toM_r2 hpR (by rw [e₂, v₁ (i := R2P) (by decide) (by decide), v₁ (i := QY) (by decide) (by decide), hr2'])

/-! ## The curve's equation -/

/-- `curveOps` on slot numbers. -/
def curveN : List FOp :=
  [.mul W0 QYM QYM, .mul W1 QXM QXM, .mul W2 W1 QXM, .mul W1 AP QXM, .add W3 W2 W1,
    .add W2 W3 BP, .sub W1 W0 W2]

theorem curveOps_eq (c : Cfg) : fprog c.SP (Impl.Ecdh.PPC64LE.Cfg.curveOps c) = Point.fprogR c.sl c.SP curveN := rfl

theorem curveN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    runOps curveN e W1 = e QYM * e QYM - ((e QXM * e QXM * e QXM + e AP * e QXM) + e BP) := by
  simp only [curveN, runOps_cons, runOps_nil, FOp.run, Function.update_apply]
  simp only [W0, W1, W2, W3, QYM, QXM, AP, BP, KM, TT, SM, RM, XM, X, EM, Nat.reduceEqDiff, ↓reduceIte]

theorem curveN_reads : readsOk curveN [QXM, QYM, AP, BP] = true := by decide

theorem curveN_ids : ∀ op ∈ curveN, op.out ∈ [W0, W1, W2, W3] ∧ ∀ x ∈ op.out :: op.ins, x < 45 := by decide

/-- The slots `curveN` writes are apart from every other. -/
theorem curveLay (h7 : c.n < 10) : Point.LayR c.n 45 [W0, W1, W2, W3] c.sl where
  le := fun _ hx => sl_below_own c h7 hx
  apart := fun _ _ _ _ hxw => sl_apart c hxw

/-- `curveN` over any modulus `S` of `c.n` words, `m`. -/
theorem curve_core {S : Impl.Weierstrass.Mont.Modulus} {m : Nat} [NeZero m] (hkS : S.k = c.n) (hmS : S.m = m)
    (hM : ModOk c.n m) (h7 : c.n < 10) (hm : UnitMod m (2 ^ (64 * c.n))) {base : Addr} {s : State}
    (hw : WsReg s base) (hlt : ∀ x ∈ [QXM, QYM, AP, BP], sv c base s x < m) :
    WP isa (Point.fprogR c.sl S curveN) s fun s' =>
      Point.KeepR c.n c.sl base (curveN.map FOp.out) s s' ∧
      Point.InvR c.n 45 c.sl base m (validAfter curveN [QXM, QYM, AP, BP])
        (runOps curveN fun x => toM m (2 ^ (64 * c.n)) (sv c base s x)) s' := by
  obtain ⟨cv, w, m', k', d⟩ := S
  dsimp only at hkS hmS
  subst hkS hmS
  exact Point.fprogR_ok (S := ⟨cv, w, m', c.n, d⟩) hM rfl (curveLay h7) hm curveN
    ⟨hw, by decide, hlt, fun _ _ => rfl⟩ curveN_ids curveN_reads

/-- `y² = x³ + a x + b`, in `Fin p`. -/
abbrev OnCurve (c : Cfg) (x y : Fe c.C) : Prop :=
  y * y - ((x * x * x + Fin.ofNat c.C.p c.C.a * x) + Fin.ofNat c.C.p c.C.b) = 0

/-- `y² - (x³ + a x + b)` to `W1`, zero iff the point is on the curve. -/
theorem curve_ok (hc : CfgOk c) {base : Addr} {s : State} (hw : WsReg s base)
    (hx : sv c base s QXM < c.C.p) (hy : sv c base s QYM < c.C.p)
    (hap : sv c base s AP = c.mont c.C.a) (hbp : sv c base s BP = c.mont c.C.b) :
    WP isa (fprog c.SP (Impl.Ecdh.PPC64LE.Cfg.curveOps c)) s fun s' =>
      WsReg s' base ∧ Rk fnClob s s' ∧ Unch base (slW c [W0, W1, W2, W3] ++ [(own c.n, 64 * c.n)]) s.mem s'.mem ∧
      (sv c base s' W1 = 0 ↔ OnCurve c (toM c.C.p (2 ^ (64 * c.n)) (sv c base s QXM))
        (toM c.C.p (2 ^ (64 * c.n)) (sv c base s QYM))) := by
  have h7 := hc.n10
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_arith)
  have hM : ModOk c.n c.C.p := by have := hc.fp; rw [hc.fpk, hc.fpm] at this; exact this
  rw [curveOps_eq]
  refine WP.mono (curve_core hc.fpk hc.fpm hM h7 hpR hw (fun x hx' => ?_)) fun s' ⟨K, I⟩ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
    rcases hx' with rfl | rfl | rfl | rfl
    · exact hx
    · exact hy
    · rw [hap]; exact hmont _
    · rw [hbp]; exact hmont _
  have hW1 : W1 ∈ validAfter curveN [QXM, QYM, AP, BP] := by decide
  have v := I.val W1 hW1
  have lt := I.lt W1 hW1
  rw [curveN_run] at v
  refine ⟨I.ws, ⟨K.gpr, K.rd, K.wr, K.sp⟩, (K.mem : Unch _ _ _ _).mono fun w hw' => ?_, ?_⟩
  · simp only [curveN, List.map_cons, List.map_nil, FOp.out, slW, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hw' ⊢
    grind
  · rw [← toM_eq_zero_iff hpR lt, v]
    show _ * _ - ((_ * _ * _ + toM _ _ (sv c base s AP) * _) + toM _ _ (sv c base s BP)) = 0 ↔ _
    rw [hap, hbp, toM_cmont hc, toM_cmont hc]

/-! ## The point for the ladder -/

theorem select_eq (c : Cfg) : Impl.Ecdh.PPC64LE.Cfg.select c =
    .load .d .r10 wb (c.sl FLAG) ::
    (sel c.n (c.sl PX) (c.sl GX) (c.sl QXM) ++ sel c.n (c.sl PY) (c.sl GY) (c.sl QYM)) := by
  simp only [Impl.Ecdh.PPC64LE.Cfg.select, List.cons_append, List.nil_append]

theorem select_ok (hc : CfgOk c) {base : Addr} {s : State} (hw : WsReg s base) {P : Prop} [Decidable P]
    (hf : flagW c base s = mask64 P) :
    WP isa (.block (Impl.Ecdh.PPC64LE.Cfg.select c)) s fun s' =>
      WsReg s' base ∧ Kp [.r4, .r5, .r10] s s' ∧ Unch base (slW c [PX, PY]) s.mem s'.mem ∧
      sv c base s' PX = (if P then sv c base s QXM else sv c base s GX) ∧
      sv c base s' PY = (if P then sv c base s QYM else sv c base s GY) := by
  have h7 := hc.n10
  have hn := hw.nowrap
  have hsz : size = 8192 := rfl
  have hap : ∀ {i j}, i ≠ j → c.sl i ≤ c.sl j ∨ c.sl j + 8 * c.n ≤ c.sl i := fun h => by
    have := sl_apart c h; omega_arith
  have hle : ∀ {i}, i < 45 → c.sl i + 8 * c.n ≤ size := fun hi => by
    have := sl_le c h7 hi; omega_arith
  rw [select_eq]
  have hF := sl_le c h7 (i := FLAG) (by decide)
  refine wp_step (ld0_ok hw.ws hw.at3 (by decide) (sl_al c FLAG) (by omega_arith)) ?_
  have hc₁ : (s.write .r10 (word s.mem base (c.sl FLAG))).gpr .r10 = if decide P then BitVec.allOnes 64 else 0 := by
    simp only [write_gpr, ite_true]; rw [← flagW, hf]; simp only [mask64, decide_eq_true_eq]
  have hs₁ := hw.ws.write .r10 (word s.mem base (c.sl FLAG))
  have h3₁ := hw.at3.write (d := .r10) (word s.mem base (c.sl FLAG))
  refine wp_append (WP.mono (sel_ok (decide P) c.n hs₁ h3₁ hc₁ (sl_al c _) (sl_al c _) (sl_al c _)
    (hle (i := PX) (by decide)) (hle (i := GX) (by decide)) (hle (i := QXM) (by decide)) (hap (by decide))
    (hap (by decide))) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_)
  have hc₂ : s₂.gpr .r10 = if decide P then BitVec.allOnes 64 else 0 := by rw [k₂.gpr _ (by decide), hc₁]
  refine WP.mono (sel_ok (decide P) c.n (k₂.ws hs₁) (k₂.at h3₁) hc₂ (sl_al c _) (sl_al c _) (sl_al c _)
    (hle (i := PY) (by decide)) (hle (i := GY) (by decide)) (hle (i := QYM) (by decide)) (hap (by decide))
    (hap (by decide))) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have K₃ : Kp [.r4, .r5, .r10] s s₃ :=
    ((Kp.write _ _ (by decide)).trans (k₂.mono (by decide))).trans (k₃.mono (by decide))
  refine ⟨hw.of_kp K₃, K₃, ?_, ?_, ?_⟩
  · have := O₂.unch.trans O₃.unch
    exact this
  · show wordsVal s₃.mem _ _ _ = _
    rw [sv_unch O₃.unch h7 hn (i := PX) (by decide) (apart_slW (c := c) (l := [PY]) (by decide)), e₂]
    by_cases hP : P <;> simp [hP]
  · show wordsVal s₃.mem _ _ _ = _
    rw [e₃, sv_unch O₂.unch h7 hn (i := QYM) (by decide) (apart_slW (c := c) (l := [PX]) (by decide)),
      sv_unch O₂.unch h7 hn (i := GY) (by decide) (apart_slW (c := c) (l := [PX]) (by decide))]
    by_cases hP : P <;> simp [hP]

/-! ## The whole validation -/

/-- The working-space ranges of a stage are in the working space. -/
theorem le_append {W W' : List (Nat × Nat)} (h : ∀ w ∈ W, w.1 + w.2 ≤ size) (h' : ∀ w ∈ W', w.1 + w.2 ≤ size) :
    ∀ w ∈ W ++ W', w.1 + w.2 ≤ size := fun w hw => (List.mem_append.mp hw).elim (h w) (h' w)

/-- The peer's point is valid as the code checks it: `P₀` (its first byte
and the range of its coordinates) and the curve's equation. -/
abbrev PeerOk (c : Cfg) (base : Addr) (s : State) (P₀ : Prop) : Prop :=
  P₀ ∧ OnCurve c (Fin.ofNat c.C.p (sv c base s E)) (Fin.ofNat c.C.p (sv c base s QY))

/-- What the validation writes. -/
abbrev valW (c : Cfg) : List (Nat × Nat) :=
  slW c [QXM, QYM, W0, W1, W2, W3, PY] ++ [(own c.n, 64 * c.n), (c.sl FLAG, 8)]

theorem fixedOk_valW (h7 : c.n < 10) : FixedOk c (valW c) :=
  show FixedOk c (slW c [QXM, QYM, W0, W1, W2, W3, PY] ++ ([(own c.n, 64 * c.n)] ++ [(c.sl FLAG, 8)])) from
    (fixedOk_slW (by decide)).append (FixedOk.append (W := [(own c.n, 64 * c.n)]) (fun w hw => by
      rw [List.mem_singleton.mp hw]
      exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_below_own c h7 (i := 12) (by decide))))
      fixedOk_flag)

theorem valW_le (h7 : c.n < 10) : ∀ w ∈ valW c, w.1 + w.2 ≤ size := by
  have hsz : size = 8192 := rfl
  have ho := own_below_bits c h7 0
  have hb := bitsAt_le c h7 (j := 0) (by decide)
  have hF := sl_le c h7 (i := FLAG) (by decide)
  refine le_append (fun w hw => ?_) (fun w hw => ?_)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    have hl : ∀ i ∈ [QXM, QYM, W0, W1, W2, W3, PY], i < 45 := by decide
    have := sl_le c h7 (hl i hi)
    dsimp only; omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl <;> (dsimp only; omega_arith)

theorem tbl_apart_valW (h7 : c.n < 10) (h0 : 0 < c.n) (j t : Nat) :
    ∀ w ∈ valW c, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t :=
  apart_append (tbl_apart_slW h7 (by decide) j t)
    (show ∀ w ∈ [(own c.n, 64 * c.n)] ++ [(c.sl FLAG, 8)], _ from
      apart_append (tbl_apart_own h7 j t) (tbl_apart_flag h7 h0 j t))

theorem validate_eq (c : Cfg) : Impl.Ecdh.PPC64LE.Cfg.validate c =
    .seq (mulCall c.SP (c.sl QXM) (c.sl E) (c.sl R2P)) (.seq (mulCall c.SP (c.sl QYM) (c.sl QY) (c.sl R2P))
      (.seq (fprog c.SP (Impl.Ecdh.PPC64LE.Cfg.curveOps c))
      (.block (Impl.Ecdh.PPC64LE.Cfg.checkZero c (c.sl W1) ++ Impl.Ecdh.PPC64LE.Cfg.select c)))) := rfl

/-- A word apart from what a stage writes. -/
theorem flag_unch (h7 : c.n < 10) (h0 : 0 < c.n) {base : Addr} {W : List (Nat × Nat)} {m m' : Mem}
    (hu : Unch base W m m') (hW : ∀ w ∈ W, c.sl FLAG + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG) :
    word m' base (c.sl FLAG) = word m base (c.sl FLAG) :=
  hu.word (fun w hw => (hW w hw).imp (fun h => by omega_arith) id)
    (by have := sl_le c h7 (i := FLAG) (by decide); omega_arith)

theorem validate_ok (hc : CfgOk c) {base : Addr} {s : State} (hw : WsReg s base) {g : Reg → BitVec 64}
    {lr : BitVec 64} (F : Fixed c base g lr s.mem) (hr2 : sv c base s R2P = c.R * c.R % c.C.p)
    (hbp : sv c base s BP = c.mont c.C.b) {P₀ : Prop} [Decidable P₀] (hf : flagW c base s = mask64 P₀) :
    WP isa (Impl.Ecdh.PPC64LE.Cfg.validate c) s fun s' =>
      WsReg s' base ∧ Rk fnClob s s' ∧ Unch base (valW c) s.mem s'.mem ∧
      flagW c base s' = mask64 (PeerOk c base s P₀) ∧
      sv c base s' PX < c.C.p ∧ sv c base s' PY < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' PX) =
        (if PeerOk c base s P₀ then Fin.ofNat c.C.p (sv c base s E) else Fin.ofNat c.C.p c.C.gx) ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' PY) =
        (if PeerOk c base s P₀ then Fin.ofNat c.C.p (sv c base s QY) else Fin.ofNat c.C.p c.C.gy) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hw.nowrap
  have hp3 := hc.p_ge
  have hsz : size = 8192 := rfl
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_arith)
  have hF : c.sl FLAG + 8 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega_arith
  rw [validate_eq]
  refine mont_ok hc hw hr2 fun s₂ Mp => ?_
  have F₂ := F.unch h7 hn ((fixedOk_callW h7 (o := QXM) (by decide)).append (fixedOk_callW h7 (o := QYM) (by decide)))
    Mp.unch
  have e₂ : ∀ {i}, i < 45 → i ∉ [QXM, QYM] → sv c base s₂ i = sv c base s i := fun hi hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hl
    exact sv_unch Mp.unch h7 hn hi (apart_append (apart_callW h7 hi hl.1) (apart_callW h7 hi hl.2))
  refine WP.seq (WP.mono (curve_ok hc Mp.ws Mp.x_lt Mp.y_lt F₂.ap
    (by rw [e₂ (i := BP) (by decide) (by decide)]; exact hbp)) fun s₃ ⟨hw₃, k₃, U₃, z₃⟩ => ?_)
  rw [Mp.x, Mp.y] at z₃
  refine wp_append (WP.mono (checkZero_ok c hw₃.ws hw₃.at3 (sl_al c W1) h0
    (by have := sl_le c h7 (i := W1) (by decide); omega_arith) hF) fun s₄ ⟨f₄, k₄, O₄⟩ => ?_)
  have hw₄ := hw₃.of_kp k₄
  have apC : ∀ w ∈ slW c [W0, W1, W2, W3] ++ [(own c.n, 64 * c.n)],
      c.sl FLAG + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG :=
    apart_append (apart_slW (c := c) (l := [W0, W1, W2, W3]) (i := FLAG) (by decide)) (apart_own h7 (by decide))
  have hf₄ : flagW c base s₄ = mask64 (PeerOk c base s P₀) := by
    rw [f₄, flagW, flag_unch h7 h0 U₃ apC, flag_unch h7 h0 Mp.unch
      (apart_append (apart_callW h7 (by decide) (by decide)) (apart_callW h7 (by decide) (by decide))), ← flagW,
      hf, mask64_and]
    simp only [mask64, z₃]
  have U₄ : Unch base (slW c [W0, W1, W2, W3] ++ [(own c.n, 64 * c.n)] ++ [(c.sl FLAG, 8)]) s₂.mem s₄.mem :=
    U₃.trans O₄.unch
  have F₄ := F₂.unch h7 hn (((fixedOk_slW (l := [W0, W1, W2, W3]) (by decide)).append
    (fun w hw => by
      rw [List.mem_singleton.mp hw]
      exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_below_own c h7 (i := 12) (by decide))))).append
    fixedOk_flag) U₄
  refine WP.mono (select_ok hc hw₄ hf₄) fun s₆ ⟨hw₆, k₆, U₆, px, py⟩ => ?_
  have q₄ : ∀ {i}, i < 45 → i ∉ [W0, W1, W2, W3] → i ≠ FLAG → sv c base s₄ i = sv c base s₂ i :=
    fun hi hl hfl => sv_unch U₄ h7 hn hi (apart_append (apart_append (apart_slW hl) (apart_own h7 hi))
      (apart_flag h0 hfl))
  have qx : sv c base s₄ QXM = sv c base s₂ QXM := q₄ (by decide) (by decide) (by decide)
  have qy : sv c base s₄ QYM = sv c base s₂ QYM := q₄ (by decide) (by decide) (by decide)
  refine ⟨hw₆, (k₃.trans (k₄.rk (rs' := fnClob))).trans (k₆.rk (rs' := fnClob)) |> Mp.rk.trans, ?_,
    by rw [flagW, flag_unch h7 h0 U₆ (apart_slW (c := c) (l := [PX, PY]) (i := FLAG) (by decide)), ← flagW]; exact hf₄,
    ?_, ?_, ?_, ?_⟩
  · refine ((Mp.unch.trans U₄).trans U₆).mono fun w hw' => ?_
    simp only [callW, slW, List.map_cons, List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hw' ⊢
    simp only [PX, W3] at hw' ⊢
    grind
  · rw [px]; split
    · rw [qx]; exact Mp.x_lt
    · exact lt_of_eq_of_lt F₄.gx (hmont _)
  · rw [py]; split
    · rw [qy]; exact Mp.y_lt
    · exact lt_of_eq_of_lt F₄.gy (hmont _)
  · rw [px]; split
    · rw [qx, Mp.x]
    · show toM _ _ (wordsVal s₄.mem base (c.sl GX) c.n) = _
      rw [F₄.gx, toM_cmont hc]
  · rw [py]; split
    · rw [qy, Mp.y]
    · show toM _ _ (wordsVal s₄.mem base (c.sl GY) c.n) = _
      rw [F₄.gy, toM_cmont hc]

end VG.Proof.Ecdh.PPC64LE
