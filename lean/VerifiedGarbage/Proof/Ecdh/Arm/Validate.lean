import VerifiedGarbage.Proof.Ecdh.Arm.Peer
import VerifiedGarbage.Proof.Ecdsa.Arm.Lays
import VerifiedGarbage.Proof.Ecdsa.Arm.Middle
import VerifiedGarbage.Proof.Ecdsa.Arm.Main

/-!
# ECDH on 32-bit ARM: the peer's point, `[d]P` and `Z^(p-2)`

As on x86 (`Proof/Ecdh/X86/Validate.lean`).

## The peer's point

`validate` takes the peer's `x` and `y` into Montgomery's form
(multiplications by `R² mod p`, `mont_ok`), computes `y² - (x³ + a x + b)`
(`curveOps`, a field program, by `fprog_ok`: `curve_ok`), ands the mask of
its being zero into the flag, and selects for the ladder the peer's point if
the flag is set, else `G` (`select_ok`): `validate_ok`.
-/

namespace VG.Proof.Ecdh.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm
open VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.Arm
open VG.Proof.X25519.Arm (Rest wp_ldr)
open VG.Impl.Ecdh.Arm (QY R2P BP QXM QYM W0 W1 W2 W3 PX PY)

variable {c : Cfg}

/-- The working-space ranges of a stage are in the working space. -/
theorem le_append {W W' : List (Nat × Nat)} (h : ∀ w ∈ W, w.1 + w.2 ≤ size) (h' : ∀ w ∈ W', w.1 + w.2 ≤ size) :
    ∀ w ∈ W ++ W', w.1 + w.2 ≤ size := fun w hw => by
  rcases List.mem_append.mp hw with hw | hw
  · exact h w hw
  · exact h' w hw

/-- `curveOps` on slot numbers. -/
def curveN : List FOp :=
  [.mul W0 QYM QYM, .mul W1 QXM QXM, .mul W2 W1 QXM, .mul W1 AP QXM, .add W3 W2 W1,
    .add W2 W3 BP, .sub W1 W0 W2]

theorem curveOps_eq (c : Cfg) : Impl.Ecdh.Arm.Cfg.curveOps c = curveN.map (FOp.rename c.sl) := rfl

theorem curveN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    runOps curveN e W1 = e QYM * e QYM - ((e QXM * e QXM * e QXM + e AP * e QXM) + e BP) := by
  simp only [curveN, runOps_cons, runOps_nil, FOp.run, Function.update_apply]
  simp only [W0, W1, W2, W3, QYM, QXM, AP, BP, KM, TT, SM, RM, XM, X, EM, Nat.reduceEqDiff, ↓reduceIte]

theorem curveN_reads : readsOk curveN [QXM, QYM, AP, BP] = true := by decide

/-- The slots of the check. -/
abbrev curveSl : List Nat := [QXM, QYM, AP, BP, W0, W1, W2, W3]

theorem curveN_slots : ∀ op ∈ curveN, ∀ x ∈ op.out :: op.ins, x ∈ curveSl := by decide

theorem curveN_out : ∀ op ∈ curveN, op.out ∈ [W0, W1, W2, W3, TMP] := by decide

/-! ## Montgomery's form -/

/-- What the two multiplications by `R² mod p` leave. -/
structure MontPost (c : Cfg) (base : Addr) (s s' : State) : Prop where
  scr : Scr s' base size
  rest : Rest clob s s'
  unch : Unch base (slWk c [QXM, QYM, TMP]) s.mem s'.mem
  mod : ModOkW c.MP' size c.C.p s'.mem base
  x_lt : sv c base s' QXM < c.C.p
  x : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' QXM) = Fin.ofNat c.C.p (sv c base s E)
  y_lt : sv c base s' QYM < c.C.p
  y : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' QYM) = Fin.ofNat c.C.p (sv c base s QY)

theorem mont_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    (hM : ModOkW c.MP' size c.C.p s.mem base) (hr2 : sv c base s R2P = c.R * c.R % c.C.p)
    {rest : Prog isa} {Q : State → Prop} (h : ∀ s', MontPost c base s s' → WP isa rest s' Q) :
    WP isa (.seq (mul c.MP' c.wk (c.sl QXM) (c.sl E) (c.sl R2P))
      (.seq (mul c.MP' c.wk (c.sl QYM) (c.sl QY) (c.sl R2P)) rest)) s Q := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hr2' : sv c base s R2P = 2 ^ (64 * c.n) * 2 ^ (64 * c.n) % c.C.p := hr2
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) (.inl rfl) rfl h7 hs hM (o := QXM) (a := E) (b := R2P) (by decide)
    (by decide) (by decide) (by decide) (by rw [hr2']; exact Nat.mod_lt _ (by omega))) fun s₁ ⟨k₁, lt₁, e₁⟩ => ?_)
  have hs₁ := k₁.scr hs
  have kP₁ := hM.keepArm (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  have r2₁ : sv c base s₁ R2P = sv c base s R2P :=
    sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)
  have y₁ : sv c base s₁ QY = sv c base s QY := sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) (.inl rfl) rfl h7 hs₁ kP₁ (o := QYM) (a := QY) (b := R2P) (by decide)
    (by decide) (by decide) (by decide) (by rw [r2₁, hr2']; exact Nat.mod_lt _ (by omega)))
    fun s₂ ⟨k₂, lt₂, e₂⟩ => h s₂ ?_)
  have x₂ : sv c base s₂ QXM = sv c base s₁ QXM :=
    sv_keep (MP'_n c) rfl h7 hn k₂ (by decide) (by decide) (by decide)
  refine ⟨k₂.scr hs₁, k₁.rest.trans k₂.rest, ?_, kP₁.keepArm (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₂ (by decide) (by decide),
    by rw [x₂]; exact lt₁, ?_, lt₂, ?_⟩
  · exact ((unch_slots (MP'_n c) rfl k₁.unch (l := [QXM, QYM, TMP]) (by simp) (by simp)).trans
      (unch_slots (MP'_n c) rfl k₂.unch (l := [QXM, QYM, TMP]) (by simp) (by simp))).mono
      fun w hw => by simpa only [List.mem_append, or_self] using hw
  · rw [x₂]; exact toM_r2 hpR (by rw [e₁, hr2'])
  · exact toM_r2 hpR (by rw [e₂, r2₁, y₁, hr2'])

/-! ## The curve's equation -/

/-- `y² = x³ + a x + b`, in `Fin p`. -/
abbrev OnCurve (c : Cfg) (x y : Fe c.C) : Prop :=
  y * y - ((x * x * x + Fin.ofNat c.C.p c.C.a * x) + Fin.ofNat c.C.p c.C.b) = 0

/-- `y² - (x³ + a x + b)` to `W1`, zero iff the point is on the curve. -/
theorem curve_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    (hM : ModOkW c.MP' size c.C.p s.mem base) (hx : sv c base s QXM < c.C.p) (hy : sv c base s QYM < c.C.p)
    (hap : sv c base s AP = c.mont c.C.a) (hbp : sv c base s BP = c.mont c.C.b) :
    WP isa (fprog c.MP' c.wk (Impl.Ecdh.Arm.Cfg.curveOps c)) s fun s' =>
      Scr s' base size ∧ Rest clob s s' ∧ Unch base (slWk c [W0, W1, W2, W3, TMP]) s.mem s'.mem ∧
      (sv c base s' W1 = 0 ↔ OnCurve c (toM c.C.p (2 ^ (64 * c.n)) (sv c base s QXM))
        (toM c.C.p (2 ^ (64 * c.n)) (sv c base s QYM))) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hL : Lay c.MP' size (· ∈ curveSl.map c.sl) := lay_map hc rfl rfl rfl (by decide)
  have hW : WkOk c.MP' size c.wk (· ∈ curveSl.map c.sl) := ⟨wk_le c h7 rfl, fun x hx => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have : ∀ i ∈ curveSl, i < 45 := by decide
      exact sl_below_wk c (this i hi),
    sl_below_wk c (i := MP) (by decide), sl_below_wk c (i := TMP) (by decide)⟩
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega)
  have I : Inv c.MP' base size c.C.p (· ∈ curveSl.map c.sl) ([QXM, QYM, AP, BP].map c.sl)
      (fun o => toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base o c.n)) s := by
    refine ⟨hs, hM, fun x hx => ?_, fun x hx => ?_, fun _ _ => rfl⟩
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have sub : ∀ i ∈ [QXM, QYM, AP, BP], i ∈ curveSl := by decide
      exact List.mem_map_of_mem (sub i hi)
    · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hx
      · exact hy
      · show sv c base s AP < _; rw [hap]; exact hmont _
      · show sv c base s BP < _; rw [hbp]; exact hmont _
  refine WP.mono (fprog_ok hL hW hpR (Impl.Ecdh.Arm.Cfg.curveOps c) I (fun op hop x hx => ?_)
    (by rw [curveOps_eq]; exact readsOk_rename c.sl curveN_reads)) fun s₃ ⟨PK, I₃⟩ => ?_
  · rw [curveOps_eq] at hop
    obtain ⟨op₀, h₀, rfl⟩ := List.mem_map.mp hop
    have hx' : x ∈ (op₀.out :: op₀.ins).map c.sl := by
      cases op₀ <;> simpa [FOp.rename, FOp.out, FOp.ins] using hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    exact List.mem_map_of_mem (curveN_slots op₀ h₀ i hi)
  have hW1 : c.sl W1 ∈ validAfter (Impl.Ecdh.Arm.Cfg.curveOps c) ([QXM, QYM, AP, BP].map c.sl) :=
    (mem_validAfter _ _).mpr (Or.inr (by simp [Impl.Ecdh.Arm.Cfg.curveOps, FOp.out]))
  have v₃ : toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₃.mem base (c.sl W1) c.n) = _ := I₃.val _ hW1
  have lt₃ : wordsVal s₃.mem base (c.sl W1) c.n < c.C.p := I₃.lt _ hW1
  rw [curveOps_eq, congrFun (runOps_rename c.sl curveN _ fun _ _ y h => sl_inj c h0 h) W1,
    curveN_run] at v₃
  refine ⟨I₃.scr, PK.rest, (Outs.unch PK.mem).mono fun w hw => ?_, ?_⟩
  · simp only [progW] at hw
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hw
      rw [curveOps_eq, List.map_map] at ho
      obtain ⟨op₀, h₀, rfl⟩ := List.mem_map.mp ho
      exact List.mem_append_left _ (List.mem_map.mpr ⟨op₀.out, curveN_out op₀ h₀, by
        rw [Function.comp_apply, FOp.out_rename]; rfl⟩)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact List.mem_append_left _ (List.mem_map_of_mem (f := fun i => (c.sl i, 8 * c.n))
          (show TMP ∈ [W0, W1, W2, W3, TMP] by decide))
      · exact List.mem_append_right _ (by rw [accLen_MP']; exact List.mem_singleton_self _)
  · rw [← toM_eq_zero_iff hpR lt₃, v₃]
    show _ * _ - ((_ * _ * _ + toM _ _ (sv c base s AP) * _) + toM _ _ (sv c base s BP)) = 0 ↔ _
    rw [hap, hbp, toM_cmont hc, toM_cmont hc]

/-! ## The point for the ladder -/

theorem select_eq (c : Cfg) : Impl.Ecdh.Arm.Cfg.select c =
    .ldr .r10 wb (c.sl FLAG) ::
    (sel (2 * c.n) (c.sl PX) (c.sl GX) (c.sl QXM) ++ sel (2 * c.n) (c.sl PY) (c.sl GY) (c.sl QYM)) := by
  simp only [Impl.Ecdh.Arm.Cfg.select, List.cons_append, List.nil_append]

theorem select_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size) {P : Prop} [Decidable P]
    (hf : flagW c base s = mask32 P) :
    WP isa (.block (Impl.Ecdh.Arm.Cfg.select c)) s fun s' =>
      Scr s' base size ∧ Rest [.r4, .r5, .r10] s s' ∧ Unch base (slW c [PX, PY]) s.mem s'.mem ∧
      sv c base s' PX = (if P then sv c base s QXM else sv c base s GX) ∧
      sv c base s' PY = (if P then sv c base s QYM else sv c base s GY) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hap : ∀ {i j}, i ≠ j → c.sl i ≤ c.sl j ∨ c.sl j + 4 * (2 * c.n) ≤ c.sl i := fun h => by
    have := sl_apart c h; omega
  have hle : ∀ {i}, i < 45 → c.sl i + 4 * (2 * c.n) ≤ size := fun hi => by
    have := sl_le c h7 hi; omega
  rw [select_eq]
  have hF := sl_le c h7 (i := FLAG) (by decide)
  refine wp_ldr (hs.off_lt (by omega)) (hs.ea (by omega)) (hs.read (d := c.sl FLAG) (n := 4) (by omega))
    fun s₁ u₁ => ?_
  have k₁ : Rest [.r4, .r5, .r10] s s₁ := u₁.rest (by simp)
  have hs₁ := hs.of_rest k₁ (by decide)
  have hc₁ : s₁.gpr .r10 = if decide P then BitVec.allOnes 32 else 0 := by
    rw [u₁.gpr, ← flagW, hf]; simp only [mask32, decide_eq_true_eq]
  refine VG.Proof.X25519.Arm.WP.append (sel_ok (decide P) (2 * c.n) hs₁ hc₁ (hle (i := PX) (by decide))
    (hle (i := GX) (by decide)) (hle (i := QXM) (by decide)) (hap (by decide)) (hap (by decide)))
    fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_rest k₂ (by decide)
  have hc₂ : s₂.gpr .r10 = if decide P then BitVec.allOnes 32 else 0 := by rw [k₂.gpr _ (by decide), hc₁]
  refine WP.mono (sel_ok (decide P) (2 * c.n) hs₂ hc₂ (hle (i := PY) (by decide))
    (hle (i := GY) (by decide)) (hle (i := QYM) (by decide)) (hap (by decide)) (hap (by decide)))
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hm₁ : s₁.mem = s.mem := u₁.mem
  have O₂' : Outside base (c.sl PX) (8 * c.n) s₁.mem s₂.mem := by
    rw [show 8 * c.n = 4 * (2 * c.n) by omega]; exact O₂
  have O₃' : Outside base (c.sl PY) (8 * c.n) s₂.mem s₃.mem := by
    rw [show 8 * c.n = 4 * (2 * c.n) by omega]; exact O₃
  refine ⟨hs₂.of_rest k₃ (by decide), k₁.trans ((k₂.mono (by simp)).trans (k₃.mono (by simp))), ?_, ?_, ?_⟩
  · have := O₂'.unch.trans O₃'.unch
    rw [hm₁] at this
    exact this.mono fun w hw => by simpa using hw
  · show wordsVal s₃.mem _ _ _ = _
    rw [sv_out O₃' h7 hn (by decide) (by decide), wordsVal_eq_val32, e₂, hm₁, ← wordsVal_eq_val32,
      ← wordsVal_eq_val32]
    by_cases hP : P <;> simp [hP]
  · show wordsVal s₃.mem _ _ _ = _
    rw [wordsVal_eq_val32, e₃, ← wordsVal_eq_val32, ← wordsVal_eq_val32,
      sv_out O₂' h7 hn (by decide) (by decide), sv_out O₂' h7 hn (by decide) (by decide), hm₁]
    by_cases hP : P <;> simp [hP]

/-! ## The whole validation -/

/-- The peer's point is valid as the code checks it: `P₀` (its first byte
and the range of its coordinates) and the curve's equation. -/
abbrev PeerOk (c : Cfg) (base : Addr) (s : State) (P₀ : Prop) : Prop :=
  P₀ ∧ OnCurve c (Fin.ofNat c.C.p (sv c base s E)) (Fin.ofNat c.C.p (sv c base s QY))

theorem validate_eq (c : Cfg) : Impl.Ecdh.Arm.Cfg.validate c =
    .seq (mul c.MP' c.wk (c.sl QXM) (c.sl E) (c.sl R2P)) (.seq (mul c.MP' c.wk (c.sl QYM) (c.sl QY) (c.sl R2P))
      (.seq (fprog c.MP' c.wk (Impl.Ecdh.Arm.Cfg.curveOps c))
      (.block (Impl.Ecdh.Arm.Cfg.checkZero c (c.sl W1) ++ Impl.Ecdh.Arm.Cfg.select c)))) := rfl

theorem validate_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    {g : Reg → BitVec 32} (F : Fixed c base g s.mem) (hr2 : sv c base s R2P = c.R * c.R % c.C.p)
    (hbp : sv c base s BP = c.mont c.C.b) {P₀ : Prop} [Decidable P₀]
    (hf : flagW c base s = mask32 P₀) :
    WP isa (Impl.Ecdh.Arm.Cfg.validate c) s fun s' =>
      Scr s' base size ∧ Rest powClob s s' ∧
      Unch base (slWk c [QXM, QYM, TMP, W0, W1, W2, W3, PY] ++ [(c.sl FLAG, 4)]) s.mem s'.mem ∧
      flagW c base s' = mask32 (PeerOk c base s P₀) ∧
      sv c base s' PX < c.C.p ∧ sv c base s' PY < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' PX) =
        (if PeerOk c base s P₀ then Fin.ofNat c.C.p (sv c base s E) else Fin.ofNat c.C.p c.C.gx) ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' PY) =
        (if PeerOk c base s P₀ then Fin.ofNat c.C.p (sv c base s QY) else Fin.ofNat c.C.p c.C.gy) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hp3 := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega)
  have hF : c.sl FLAG + 4 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega
  rw [validate_eq]
  refine mont_ok hc hs (modP_of hc F.mp) hr2 fun s₂ Mp => ?_
  have F₂ := F.unch h7 hn (fixedOk_slWk (l := [QXM, QYM, TMP]) (by decide)) Mp.unch
  have e₂ : ∀ {i}, i < 45 → i ∉ [QXM, QYM, TMP] → sv c base s₂ i = sv c base s i := fun hi hl =>
    sv_unch Mp.unch h7 hn hi (apart_slWk hi hl)
  refine WP.seq (WP.mono (curve_ok hc Mp.scr Mp.mod Mp.x_lt Mp.y_lt F₂.ap
    (by rw [e₂ (i := BP) (by decide) (by decide)]; exact hbp)) fun s₃ ⟨hs₃, g₃, U₃, z₃⟩ => ?_)
  rw [Mp.x, Mp.y] at z₃
  refine VG.Proof.X25519.Arm.WP.append (checkZero_ok c hs₃ h0 (sl_le c h7 (i := W1) (by decide)) hF)
    fun s₄ ⟨f₄, k₄, O₄⟩ => ?_
  have hs₄ := hs₃.of_rest k₄ (by decide)
  have hf₄ : flagW c base s₄ = mask32 (PeerOk c base s P₀) := by
    rw [f₄, flagW, flag_unch U₃ h7 h0 hn (by decide), flag_unch Mp.unch h7 h0 hn (by decide), ← flagW, hf,
      mask32_and]
    simp only [mask32, z₃]
  have U₄ : Unch base (slWk c [W0, W1, W2, W3, TMP] ++ [(c.sl FLAG, 4)]) s₂.mem s₄.mem := U₃.trans O₄.unch
  have F₄ := F₂.unch h7 hn ((fixedOk_slWk (l := [W0, W1, W2, W3, TMP]) (by decide)).append fixedOk_flag) U₄
  refine WP.mono (select_ok hc hs₄ hf₄) fun s₆ ⟨hs₆, k₆, U₆, px, py⟩ => ?_
  have q₄ : ∀ {i}, i < 45 → i ∉ [W0, W1, W2, W3, TMP] → i ≠ FLAG → sv c base s₄ i = sv c base s₂ i :=
    fun hi hl hf => sv_unch U₄ h7 hn hi (apart_append (apart_slWk hi hl) (apart_flag h0 hf))
  have qx : sv c base s₄ QXM = sv c base s₂ QXM := q₄ (by decide) (by decide) (by decide)
  have qy : sv c base s₄ QYM = sv c base s₂ QYM := q₄ (by decide) (by decide) (by decide)
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  refine ⟨hs₆, ?_, ?_,
    by rw [flagW, flag_unch (U₆.mono fun w hw => List.mem_append_left _ hw) h7 h0 hn (l := [PX, PY]) (by decide), ← flagW]; exact hf₄, ?_, ?_, ?_, ?_⟩
  · exact ((Mp.rest.trans g₃).mono (by decide)).trans ((k₄.mono (by decide)).trans (k₆.mono (by decide)))
  · have sub : ∀ i ∈ [QXM, QYM, TMP, W0, W1, W2, W3, TMP, PX, PY], i ∈ [QXM, QYM, TMP, W0, W1, W2, W3, PY] := by
      decide
    have hsl : ∀ {l : List Nat}, (∀ i ∈ l, i ∈ [QXM, QYM, TMP, W0, W1, W2, W3, TMP, PX, PY]) →
        ∀ w ∈ slW c l, w ∈ slWk c [QXM, QYM, TMP, W0, W1, W2, W3, PY] ++ [(c.sl FLAG, 4)] := fun hl w hw => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem (sub i (hl i hi))))
    have hwk : (c.wk, 32 * c.n + 8) ∈ slWk c [QXM, QYM, TMP, W0, W1, W2, W3, PY] ++ [(c.sl FLAG, 4)] :=
      List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))
    refine ((Mp.unch.trans U₄).trans U₆).mono fun w hw => ?_
    simp only [List.mem_append, List.mem_singleton] at hw
    rcases hw with ((hw | hw) | ((hw | hw) | hw)) | hw
    · exact hsl (by decide) w hw
    · rw [hw]; exact hwk
    · exact hsl (by decide) w hw
    · rw [hw]; exact hwk
    · rw [hw]; exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact hsl (by decide) w hw
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

/-!
## `[d]P` and `Z^(p-2)`

The signature's ladder with its point at `PX`, `PY`, `ONEP` (`ladderQ`),
whose slots are apart as `ladder_ok` needs (`ladLayQ`, `ladWkQ`, as
`ladLay` and `ladWk`), then the signature's power (`ladPow_ok`, as
`stage₂`), for any invariant of the ladder: `Main.lean` gives the one of the
group law, that `R` represents `[k >>> j]P`.
-/

theorem ladLayQ (hc : CfgOk c) : LadLay (Impl.Ecdh.Arm.Cfg.ladderQ c) size 8192 := by
  have hn := hc.n0
  have h7 := hc.n10
  refine ⟨?_, rcbApart_of hn (lw := [T0, T1, T2, T3, T4, T5, DX, DY, DZ])
      (lr := [AP, B3P, RX, RY, RZ, RX, RY, RZ]) rfl rfl (by decide) (by decide),
    rcbApart_of hn (lw := [T0, T1, T2, T3, T4, T5, TX, TY, TZ])
      (lr := [AP, B3P, DX, DY, DZ, PX, PY, ONEP]) rfl rfl (by decide) (by decide), ?_,
    ⟨fun h => by have := sl_inj c hn h; exact absurd this (by decide),
      fun h => by have := sl_inj c hn h; exact absurd this (by decide),
      fun h => by have := sl_inj c hn h; exact absurd this (by decide)⟩, ?_,
    ⟨show 1 ≤ 64 * c.n by omega, show 64 * c.n < 2 ^ 16 by omega⟩,
    bitsAt_le c h7 (j := 0) (by decide), ?_⟩
  · exact lay_map hc rfl rfl rfl (l := [AP, B3P, PX, PY, ONEP, RX, RY, RZ, T0, T1, T2, T3, T4, T5,
      DX, DY, DZ, TX, TY, TZ]) (by decide)
  · exact map_sl_disj hn (l₁ := [AP, B3P, PX, PY, ONEP])
      (l₂ := [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ])
      (by decide)
  · exact map_sl_disj hn (l₁ := [RX, RY, RZ]) (l₂ := [DX, DY, DZ, TX, TY, TZ]) (by decide)
  · intro w hw
    simp only [ladW, List.mem_append, List.mem_map, List.mem_singleton] at hw
    rcases hw with ⟨y, hy, rfl⟩ | rfl
    · have hy' : y ∈ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX,
          TY, TZ].map c.sl := hy
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy'
      have hl : ∀ i ∈ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX,
          TY, TZ], i < 45 := by decide
      exact Or.inr (sl_below_bits c (hl i hi) 0 0)
    · exact Or.inr (sl_below_bits c (i := TMP) (by decide) 0 0)

theorem ladWkQ (hc : CfgOk c) : LadWk (Impl.Ecdh.Arm.Cfg.ladderQ c) size c.wk where
  le := wk_le c hc.n10 rfl
  sl := by
    have e : ladSlots (Impl.Ecdh.Arm.Cfg.ladderQ c) = [AP, B3P, PX, PY, ONEP, RX, RY, RZ, T0, T1, T2, T3,
      T4, T5, DX, DY, DZ, TX, TY, TZ].map c.sl := rfl
    rw [e]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have : ∀ i ∈ [AP, B3P, PX, PY, ONEP, RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TX, TY, TZ],
      i < 45 := by decide
    exact sl_below_wk c (this i hi)
  mo := sl_below_wk c (i := MP) (by decide)
  tmp := sl_below_wk c (i := TMP) (by decide)
  bits := wk_below_bits c rfl 0

theorem ladWxQ_eq (c : Cfg) : ladWx (Impl.Ecdh.Arm.Cfg.ladderQ c) c.wk = slW c [RX, RY, RZ, T0, T1, T2, T3,
    T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ, TMP] ++ [(c.wk, accLen c.MP')] := rfl

/-- What the ladder and the power leave: `Q 0` accepts what `R` holds. -/
structure LadPost (c : Cfg) (base : Addr) (Q : Nat → Fe c.C → Fe c.C → Fe c.C → Prop) (s s' : State) :
    Prop where
  scr : Scr s' base size
  rest : Rest powClob s s'
  unch : Unch base (slWk c [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5,
    TX, TY, TZ, TMP] ++ slWk c [ACC, PT, TMP]) s.mem s'.mem
  q : Q 0 (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY)) (tmv c.C c.n base s' (c.sl RZ))
  acc_lt : sv c base s' ACC < c.C.p
  acc : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' ACC) = tmv c.C c.n base s' (c.sl RZ) ^ (c.C.p - 2)
  rz_lt : sv c base s' RZ < c.C.p

/-- The ladder, from `R = O`, then `Z^(p-2)`, for any invariant `Q` that an
iteration keeps and that `Q (64 n)` accepts `O`. -/
theorem ladPow_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size) (hf : Far s base 8192)
    {g : Reg → BitVec 32}
    (F : Fixed c base g s.mem) {k : Nat} {Q : Nat → Fe c.C → Fe c.C → Fe c.C → Prop}
    (hstep : Step (Impl.Ecdh.Arm.Cfg.ladderQ c) c.C base s k Q) (hO : Q (64 * c.n) 0 1 0)
    (hpx : sv c base s PX < c.C.p) (hpy : sv c base s PY < c.C.p)
    (hrx : sv c base s RX = 0) (hry : sv c base s RY = c.mont 1) (hrz : sv c base s RZ = 0)
    (ht₀ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0)
    (ht₁ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 1 + t)) = if (c.C.p - 2).testBit t then 1 else 0)
    {rest : Prog isa} {R : State → Prop} (h : ∀ s', LadPost c base Q s s' → WP isa rest s' R) :
    WP isa (.seq (ladder (Impl.Ecdh.Arm.Cfg.ladderQ c) c.wk) (.seq (pow c.powP c.wk) rest)) s R := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega)
  have henc : encodable (BitVec.ofNat 32 (64 * c.n)) = true := by
    have : ∀ n < 10, encodable (BitVec.ofNat 32 (64 * n)) = true := by decide
    exact this _ h7
  have hlt : ∀ x ∈ ladR (Impl.Ecdh.Arm.Cfg.ladderQ c), wordsVal s.mem base x c.MP'.n < c.C.p := by
    intro x hx
    have hx' : x ∈ [AP, B3P, PX, PY, ONEP, RX, RY, RZ].map c.sl := hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    show sv c base s i < c.C.p
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt F.ap (hmont _)
    · exact lt_of_eq_of_lt F.b3p (hmont _)
    · exact hpx
    · exact hpy
    · exact lt_of_eq_of_lt F.onep (Nat.mod_lt _ (by omega))
    · exact lt_of_eq_of_lt hrx (by omega)
    · exact lt_of_eq_of_lt hry (hmont _)
    · exact lt_of_eq_of_lt hrz (by omega)
  have hR : Q (64 * c.n) (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY))
      (tmv c.C c.n base s (c.sl RZ)) := by
    show Q _ (toM _ _ (sv c base s RX)) (toM _ _ (sv c base s RY)) (toM _ _ (sv c base s RZ))
    rw [hrx, hry, hrz, toM_cmont hc, toM_zero]
    exact hO
  refine WP.seq (WP.mono (ladder_ok (L := Impl.Ecdh.Arm.Cfg.ladderQ c) (k := k) (ladLayQ hc)
    (ladWkQ hc) hpR (bitsAt_lt hc (j := 0) (by decide)) hs hf (modP_of hc F.mp) hlt hstep hR ht₀ henc)
    fun s₅ ⟨K₅, U₅, M₅, L₅, R₅⟩ => ?_)
  rw [ladWxQ_eq, accLen_MP'] at U₅
  have hs₅ := hs.of_rest K₅ (by decide)
  have hf₅ := hf.of_rest K₅
  have F₅ := F.unch h7 hn (fixedOk_slWk (by decide)) U₅
  have rz₅ : wordsVal s₅.mem base (c.sl RZ) c.n < c.C.p :=
    L₅ (c.sl RZ) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  refine WP.seq (WP.mono (pow_ok (P := c.powP) (e := c.C.p - 2) (powLayP hc) (powWkP hc) hpR
    (bitsAt_lt hc (j := 1) (by decide)) hs₅ hf₅ M₅ rz₅
    F₅.onep (fun t ht => by
      show s₅.mem (off base (bitsAt c.n 1 + t)) = _
      rw [tbl_unch U₅ h7 (j := 1) (by decide) ht (tbl_apart_slWk (by decide))]
      exact ht₁ t ht)
    (show c.C.p - 2 < 2 ^ (64 * c.n) by have := hc.p_lt; omega) henc) fun s₆ ⟨K₆, U₆, lt₆, v₆⟩ => h s₆ ?_)
  rw [powWxP_eq, accLen_MP'] at U₆
  have r₆ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] → sv c base s₆ i = sv c base s₅ i := fun hi h₁ =>
    sv_unch U₆ h7 hn hi (apart_slWk hi h₁)
  refine ⟨hs₅.of_rest K₆ (by decide), K₅.trans K₆, U₅.trans U₆, ?_, lt₆, ?_, ?_⟩
  · show Q 0 (toM _ _ (sv c base s₆ RX)) (toM _ _ (sv c base s₆ RY)) (toM _ _ (sv c base s₆ RZ))
    rw [r₆ (i := RX) (by decide) (by decide), r₆ (i := RY) (by decide) (by decide),
      r₆ (i := RZ) (by decide) (by decide)]
    exact R₅
  · show _ = toM _ _ (sv c base s₆ RZ) ^ _
    rw [r₆ (i := RZ) (by decide) (by decide)]
    exact v₆
  · rw [r₆ (i := RZ) (by decide) (by decide)]; exact rz₅

end VG.Proof.Ecdh.Arm
