import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages

/-!
# ECDH on AArch64: the peer's point, `[d]P` and `Z^(p-2)`

## The peer's point

`validate` takes the peer's `x` and `y` into Montgomery's form
(multiplications by `R² mod p`), computes `y² - (x³ + a x + b)` (`curveOps`,
a field program, by `fprog_ok`), ands the mask of its being zero into the
flag, and selects for the window method the peer's point if the flag is set, else
`G` (`validate_ok`).
-/

namespace VG.Proof.Ecdh.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps)
open VG.Impl.Ecdh.AArch64 (QY R2P BP QXM QYM W0 W1 W2 W3 PX PY)

variable {c : Cfg}

/-- `curveOps` on slot numbers. -/
def curveN : List FOp :=
  [.mul W0 QYM QYM, .mul W1 QXM QXM, .mul W2 W1 QXM, .mul W1 AP QXM, .add W3 W2 W1,
    .add W2 W3 BP, .sub W1 W0 W2]

theorem curveOps_eq (c : Cfg) : Impl.Ecdh.AArch64.Cfg.curveOps c = curveN.map (FOp.rename c.sl) := rfl

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
  gpr : ∀ r, r ∉ clob c.n → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  unch : Unch base (slW c [QXM, QYM, TMP]) s.mem s'.mem
  mod : ModOkA c.MP' size c.C.p s'.mem base
  x_lt : sv c base s' QXM < c.C.p
  x : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' QXM) = Fin.ofNat c.C.p (sv c base s E)
  y_lt : sv c base s' QYM < c.C.p
  y : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' QYM) = Fin.ofNat c.C.p (sv c base s QY)

theorem mont_ok (hc : BaseCfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    (hM : ModOkA c.MP' size c.C.p s.mem base) (hr2 : sv c base s R2P = c.R * c.R % c.C.p) :
    WP isa (.block (Impl.Mont.AArch64.mul c.MP' (c.sl QXM) (c.sl E) (c.sl R2P) ++
      Impl.Mont.AArch64.mul c.MP' (c.sl QYM) (c.sl QY) (c.sl R2P))) s (MontPost c base s) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hr2' : sv c base s R2P = 2 ^ (64 * c.n) * 2 ^ (64 * c.n) % c.C.p := hr2
  rw [WP.block_append_iff]
  refine WP.mono (slMul_ok (MP'_n c) h7 hs hM (MP'_A c) (o := QXM) (a := E) (b := R2P) (by decide)
    (by decide) (by decide) (by rw [hr2']; exact Nat.mod_lt _ (by omega))) fun s₁ ⟨k₁, lt₁, e₁⟩ => ?_
  have hs₁ := k₁.scr hs
  have kP₁ := hM.keepA64 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  have r2₁ : sv c base s₁ R2P = sv c base s R2P := sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)
  have y₁ : sv c base s₁ QY = sv c base s QY := sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)
  refine WP.mono (slMul_ok (MP'_n c) h7 hs₁ kP₁ (MP'_A c) (o := QYM) (a := QY) (b := R2P) (by decide)
    (by decide) (by decide) (by rw [r2₁, hr2']; exact Nat.mod_lt _ (by omega))) fun s₂ ⟨k₂, lt₂, e₂⟩ => ?_
  have x₂ : sv c base s₂ QXM = sv c base s₁ QXM := sv_keep (MP'_n c) rfl h7 hn k₂ (by decide) (by decide) (by decide)
  refine ⟨k₂.scr hs₁, fun r hr => by rw [k₂.gpr r hr, k₁.gpr r hr], by rw [k₂.rd, k₁.rd],
    by rw [k₂.wr, k₁.wr], ?_, kP₁.keepA64 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₂ (by decide) (by decide),
    by rw [x₂]; exact lt₁, ?_, lt₂, ?_⟩
  · exact ((unch_slots (MP'_n c) rfl k₁.unch (l := [QXM, QYM, TMP]) (by simp) (by simp)).trans
      (unch_slots (MP'_n c) rfl k₂.unch (l := [QXM, QYM, TMP]) (by simp) (by simp))).mono
      fun w hw => by simp only [List.mem_append, or_self] at hw; exact hw
  · rw [x₂]; exact toM_r2 hpR (by rw [e₁, hr2'])
  · exact toM_r2 hpR (by rw [e₂, r2₁, y₁, hr2'])

/-! ## The curve's equation -/

/-- `y² = x³ + a x + b`, in `Fin p`. -/
abbrev OnCurve (c : Cfg) (x y : Fe c.C) : Prop :=
  y * y - ((x * x * x + Fin.ofNat c.C.p c.C.a * x) + Fin.ofNat c.C.p c.C.b) = 0

theorem curve_ok (hc : BaseCfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    (hM : ModOkA c.MP' size c.C.p s.mem base) (hx : sv c base s QXM < c.C.p) (hy : sv c base s QYM < c.C.p)
    (hap : sv c base s AP = c.mont c.C.a) (hbp : sv c base s BP = c.mont c.C.b) {P₀ : Prop} [Decidable P₀]
    (hf : word s.mem base (c.sl FLAG) = mask P₀) :
    WP isa (.block (fprog c.MP' (Impl.Ecdh.AArch64.Cfg.curveOps c) ++
      Impl.Ecdh.AArch64.Cfg.checkZero c (c.sl W1))) s fun s' =>
      Scr s' base size ∧ (∀ r, r ∉ clob c.n → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Unch base (slW c [W0, W1, W2, W3, TMP] ++ [(c.sl FLAG, 8)]) s.mem s'.mem ∧
      word s'.mem base (c.sl FLAG) = mask (P₀ ∧ OnCurve c (toM c.C.p (2 ^ (64 * c.n)) (sv c base s QXM))
        (toM c.C.p (2 ^ (64 * c.n)) (sv c base s QYM))) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hF : c.sl FLAG + 8 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega
  have hL : Lay c.MP' size (· ∈ curveSl.map c.sl) := lay_map hc rfl rfl rfl (by decide)
  have hAl : Aligned c.MP' (· ∈ curveSl.map c.sl) := ⟨fun x hx => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx; exact sl_mod8 c i, MP'_A c,
    fun f m' h => (hc.call_p f m' h).2⟩
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
  rw [WP.block_append_iff]
  refine WP.mono (fprog_ok hL hAl hpR (Impl.Ecdh.AArch64.Cfg.curveOps c) I (fun op hop x hx => ?_)
    (by rw [curveOps_eq]; exact readsOk_rename c.sl curveN_reads)) fun s₃ ⟨PK, I₃⟩ => ?_
  · rw [curveOps_eq] at hop
    obtain ⟨op₀, h₀, rfl⟩ := List.mem_map.mp hop
    have hx' : x ∈ (op₀.out :: op₀.ins).map c.sl := by
      cases op₀ <;> simpa [FOp.rename, FOp.out, FOp.ins] using hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    exact List.mem_map_of_mem (curveN_slots op₀ h₀ i hi)
  have hW1 : c.sl W1 ∈ validAfter (Impl.Ecdh.AArch64.Cfg.curveOps c) ([QXM, QYM, AP, BP].map c.sl) :=
    (mem_validAfter _ _).mpr (Or.inr (by simp [Impl.Ecdh.AArch64.Cfg.curveOps, FOp.out]))
  have v₃ : toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₃.mem base (c.sl W1) c.n) = _ := I₃.val _ hW1
  have lt₃ : wordsVal s₃.mem base (c.sl W1) c.n < c.C.p := I₃.lt _ hW1
  have hout : ∀ op ∈ curveN, op.out ≠ TMP ∧ op.out ≠ 54 ∧ op.out ≠ 82 := by decide
  rw [curveOps_eq, congrFun (runOps_rename c.sl curveN _ fun op hop y h =>
      sl_inj c h0 h (.inr (hout op hop).2) (.inl (hout op hop).1)) W1,
    curveN_run] at v₃
  have U₃ : Unch base (slW c [W0, W1, W2, W3, TMP]) s.mem s₃.mem := PK.unch.mono fun w hw => by
    rw [curveOps_eq, List.map_map] at hw
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hw
    rcases hw with ⟨op, ⟨op₀, h₀, rfl⟩, rfl⟩ | rfl
    · exact List.mem_map.mpr ⟨op₀.out, curveN_out op₀ h₀, by rw [Function.comp_apply, FOp.out_rename]; rfl⟩
    · exact List.mem_map_of_mem (by decide)
  have hs₃ := PK.scr hs
  refine WP.mono (checkZero_ok c hs₃ h0 (sl_le c h7 (i := W1) (by decide)) hF (sl_mod8 c _)
    (sl_mod8 c FLAG)) fun s₄ ⟨f₄, k₄, O₄⟩ => ?_
  refine ⟨hs₃.of_keepRegs k₄ (by decide), fun r hr => ?_, by rw [k₄.rd, PK.rd], by rw [k₄.wr, PK.wr],
    U₃.trans O₄.unch, ?_⟩
  · rw [k₄.gpr r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl <;> simp [clob])), PK.gpr r hr]
  · have hz : wordsVal s₃.mem base (c.sl W1) c.n = 0 ↔
        OnCurve c (toM c.C.p (2 ^ (64 * c.n)) (sv c base s QXM)) (toM c.C.p (2 ^ (64 * c.n)) (sv c base s QYM)) := by
      rw [← toM_eq_zero_iff hpR lt₃, v₃]
      show _ * _ - ((_ * _ * _ + toM _ _ (sv c base s AP) * _) + toM _ _ (sv c base s BP)) = 0 ↔ _
      rw [hap, hbp, toM_cmont hc, toM_cmont hc]
    rw [f₄, flag_unch U₃ h7 h0 hn (by decide), hf, mask_and]
    simp only [mask, hz]

/-! ## The point for the window method -/

theorem mask_bool (P : Prop) [Decidable P] : mask P = if decide P then BitVec.allOnes 64 else 0 := by
  simp only [mask, decide_eq_true_eq]

theorem select_eq (c : Cfg) : Impl.Ecdh.AArch64.Cfg.select c =
    ([ld .x3 (c.sl FLAG)] : List Instr) ++
    (sel c.n (c.sl PX) (c.sl GX) (c.sl QXM) ++ sel c.n (c.sl PY) (c.sl GY) (c.sl QYM)) := by
  simp only [Impl.Ecdh.AArch64.Cfg.select, List.append_assoc]

theorem select_ok (hc : BaseCfgOk c) {base : Addr} {s : State} (hs : Scr s base size) {P : Prop} [Decidable P]
    (hf : word s.mem base (c.sl FLAG) = mask P) :
    WP isa (.block (Impl.Ecdh.AArch64.Cfg.select c)) s fun s' =>
      Scr s' base size ∧ KeepRegs [.x1, .x2, .x3] s s' ∧ Unch base (slW c [PX, PY]) s.mem s'.mem ∧
      sv c base s' PX = (if P then sv c base s QXM else sv c base s GX) ∧
      sv c base s' PY = (if P then sv c base s QYM else sv c base s GY) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hap : ∀ {i j}, i ≠ j → (i ≠ TMP ∨ (j ≠ 54 ∧ j ≠ 82)) → (j ≠ TMP ∨ (i ≠ 54 ∧ i ≠ 82)) →
      c.sl i ≤ c.sl j ∨ c.sl j + 8 * c.n ≤ c.sl i := fun h h₁ h₂ => by
    have := sl_apart c h h₁ h₂; omega
  rw [select_eq, WP.block_append_iff]
  refine WP.mono (ld_ok hs (d := c.sl FLAG) (by have := sl_le c h7 (i := FLAG) (by decide); omega)
    (sl_mod8 c FLAG) .x3) fun s₁ ⟨e₁, k₁, _⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hc₁ : s₁.gpr .x3 = if decide P then BitVec.allOnes 64 else 0 := by rw [e₁, hf, mask_bool]
  rw [WP.block_append_iff]
  refine WP.mono (sel_ok (decide P) c.n hs₁ hc₁ (sl_le c h7 (i := PX) (by decide))
    (sl_le c h7 (i := GX) (by decide)) (sl_le c h7 (i := QXM) (by decide)) (sl_mod8 c _) (sl_mod8 c _)
    (sl_mod8 c _) (hap (by decide) (by decide) (by decide))
    (hap (by decide) (by decide) (by decide))) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have hc₂ : s₂.gpr .x3 = if decide P then BitVec.allOnes 64 else 0 := by rw [k₂.gpr _ (by decide), hc₁]
  refine WP.mono (sel_ok (decide P) c.n hs₂ hc₂ (sl_le c h7 (i := PY) (by decide))
    (sl_le c h7 (i := GY) (by decide)) (sl_le c h7 (i := QYM) (by decide)) (sl_mod8 c _) (sl_mod8 c _)
    (sl_mod8 c _) (hap (by decide) (by decide) (by decide))
    (hap (by decide) (by decide) (by decide))) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hm₁ : s₁.mem = s.mem := k₁.mem
  refine ⟨hs₂.of_keepRegs k₃ (by decide), ((Keeps.regs k₁).mono (by sub_regs)).trans
    ((k₂.mono (by sub_regs)).trans (k₃.mono (by sub_regs))), ?_, ?_, ?_⟩
  · have := O₂.unch.trans O₃.unch
    rw [hm₁] at this
    exact this.mono fun w hw => by simpa using hw
  · show wordsVal s₃.mem _ _ _ = _
    rw [sv_out O₃ h7 hn (by decide) (by decide), e₂, hm₁]
    by_cases hP : P <;> simp [hP]
  · show wordsVal s₃.mem _ _ _ = _
    rw [e₃, sv_out O₂ h7 hn (by decide) (by decide), sv_out O₂ h7 hn (by decide) (by decide), hm₁]
    by_cases hP : P <;> simp [hP]

/-! ## The whole validation -/

theorem validate_wp (c : Cfg) {s : State} {Q : State → Prop} :
    WP isa (Impl.Ecdh.AArch64.Cfg.validate c) s Q ↔
      WP isa (.block ((Impl.Mont.AArch64.mul c.MP' (c.sl QXM) (c.sl E) (c.sl R2P) ++
        Impl.Mont.AArch64.mul c.MP' (c.sl QYM) (c.sl QY) (c.sl R2P)) ++
        ((fprog c.MP' (Impl.Ecdh.AArch64.Cfg.curveOps c) ++ Impl.Ecdh.AArch64.Cfg.checkZero c (c.sl W1)) ++
          Impl.Ecdh.AArch64.Cfg.select c))) s Q := by
  rw [Impl.Ecdh.AArch64.Cfg.validate, blocks_wp]
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil, fprog,
    List.flatMap_def, List.append_assoc]

/-- The peer's point is valid as the code checks it: `P₀` (its first byte
and the range of its coordinates) and the curve's equation. -/
abbrev PeerOk (c : Cfg) (base : Addr) (s : State) (P₀ : Prop) : Prop :=
  P₀ ∧ OnCurve c (Fin.ofNat c.C.p (sv c base s E)) (Fin.ofNat c.C.p (sv c base s QY))

theorem validate_ok (hc : BaseCfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    {g : Reg → BitVec 64} (F : Fixed c base g s.mem) (hr2 : sv c base s R2P = c.R * c.R % c.C.p)
    (hbp : sv c base s BP = c.mont c.C.b) {P₀ : Prop} [Decidable P₀]
    (hf : word s.mem base (c.sl FLAG) = mask P₀) :
    WP isa (Impl.Ecdh.AArch64.Cfg.validate c) s fun s' =>
      Scr s' base size ∧ (∀ r, r ∉ clob c.n → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Unch base (slW c [QXM, QYM, TMP, W0, W1, W2, W3, PY] ++ [(c.sl FLAG, 8)]) s.mem s'.mem ∧
      word s'.mem base (c.sl FLAG) = mask (PeerOk c base s P₀) ∧
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
  rw [validate_wp, WP.block_append_iff]
  refine WP.mono (mont_ok hc hs (modP_of hc F.mp) hr2) fun s₂ Mp => ?_
  have F₂ := F.unch h7 hn (fixedOk_slW (l := [QXM, QYM, TMP]) (by decide)) Mp.unch
  have e₂ : ∀ {i}, i < 45 → i ∉ [QXM, QYM, TMP] → sv c base s₂ i = sv c base s i := fun hi hl =>
    sv_unch Mp.unch h7 hn hi (apart_slW hl)
  rw [WP.block_append_iff]
  refine WP.mono (curve_ok hc Mp.scr Mp.mod Mp.x_lt Mp.y_lt F₂.ap (P₀ := P₀)
    (by rw [e₂ (i := BP) (by decide) (by decide)]; exact hbp)
    (by rw [flag_unch Mp.unch h7 h0 hn (by decide)]; exact hf)) fun s₄ ⟨hs₄, g₄, rd₄, wr₄, U₄, f₄⟩ => ?_
  rw [Mp.x, Mp.y] at f₄
  have F₄ := F₂.unch h7 hn ((fixedOk_slW (l := [W0, W1, W2, W3, TMP]) (by decide)).append fixedOk_flag) U₄
  refine WP.mono (select_ok hc hs₄ f₄) fun s₆ ⟨hs₆, k₆, U₆, px, py⟩ => ?_
  have q₄ : ∀ {i}, i < 45 → i ∉ [W0, W1, W2, W3, TMP] → i ≠ FLAG → sv c base s₄ i = sv c base s₂ i :=
    fun hi hl hf => sv_unch U₄ h7 hn hi (apart_append (apart_slW hl) (apart_flag h0 hf))
  have F₆ := F₄.unch h7 hn (fixedOk_slW (l := [PX, PY]) (by decide)) U₆
  have qx : sv c base s₄ QXM = sv c base s₂ QXM := q₄ (by decide) (by decide) (by decide)
  have qy : sv c base s₄ QYM = sv c base s₂ QYM := q₄ (by decide) (by decide) (by decide)
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  refine ⟨hs₆, fun r hr => ?_, by rw [k₆.rd, rd₄, Mp.rd], by rw [k₆.wr, wr₄, Mp.wr], ?_,
    by rw [flag_unch U₆ h7 h0 hn (by decide)]; exact f₄, ?_, ?_, ?_, ?_⟩
  · rw [k₆.gpr r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;> simp [clob])), g₄ r hr,
      Mp.gpr r hr]
  · have sub : ∀ i ∈ [QXM, QYM, TMP, W0, W1, W2, W3, TMP, PX, PY], i ∈ [QXM, QYM, TMP, W0, W1, W2, W3, PY] := by
      decide
    have hsl : ∀ {l : List Nat}, (∀ i ∈ l, i ∈ [QXM, QYM, TMP, W0, W1, W2, W3, TMP, PX, PY]) →
        ∀ w ∈ slW c l, w ∈ slW c [QXM, QYM, TMP, W0, W1, W2, W3, PY] ++ [(c.sl FLAG, 8)] := fun hl w hw => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact List.mem_append_left _ (List.mem_map_of_mem (sub i (hl i hi)))
    refine ((Mp.unch.trans U₄).trans U₆).mono fun w hw => ?_
    rcases List.mem_append.mp hw with hw | hw
    · rcases List.mem_append.mp hw with hw | hw
      · exact hsl (by decide) w hw
      · rcases List.mem_append.mp hw with hw | hw
        · exact hsl (by decide) w hw
        · exact List.mem_append_right _ hw
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

end VG.Proof.Ecdh.AArch64
