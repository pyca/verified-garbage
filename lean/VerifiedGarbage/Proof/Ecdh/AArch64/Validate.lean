module
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Fixed
public import VerifiedGarbage.Proof.Weierstrass.Words

import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Ecdsa.AArch64.Scalar
import VerifiedGarbage.Proof.Ecdsa.AArch64.Middle
import VerifiedGarbage.Proof.Weierstrass.AArch64.Blocks
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
import VerifiedGarbage.Proof.Weierstrass.AArch64.CombSelect

/-!
# ECDH on AArch64: the peer's point, `[d]P` and `Z^(p-2)`

## The peer's point

`validate` takes the peer's `x` and `y` into Montgomery's form
(multiplications by `R² mod p`), computes `y² - (x³ + a x + b)` (`curveOps`,
a field program, by `fprog_ok`), ands the mask of its being zero into the
flag, and selects for the window method the peer's point if the flag is set, else
`G` (`validate_ok`).
-/

@[expose] public section

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
  have hout : ∀ op ∈ curveN, op.out ≠ TMP ∧ op.out ≠ 54 ∧ op.out ≠ 61 ∧ op.out ≠ 82 := by decide
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
  have hap : ∀ {i j}, i ≠ j → (i ≠ TMP ∨ (j ≠ 54 ∧ j ≠ 61 ∧ j ≠ 82)) → (j ≠ TMP ∨ (i ≠ 54 ∧ i ≠ 61 ∧ i ≠ 82)) →
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

theorem onCurve_wp (c : Cfg) {s : State} {Q : State → Prop} :
    WP isa (Impl.Ecdh.AArch64.Cfg.onCurve c) s Q ↔
      WP isa (.block ((Impl.Mont.AArch64.mul c.MP' (c.sl QXM) (c.sl E) (c.sl R2P) ++
        Impl.Mont.AArch64.mul c.MP' (c.sl QYM) (c.sl QY) (c.sl R2P)) ++
        ((fprog c.MP' (Impl.Ecdh.AArch64.Cfg.curveOps c) ++ Impl.Ecdh.AArch64.Cfg.checkZero c (c.sl W1)) ++
          Impl.Ecdh.AArch64.Cfg.select c))) s Q := by
  rw [Impl.Ecdh.AArch64.Cfg.onCurve, blocks_wp]
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil, fprog,
    List.flatMap_def, List.append_assoc]

/-- The peer's point is valid as the code checks it: `P₀` (its first byte
and the range of its coordinates) and the curve's equation. -/
abbrev PeerOk (c : Cfg) (base : Addr) (s : State) (P₀ : Prop) : Prop :=
  P₀ ∧ OnCurve c (Fin.ofNat c.C.p (sv c base s E)) (Fin.ofNat c.C.p (sv c base s QY))

theorem onCurve_ok (hc : BaseCfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    {g : Reg → BitVec 64} (F : Fixed c base g s.mem) (hr2 : sv c base s R2P = c.R * c.R % c.C.p)
    (hbp : sv c base s BP = c.mont c.C.b) {P₀ : Prop} [Decidable P₀]
    (hf : word s.mem base (c.sl FLAG) = mask P₀) :
    WP isa (Impl.Ecdh.AArch64.Cfg.onCurve c) s fun s' =>
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
  rw [onCurve_wp, WP.block_append_iff]
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

/-! ## The check of the point: `x < p`, `y < p`, then `onCurve` -/

theorem checkBody_ok (hc : BaseCfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    {g : Reg → BitVec 64} (F : Fixed c base g s.mem) (hr2 : sv c base s R2P = c.R * c.R % c.C.p)
    (hbp : sv c base s BP = c.mont c.C.b) {P₀ : Prop} [Decidable P₀]
    (hf : word s.mem base (c.sl FLAG) = mask P₀) :
    WP isa (Impl.Ecdh.AArch64.Cfg.checkBody c) s fun s' =>
      Scr s' base size ∧ (∀ r, r ∉ clob c.n → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Unch base (slW c [QXM, QYM, TMP, W0, W1, W2, W3, PY] ++ [(c.sl FLAG, 8)]) s.mem s'.mem ∧
      word s'.mem base (c.sl FLAG) = mask (PeerOk c base s ((P₀ ∧ sv c base s E < c.C.p) ∧ sv c base s QY < c.C.p)) ∧
      sv c base s' PX < c.C.p ∧ sv c base s' PY < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' PX) =
        (if PeerOk c base s ((P₀ ∧ sv c base s E < c.C.p) ∧ sv c base s QY < c.C.p) then
          Fin.ofNat c.C.p (sv c base s E) else Fin.ofNat c.C.p c.C.gx) ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' PY) =
        (if PeerOk c base s ((P₀ ∧ sv c base s E < c.C.p) ∧ sv c base s QY < c.C.p) then
          Fin.ofNat c.C.p (sv c base s QY) else Fin.ofNat c.C.p c.C.gy) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hF : c.sl FLAG + 8 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega_arith
  have hY := sl_le c h7 (i := QY) (by decide)
  have hE := sl_le c h7 (i := E) (by decide)
  have hM := sl_le c h7 (i := MP) (by decide)
  rw [Impl.Ecdh.AArch64.Cfg.checkBody]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (checkLtP_ok c hs h0 hE hM hF (sl_mod8 c E) (sl_mod8 c MP) (sl_mod8 c FLAG)) fun s₁ ⟨f₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  refine WP.mono (checkLtP_ok c hs₁ h0 hY hM hF (sl_mod8 c QY) (sl_mod8 c MP) (sl_mod8 c FLAG)) fun s₂ ⟨f₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have v₂ : ∀ {i}, i < 45 → i ≠ FLAG → sv c base s₂ i = sv c base s i := fun hi hf =>
    (sv_flag O₂ h0 h7 hn hi hf).trans (sv_flag O₁ h0 h7 hn hi hf)
  have U₂ : Unch base [(c.sl FLAG, 8)] s.mem s₂.mem := (O₁.unch.trans O₂.unch).mono fun w hw => by
    simp only [List.mem_append, List.mem_singleton] at hw ⊢; rcases hw with h | h <;> exact h
  have F₂ := F.unch h7 hn fixedOk_flag U₂
  have hmp : sv c base s MP = c.C.p := F.mp
  have hf₂ : word s₂.mem base (c.sl FLAG) = mask ((P₀ ∧ sv c base s E < c.C.p) ∧ sv c base s QY < c.C.p) := by
    rw [f₂, f₁, hf, mask_and, mask_and, sv_flag O₁ h0 h7 hn (i := QY) (by decide) (by decide),
      sv_flag O₁ h0 h7 hn (i := MP) (by decide) (by decide)]
    rw [show wordsVal s.mem base (c.sl MP) c.n = c.C.p from hmp]
  refine WP.mono (onCurve_ok hc hs₂ F₂ (by rw [v₂ (by decide) (by decide)]; exact hr2)
    (by rw [v₂ (by decide) (by decide)]; exact hbp) hf₂) fun s₃ ⟨hs₃, g₃, rd₃, wr₃, U₃, f₃, px_lt, py_lt, px, py⟩ => ?_
  unfold PeerOk at f₃ px py
  rw [show sv c base s₂ E = sv c base s E from v₂ (by decide) (by decide),
    show sv c base s₂ QY = sv c base s QY from v₂ (by decide) (by decide)] at f₃ px py
  refine ⟨hs₃, fun r hr => ?_, by rw [rd₃, k₂.rd, k₁.rd], by rw [wr₃, k₂.wr, k₁.wr],
    (U₂.trans U₃).mono fun w hw => ?_, f₃, px_lt, py_lt, px, py⟩
  · have hk : ∀ x ∈ [Reg.x1, .x2, .x7, .x16], x ∈ clob c.n := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> simp [clob]
    rw [g₃ r hr, k₂.gpr r (fun h => hr (hk r h)), k₁.gpr r (fun h => hr (hk r h))]
  · simp only [List.mem_append, List.mem_singleton] at hw ⊢
    rcases hw with h | h
    · exact Or.inr h
    · exact h

/-! ## The function: `checkBody` keeping `checkKept` in lanes, and its call -/

/-- Lane `i` of those the function keeps registers in. -/
def clane (v : VReg → BitVec 128) (i : Nat) : BitVec 64 :=
  (v (Impl.Ecdh.AArch64.Cfg.checkLane i).1).extractLsb' (64 * (Impl.Ecdh.AArch64.Cfg.checkLane i).2) 64

theorem checkLane_lt (i : Nat) : (Impl.Ecdh.AArch64.Cfg.checkLane i).2 < 2 := Nat.mod_lt _ (by decide)

theorem checkLane_inj : ∀ i < 6, ∀ j < 6, (Impl.Ecdh.AArch64.Cfg.checkLane i).1 = (Impl.Ecdh.AArch64.Cfg.checkLane j).1 →
    (Impl.Ecdh.AArch64.Cfg.checkLane i).2 = (Impl.Ecdh.AArch64.Cfg.checkLane j).2 → i = j := by decide

theorem checkLane_v : ∀ i < 6, (Impl.Ecdh.AArch64.Cfg.checkLane i).1 = .v24 ∨ (Impl.Ecdh.AArch64.Cfg.checkLane i).1 = .v25 ∨ (Impl.Ecdh.AArch64.Cfg.checkLane i).1 = .v26 := by
  decide

theorem clane_set (s : State) (x : BitVec 64) {i j : Nat} (hi : i < 6) (hj : j < 6) :
    clane (s.setV (Impl.Ecdh.AArch64.Cfg.checkLane i).1 (setLane (s.v (Impl.Ecdh.AArch64.Cfg.checkLane i).1) 64 (Impl.Ecdh.AArch64.Cfg.checkLane i).2 x)).v j =
      if i = j then x else clane s.v j := by
  unfold clane
  rw [RegUpd.v_setV]
  by_cases h1 : (Impl.Ecdh.AArch64.Cfg.checkLane j).1 = (Impl.Ecdh.AArch64.Cfg.checkLane i).1
  · simp only [h1, ite_true]
    rw [Weierstrass.AArch64.Mont.extract_setLane _ _ (checkLane_lt i) (checkLane_lt j)]
    by_cases h2 : (Impl.Ecdh.AArch64.Cfg.checkLane i).2 = (Impl.Ecdh.AArch64.Cfg.checkLane j).2
    · have := checkLane_inj i hi j hj h1.symm h2
      subst this; simp
    · have hij : i ≠ j := fun e => h2 (by rw [e])
      simp only [h2, ite_false, hij]
  · have hij : i ≠ j := fun e => h1 (by rw [e])
    simp only [h1, ite_false, hij]

/-- The registers `rs`, the `k`-th on, kept in their lanes. -/
def cins (rs : List Reg) (k : Nat) : List Instr :=
  (rs.zipIdx k).map fun (r, i) => .vop (.ins .d2 (Impl.Ecdh.AArch64.Cfg.checkLane i).1 (Impl.Ecdh.AArch64.Cfg.checkLane i).2 r)

/-- The registers `rs`, the `k`-th on, restored from their lanes. -/
def cumov (rs : List Reg) (k : Nat) : List Instr :=
  (rs.zipIdx k).map fun (r, i) => .umov .x r (Impl.Ecdh.AArch64.Cfg.checkLane i).1 (Impl.Ecdh.AArch64.Cfg.checkLane i).2

theorem csaves_ok : ∀ (rs : List Reg) (k : Nat) {s : State}, k + rs.length ≤ 6 →
    WP isa (.block (cins rs k)) s fun s' => Weierstrass.AArch64.Mont.VKeeps s s' ∧
      (∀ i (h : i < rs.length), clane s'.v (k + i) = s.gpr rs[i]) ∧ (∀ j < k, clane s'.v j = clane s.v j)
  | [], _, s, _ => WP.block_nil ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ h => absurd h (by simp), fun _ _ => rfl⟩
  | r :: rs, k, s, hk => by
    simp only [List.length_cons] at hk
    rw [cins, List.zipIdx_cons, List.map_cons, ← List.singleton_append, WP.block_append_iff]
    apply WP.of_runBlock
    simp only [runBlock_cons, Weierstrass.AArch64.Mont.exec_ins (checkLane_lt k), runStep_some, runBlock_nil,
      Option.some.injEq, exists_eq_left']
    refine WP.mono (csaves_ok rs (k + 1) (s := s.setV (Impl.Ecdh.AArch64.Cfg.checkLane k).1 (setLane (s.v (Impl.Ecdh.AArch64.Cfg.checkLane k).1) 64
      (Impl.Ecdh.AArch64.Cfg.checkLane k).2 (s.gpr r))) (by omega)) fun s' ⟨K, E, L⟩ => ⟨⟨K.gpr, K.mem, K.rd, K.wr, K.sp, K.c⟩, ?_, ?_⟩
    · intro i hi
      cases i with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [L k (by omega), clane_set s (s.gpr r) (by omega) (by omega)]
        simp
      | succ i =>
        simp only [List.getElem_cons_succ]
        rw [show k + (i + 1) = k + 1 + i by omega, E i (by simpa using hi)]; rfl
    · intro j hj
      rw [L j (by omega), clane_set s (s.gpr r) (by omega) (by omega)]
      simp only [show k ≠ j by omega, ite_false]

theorem crestores_ok : ∀ (rs : List Reg) (k : Nat) {s : State}, k + rs.length ≤ 6 → rs.Nodup →
    WP isa (.block (cumov rs k)) s fun s' => Keeps rs s s' ∧ s'.v = s.v ∧
      ∀ i (h : i < rs.length), s'.gpr rs[i] = clane s.v (k + i)
  | [], _, s, _, _ => WP.block_nil ⟨⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩, rfl, fun _ h => absurd h (by simp)⟩
  | r :: rs, k, s, hk, hnd => by
    simp only [List.length_cons] at hk
    have hr := (List.nodup_cons.mp hnd).1
    rw [cumov, List.zipIdx_cons, List.map_cons, ← List.singleton_append, WP.block_append_iff]
    apply WP.of_runBlock
    simp only [runBlock_cons, Weierstrass.AArch64.Mont.exec_umov (checkLane_lt k), runStep_some, runBlock_nil,
      Option.some.injEq, exists_eq_left']
    refine WP.mono (crestores_ok rs (k + 1) (by omega) (List.nodup_cons.mp hnd).2)
      fun s' ⟨K, V, E⟩ => ⟨⟨fun q hq => ?_, K.mem, K.rd, K.wr, K.sp⟩, V, ?_⟩
    · simp only [List.mem_cons, not_or] at hq
      rw [K.gpr q hq.2, RegUpd.gpr_write_of_ne _ _ _ hq.1]
    · intro i hi
      cases i with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [K.gpr r hr, RegUpd.gpr_write_self, BitVec.setWidth_eq]; rfl
      | succ i =>
        simp only [List.getElem_cons_succ]
        rw [E i (by simpa using hi), show k + (i + 1) = k + 1 + i by omega]; rfl

/-- A program that writes none of a vector register keeps it. -/
theorem WP.keepV {p : Prog isa} {s : State} {Q : State → Prop} {r : VReg}
    (hc : ∀ i ∈ instrs p, vdstOf i ≠ some r) (h : WP isa p s Q) : WP isa p s fun s' => Q s' ∧ s'.v r = s.v r := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.vec hc he⟩

/-- The registers the function changes: `clob`'s, but those it keeps. -/
def chkClob (c : Cfg) : List Reg := (clob c.n).filter fun r => r ∉ Impl.Ecdh.AArch64.Cfg.checkKept c

theorem checkKept_sub (c : Cfg) : ∀ r ∈ Impl.Ecdh.AArch64.Cfg.checkKept c, r ∈ preserved := by
  unfold Impl.Ecdh.AArch64.Cfg.checkKept; split <;> decide

theorem checkKept_nodup (c : Cfg) : (Impl.Ecdh.AArch64.Cfg.checkKept c).Nodup := by
  unfold Impl.Ecdh.AArch64.Cfg.checkKept; split <;> decide

theorem checkKept_len (c : Cfg) : (Impl.Ecdh.AArch64.Cfg.checkKept c).length ≤ 6 := by
  unfold Impl.Ecdh.AArch64.Cfg.checkKept; split <;> decide

/-- Every callee-saved register is either one the operations keep or one the function keeps. -/
theorem checkKept_pres (hc : BaseCfgOk c) : ∀ r ∈ preserved, r ∉ clob c.n ∨ r ∈ Impl.Ecdh.AArch64.Cfg.checkKept c := by
  have key : ∀ n < 10, ∀ r ∈ preserved, r ∉ clob n ∨
      r ∈ (if 7 ≤ n then [Reg.x21, .x22, .x23, .x24, .x25] else []) := by decide
  exact key c.n hc.n10

/-- The function: what `checkBody` does, its callee-saved registers restored. -/
theorem checkFn_ok (hc : BaseCfgOk c) (hck : Impl.Ecdh.AArch64.Cfg.checkCurve c ≠ none) {base : Addr} {s : State}
    (hs : Scr s base size) {R : Mem → Mem → Prop}
    (hb : ∀ t, Scr t base size → t.mem = s.mem → t.gpr = s.gpr → WP isa (Impl.Ecdh.AArch64.Cfg.checkBody c) t fun t' =>
      (∀ r, r ∉ clob c.n → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.sp = t.sp ∧ R t.mem t'.mem) :
    WP isa (Impl.Ecdh.AArch64.Cfg.checkFn c) s fun s' => KeepRegs (chkClob c) s s' ∧ R s.mem s'.mem := by
  obtain ⟨-, hv, -⟩ := hc.check_fn hck
  have hlen := checkKept_len c
  have hnv : ∀ j < 6, ∀ i ∈ instrs (Impl.Ecdh.AArch64.Cfg.checkBody c),
      vdstOf i ≠ some (Impl.Ecdh.AArch64.Cfg.checkLane j).1 := by
    intro j hj i hi e
    have := List.all_eq_true.mp ((Code.allInstrs_eq _ _) ▸ hv) i hi
    rcases checkLane_v j hj with h | h | h <;> rw [e, h] at this <;> simp at this
  rw [Impl.Ecdh.AArch64.Cfg.checkFn]
  refine WP.seq (WP.mono (csaves_ok (Impl.Ecdh.AArch64.Cfg.checkKept c) 0 (s := s) (by omega))
    fun s₁ ⟨K₁, L₁, _⟩ => ?_)
  have hs₁ : Scr s₁ base size := ⟨by rw [K₁.gpr]; exact hs.x0, by rw [K₁.wr]; exact hs.wr, hs.nowrap, hs.enc⟩
  have B := hb s₁ hs₁ K₁.mem K₁.gpr
  have B' : WP isa (Impl.Ecdh.AArch64.Cfg.checkBody c) s₁ fun t' => ((∀ r, r ∉ clob c.n → t'.gpr r = s₁.gpr r) ∧
      t'.rd = s₁.rd ∧ t'.wr = s₁.wr ∧ t'.sp = s₁.sp ∧ R s₁.mem t'.mem) ∧
      ∀ j < 6, clane t'.v j = clane s₁.v j := by
    obtain ⟨t, s', he, hq⟩ := B
    refine ⟨t, s', he, hq, fun j hj => ?_⟩
    unfold clane; rw [Exec.vec (hnv j hj) he]
  refine WP.seq (WP.mono B' fun s₂ ⟨⟨G₂, rd₂, wr₂, sp₂, R₂⟩, L₂⟩ => ?_)
  refine WP.mono (crestores_ok (Impl.Ecdh.AArch64.Cfg.checkKept c) 0 (s := s₂) (by omega) (checkKept_nodup c))
    fun s₃ ⟨K₃, _, E₃⟩ => ⟨⟨fun r hr => ?_, by rw [K₃.rd, rd₂, K₁.rd], by rw [K₃.wr, wr₂, K₁.wr],
      by rw [K₃.sp, sp₂, K₁.sp]⟩, by rw [K₃.mem, ← K₁.mem]; exact R₂⟩
  by_cases hk : r ∈ Impl.Ecdh.AArch64.Cfg.checkKept c
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hk
    have l := L₁ i hi
    rw [Nat.zero_add] at l
    rw [E₃ i hi, Nat.zero_add, L₂ i (by omega), l]
  · have hcl : r ∉ clob c.n := fun h => hr (List.mem_filter.mpr ⟨h, by simpa using hk⟩)
    rw [K₃.gpr r hk, G₂ r hcl, K₁.gpr]

/-- `x30` into lane 0 of `v28`. -/
theorem keepLr28_ok (s : State) :
    WP isa (.block [.vop (.ins .d2 .v28 0 .x30)]) s fun s₁ =>
      KeepRegs [] s s₁ ∧ s₁.mem = s.mem ∧ (s₁.v .v28).extractLsb' 0 64 = s.gpr .x30 := by
  apply WP.of_runBlock
  simp only [runBlock_cons, Weierstrass.AArch64.Mont.exec_ins (show 0 < 2 by decide), runStep_some, runBlock_nil,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun r _ => by simp [RegUpd.gpr_setV], rfl, rfl, rfl⟩, rfl, ?_⟩
  simp only [RegUpd.v_setV_self]
  have := Weierstrass.AArch64.Mont.extract_setLane (s.v .v28) (s.gpr .x30) (i := 0) (j := 0) (by decide) (by decide)
  simpa using this

/-- `x30` back from lane 0 of `v28`. -/
theorem lr28_ok (s : State) :
    WP isa (.block [.umov .x .x30 .v28 0]) s fun s' =>
      s'.gpr .x30 = (s.v .v28).extractLsb' 0 64 ∧ Keeps [.x30] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, Weierstrass.AArch64.Mont.exec_umov (show 0 < 2 by decide), runStep_some, runBlock_nil,
    Option.some.injEq, exists_eq_left', Nat.mul_zero]
  refine ⟨by simp [RegUpd.gpr_write], fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

/-- What the call of the function needs and gives, from its caller's memory. -/
def chkK (c : Cfg) (base : Addr) (mem : Mem) (R : Mem → Mem → Prop) : Contract isa where
  pre t := Scr t base size ∧ t.mem = mem
  post t t' := KeepRegs (chkClob c) t t' ∧ t'.v .v28 = t.v .v28 ∧ R t.mem t'.mem
  pub _ _ := True

/-- The call of the function `name`, whose code `checkFn` gives `R`: as `checkBody` inline,
keeping `x30` (in `v28`). -/
theorem chkCall_ok (hc : BaseCfgOk c) (hck : Impl.Ecdh.AArch64.Cfg.checkCurve c ≠ none) {name : String}
    {s : State} {base : Addr} (hs : Scr s base size) {R : Mem → Mem → Prop}
    (hfn : ∀ t, Scr t base size → t.mem = s.mem → WP isa (Impl.Ecdh.AArch64.Cfg.checkFn c) t fun t' =>
      KeepRegs (chkClob c) t t' ∧ R t.mem t'.mem) :
    WP isa (.seq (.block [.vop (.ins .d2 .v28 0 .x30)]) <|
      .seq (.call name (Impl.Ecdh.AArch64.Cfg.checkFn c)) (.block [.umov .x .x30 .v28 0])) s fun s' =>
      (∀ r, r ∉ clob c.n → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ R s.mem s'.mem := by
  obtain ⟨hv, -, hnf⟩ := hc.check_fn hck
  have hv28 : ∀ i ∈ instrs (Impl.Ecdh.AArch64.Cfg.checkFn c), vdstOf i ≠ some .v28 := by
    intro i hi e
    have := List.all_eq_true.mp ((Code.allInstrs_eq _ _) ▸ hv) i hi
    rw [e] at this; simp at this
  have hkv : (Impl.Ecdh.AArch64.Cfg.checkFn c).allInstrs keepsV = true := by
    rw [Code.allInstrs_eq]
    exact List.all_eq_true.mpr fun i hi => by
      have := List.all_eq_true.mp ((Code.allInstrs_eq _ _) ▸ hv) i hi
      simp only [Bool.and_eq_true] at this
      exact this.2
  have hpres := checkKept_pres hc
  refine WP.seq (WP.mono (keepLr28_ok s) fun s₁ ⟨k₁, m₁, l₁⟩ => ?_)
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have hcov : Covers [⟨base, size⟩] s₁.wr := Covers.one ⟨_, hs₁.wr, by
    have := hs.contains (d := 0) (n := size) (by omega) (by decide)
    simpa [off] using this⟩
  refine WP.seq (WP.callV (k := chkK c base s.mem R)
    (fun t ⟨ht, hm⟩ => by
      obtain ⟨tr, t', he, K, Rr⟩ := hfn t ht hm
      exact ⟨tr, t', he, ⟨fun r hr => K.gpr r fun h => (List.mem_filter.mp h).elim fun h₁ h₂ =>
          (hpres r hr).elim (· h₁) (by simpa using h₂), K.sp, Exec.preservedV he hkv⟩,
        K, Exec.vec hv28 he, Rr⟩)
    (rd := []) (wr := [⟨base, size⟩]) ⟨⟨by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), hs₁.x0], by simp,
        hs.nowrap, hs.enc⟩, by rw [State.withRegions_mem, State.callEntry_mem, m₁]⟩
      (Covers.right hcov) hcov ?_ hnf)
  intro s₂ r₂ w₂ p₂ _ _ _ _ ⟨K, V, Rr⟩
  simp only [State.withRegions_mem, State.callEntry_mem] at Rr
  rw [m₁] at Rr
  have V' : s₂.v .v28 = s₁.v .v28 := V
  refine WP.mono (lr28_ok s₂) fun s₃ ⟨l₃, k₃⟩ => ?_
  refine ⟨fun r hr => ?_, by rw [k₃.rd, r₂, k₁.rd], by rw [k₃.wr, w₂, k₁.wr], by rw [k₃.mem]; exact Rr⟩
  by_cases h30 : r = .x30
  · subst h30; rw [l₃, V', l₁]
  · have h16 : Reg.x16 ∈ clob c.n := by simp [clob]
    have h17 : Reg.x17 ∈ clob c.n := by simp [clob]
    refine (k₃.gpr _ (by simpa using h30)).trans ((K.gpr r fun h => hr (List.mem_filter.mp h).1).trans ?_)
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by
      simp only [linkRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun e => hr (e ▸ h16), fun e => hr (e ▸ h17), h30⟩), k₁.gpr _ (by simp)]

/-- What the check leaves in memory, from the caller's state `s`. -/
def ChkMem (c : Cfg) (base : Addr) (s : State) (P₀ : Prop) [Decidable P₀] (m' : Mem) : Prop :=
  Unch base (slW c [QXM, QYM, TMP, W0, W1, W2, W3, PY] ++ [(c.sl FLAG, 8)]) s.mem m' ∧
  word m' base (c.sl FLAG) = mask (PeerOk c base s ((P₀ ∧ sv c base s E < c.C.p) ∧ sv c base s QY < c.C.p)) ∧
  wordsVal m' base (c.sl PX) c.n < c.C.p ∧ wordsVal m' base (c.sl PY) c.n < c.C.p ∧
  toM c.C.p (2 ^ (64 * c.n)) (wordsVal m' base (c.sl PX) c.n) =
    (if PeerOk c base s ((P₀ ∧ sv c base s E < c.C.p) ∧ sv c base s QY < c.C.p) then
      Fin.ofNat c.C.p (sv c base s E) else Fin.ofNat c.C.p c.C.gx) ∧
  toM c.C.p (2 ^ (64 * c.n)) (wordsVal m' base (c.sl PY) c.n) =
    (if PeerOk c base s ((P₀ ∧ sv c base s E < c.C.p) ∧ sv c base s QY < c.C.p) then
      Fin.ofNat c.C.p (sv c base s QY) else Fin.ofNat c.C.p c.C.gy)

/-- `checkBody_ok` from a state with the caller's memory. -/
theorem checkBody_ok' (hc : BaseCfgOk c) {base : Addr} {s t : State} (ht : Scr t base size) (hm : t.mem = s.mem)
    {g : Reg → BitVec 64} (F : Fixed c base g s.mem) (hr2 : sv c base s R2P = c.R * c.R % c.C.p)
    (hbp : sv c base s BP = c.mont c.C.b) {P₀ : Prop} [Decidable P₀]
    (hf : word s.mem base (c.sl FLAG) = mask P₀) :
    WP isa (Impl.Ecdh.AArch64.Cfg.checkBody c) t fun t' =>
      (∀ r, r ∉ clob c.n → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.sp = t.sp ∧
      ChkMem c base s P₀ t'.mem := by
  have e : ∀ i, sv c base t i = sv c base s i := fun i => by
    show wordsVal t.mem _ _ _ = wordsVal s.mem _ _ _; rw [hm]
  have B := checkBody_ok hc ht (hm ▸ F) (by rw [e]; exact hr2) (by rw [e]; exact hbp) (P₀ := P₀) (by rw [hm]; exact hf)
  obtain ⟨tr, t', he, ⟨hs', g', rd', wr', U', f', px_lt, py_lt, px, py⟩⟩ := B
  refine ⟨tr, t', he, g', rd', wr', ?_, ?_⟩
  · exact Exec.sp he
  · unfold PeerOk at f' px py
    rw [e E, e QY] at f' px py
    rw [hm] at U'
    exact ⟨U', f', px_lt, py_lt, px, py⟩

/-- The checks of the peer's point: `x < p`, `y < p` and the curve's equation into the
flag, and the point the window method multiplies: by a call of `vg_<curve>_check_point`,
else inline, as `checkBody` does. -/
theorem validate_ok (hc : BaseCfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    {g : Reg → BitVec 64} (F : Fixed c base g s.mem) (hr2 : sv c base s R2P = c.R * c.R % c.C.p)
    (hbp : sv c base s BP = c.mont c.C.b) {P₀ : Prop} [Decidable P₀]
    (hf : word s.mem base (c.sl FLAG) = mask P₀) :
    WP isa (Impl.Ecdh.AArch64.Cfg.validate c) s fun s' =>
      Scr s' base size ∧ (∀ r, r ∉ clob c.n → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Unch base (slW c [QXM, QYM, TMP, W0, W1, W2, W3, PY] ++ [(c.sl FLAG, 8)]) s.mem s'.mem ∧
      word s'.mem base (c.sl FLAG) = mask (PeerOk c base s ((P₀ ∧ sv c base s E < c.C.p) ∧ sv c base s QY < c.C.p)) ∧
      sv c base s' PX < c.C.p ∧ sv c base s' PY < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' PX) =
        (if PeerOk c base s ((P₀ ∧ sv c base s E < c.C.p) ∧ sv c base s QY < c.C.p) then
          Fin.ofNat c.C.p (sv c base s E) else Fin.ofNat c.C.p c.C.gx) ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' PY) =
        (if PeerOk c base s ((P₀ ∧ sv c base s E < c.C.p) ∧ sv c base s QY < c.C.p) then
          Fin.ofNat c.C.p (sv c base s QY) else Fin.ofNat c.C.p c.C.gy) := by
  unfold Impl.Ecdh.AArch64.Cfg.validate
  split
  · rename_i C hC
    have hck : Impl.Ecdh.AArch64.Cfg.checkCurve c ≠ none := by rw [hC]; exact Option.some_ne_none _
    refine WP.mono (chkCall_ok hc hck hs (R := fun _ m' => ChkMem c base s P₀ m') fun t ht hm =>
      checkFn_ok hc hck ht (R := fun _ m' => ChkMem c base s P₀ m') fun u hu hum _ =>
        WP.mono (checkBody_ok' hc hu (hum.trans hm) F hr2 hbp hf) fun u' ⟨g', rd', wr', sp', M'⟩ =>
          ⟨g', rd', wr', sp', M'⟩) fun s' ⟨g', rd', wr', U', f', px_lt, py_lt, px, py⟩ => ?_
    exact ⟨⟨by rw [g' .x0 (x0_not_clob' _)]; exact hs.x0, by rw [wr']; exact hs.wr, hs.nowrap, hs.enc⟩,
      g', rd', wr', U', f', px_lt, py_lt, px, py⟩
  · exact checkBody_ok hc hs F hr2 hbp hf

end VG.Proof.Ecdh.AArch64
