module

public import VerifiedGarbage.Proof.Ecdh.AArch64.Validate
import VerifiedGarbage.Proof.Mont.Read
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Ecdsa.AArch64.Scalar
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Weierstrass.AArch64.CombSelect

/-!
# `vg_<curve>_check_point` on AArch64: what it computes

The facts of `Impl.Weierstrass.CheckPoint`'s contract for AArch64, by name
(`ptK`), for any curve of the code whose prime and size are a curve's of the
specification (`checkCurve`): `checkBodyR_ok` runs `checkBody` from `p`,
`R² mod p`, `a R mod p` and `b R mod p` alone (where `checkBody_ok` takes
every fixed slot of the signature's layout), `checkFn_ok` restores the
callee-saved registers, and `post_of_raw` states the result as the
contract does: `x R mod p` from `toM`, the flag's mask from `PeerOk`, and
every byte kept but those of the own working space and of the results.
-/

@[expose] public section

namespace VG.Proof.Ecdh.AArch64.CheckPoint

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (QY R2P BP QXM QYM W0 W1 W2 W3 PX PY)

variable {c : Cfg}

/-- The check of a public point on AArch64, by name: `ws` in `x0`. -/
def ptK (C : Impl.Weierstrass.CheckPoint.Curve) : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .x0, 8192⟩] ∧ (s.gpr .x0).toNat + 8192 ≤ 2 ^ 64 ∧
    C.pre (s.gpr .x0) s.mem
  post s s' := C.post (s.gpr .x0) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.sp = s₂.sp

/-- `checkBody` from `p`, `R² mod p`, `a R mod p` and `b R mod p`: the flag `&=` the
mask of the point's validity, `x R mod p` and `y R mod p` (as `toM`), and the point
selected by the flag, as the slots hold them. -/
theorem checkBodyR_ok (hc : BaseCfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    (hmp : sv c base s MP = c.C.p) (hap : sv c base s AP = c.mont c.C.a)
    (hr2 : sv c base s R2P = c.R * c.R % c.C.p) (hbp : sv c base s BP = c.mont c.C.b)
    {P₀ : Prop} [Decidable P₀] (hf : word s.mem base (c.sl FLAG) = mask P₀) :
    WP isa (Impl.Ecdh.AArch64.Cfg.checkBody c) s fun s' =>
      (∀ r, r ∉ clob c.n → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Unch base (slW c [QXM, QYM, TMP, W0, W1, W2, W3, PY] ++ [(c.sl FLAG, 8)]) s.mem s'.mem ∧
      word s'.mem base (c.sl FLAG) =
        mask (PeerOk c base s ((P₀ ∧ sv c base s E < c.C.p) ∧ sv c base s QY < c.C.p)) ∧
      sv c base s' QXM < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' QXM) = Fin.ofNat c.C.p (sv c base s E) ∧
      sv c base s' QYM < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' QYM) = Fin.ofNat c.C.p (sv c base s QY) ∧
      sv c base s' PX = (if PeerOk c base s ((P₀ ∧ sv c base s E < c.C.p) ∧ sv c base s QY < c.C.p)
        then sv c base s' QXM else sv c base s GX) ∧
      sv c base s' PY = (if PeerOk c base s ((P₀ ∧ sv c base s E < c.C.p) ∧ sv c base s QY < c.C.p)
        then sv c base s' QYM else sv c base s GY) := by
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
  have hf₂ : word s₂.mem base (c.sl FLAG) = mask ((P₀ ∧ sv c base s E < c.C.p) ∧ sv c base s QY < c.C.p) := by
    rw [f₂, f₁, hf, mask_and, mask_and, sv_flag O₁ h0 h7 hn (i := QY) (by decide) (by decide),
      sv_flag O₁ h0 h7 hn (i := MP) (by decide) (by decide)]
    rw [show wordsVal s.mem base (c.sl MP) c.n = c.C.p from hmp]
  rw [onCurve_wp, WP.block_append_iff]
  refine WP.mono (mont_ok hc hs₂ (modP_of hc ((v₂ (i := MP) (by decide) (by decide)).trans hmp))
    (by rw [v₂ (by decide) (by decide)]; exact hr2)) fun s₃ Mp => ?_
  have e₃ : ∀ {i}, i < 45 → i ∉ [QXM, QYM, TMP] → sv c base s₃ i = sv c base s₂ i := fun hi hl =>
    sv_unch Mp.unch h7 hn hi (apart_slW hl)
  rw [WP.block_append_iff]
  refine WP.mono (curve_ok hc Mp.scr Mp.mod Mp.x_lt Mp.y_lt
    (by rw [e₃ (i := AP) (by decide) (by decide), v₂ (by decide) (by decide)]; exact hap)
    (by rw [e₃ (i := BP) (by decide) (by decide), v₂ (by decide) (by decide)]; exact hbp)
    (P₀ := (P₀ ∧ sv c base s E < c.C.p) ∧ sv c base s QY < c.C.p)
    (by rw [flag_unch Mp.unch h7 h0 hn (by decide)]; exact hf₂)) fun s₄ ⟨hs₄, g₄, rd₄, wr₄, U₄, f₄⟩ => ?_
  rw [Mp.x, Mp.y, v₂ (i := E) (by decide) (by decide), v₂ (i := QY) (by decide) (by decide)] at f₄
  refine WP.mono (select_ok hc hs₄ f₄) fun s₅ ⟨_, k₅, U₅, px, py⟩ => ?_
  have q₄ : ∀ {i}, i < 45 → i ∉ [W0, W1, W2, W3, TMP] → i ≠ FLAG → sv c base s₄ i = sv c base s₃ i :=
    fun hi hl hf => sv_unch U₄ h7 hn hi (apart_append (apart_slW hl) (apart_flag h0 hf))
  have q₅ : ∀ {i}, i < 45 → i ∉ [PX, PY] → sv c base s₅ i = sv c base s₄ i := fun hi hl =>
    sv_unch U₅ h7 hn hi (apart_slW hl)
  have qx : sv c base s₅ QXM = sv c base s₃ QXM := (q₅ (by decide) (by decide)).trans (q₄ (by decide) (by decide) (by decide))
  have qy : sv c base s₅ QYM = sv c base s₃ QYM := (q₅ (by decide) (by decide)).trans (q₄ (by decide) (by decide) (by decide))
  have gx : sv c base s₄ GX = sv c base s GX :=
    ((q₄ (by decide) (by decide) (by decide)).trans (e₃ (by decide) (by decide))).trans (v₂ (by decide) (by decide))
  have gy : sv c base s₄ GY = sv c base s GY :=
    ((q₄ (by decide) (by decide) (by decide)).trans (e₃ (by decide) (by decide))).trans (v₂ (by decide) (by decide))
  have x₄ : sv c base s₄ QXM = sv c base s₃ QXM := q₄ (by decide) (by decide) (by decide)
  have y₄ : sv c base s₄ QYM = sv c base s₃ QYM := q₄ (by decide) (by decide) (by decide)
  refine ⟨fun r hr => ?_, by rw [k₅.rd, rd₄, Mp.rd, k₂.rd, k₁.rd], by rw [k₅.wr, wr₄, Mp.wr, k₂.wr, k₁.wr],
    ?_, by rw [flag_unch U₅ h7 h0 hn (by decide)]; exact f₄, by rw [qx]; exact Mp.x_lt,
    by rw [qx, Mp.x, v₂ (by decide) (by decide)], by rw [qy]; exact Mp.y_lt,
    by rw [qy, Mp.y, v₂ (by decide) (by decide)], by rw [px, x₄, gx, qx], by rw [py, y₄, gy, qy]⟩
  · have hk : ∀ x ∈ [Reg.x1, .x2, .x7, .x16], x ∈ clob c.n := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> simp [clob]
    have hk₅ : ∀ x ∈ [Reg.x1, .x2, .x3], x ∈ clob c.n := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [clob]
    rw [k₅.gpr r (fun h => hr (hk₅ r h)), g₄ r hr, Mp.gpr r hr, k₂.gpr r (fun h => hr (hk r h)),
      k₁.gpr r (fun h => hr (hk r h))]
  · have hsl : ∀ {l : List Nat}, (∀ i ∈ l, i ∈ [QXM, QYM, TMP, W0, W1, W2, W3, PY]) →
        ∀ w ∈ slW c l, w ∈ slW c [QXM, QYM, TMP, W0, W1, W2, W3, PY] ++ [(c.sl FLAG, 8)] := fun hl w hw => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact List.mem_append_left _ (List.mem_map_of_mem (hl i hi))
    refine (((U₂.trans Mp.unch).trans U₄).trans U₅).mono fun w hw => ?_
    simp only [List.mem_append] at hw
    rcases hw with ((hw | hw) | hw | hw) | hw
    · exact List.mem_append_right _ hw
    · exact hsl (by decide) w hw
    · exact hsl (by decide) w hw
    · exact List.mem_append_right _ hw
    · exact hsl (by decide) w hw

/-- `toM` tells apart numbers below `m`. -/
theorem toM_inj {m R x y : Nat} [NeZero m] (hR : UnitMod m R) (hx : x < m) (hy : y < m)
    (h : toM m R x = toM m R y) : x = y := by
  have hu := mul_rinv hR
  unfold toM at h
  have h' : Fin.ofNat m x = Fin.ofNat m y := by grind
  have := congrArg Fin.val h'
  rwa [Fin.val_ofNat, Fin.val_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this

/-- The number at slot `i` of the specification's layout is the one at the code's. -/
theorem num_sl {C : Impl.Weierstrass.CheckPoint.Curve} (hk : C.k = c.n) (h7 : c.n < 10) {i : Nat}
    (hi : i < 45) (hT : i ≠ TMP) (m : Mem) (base : Addr) :
    C.num base m (C.slot i) = wordsVal m base (c.sl i) c.n := by
  have hb : 8 * c.n * i ≤ 8 * 9 * 44 := Nat.mul_le_mul (Nat.mul_le_mul_left 8 (by omega_arith)) (by omega_arith)
  unfold Impl.Weierstrass.CheckPoint.Curve.num Impl.Weierstrass.Mont.numAt Impl.Weierstrass.CheckPoint.Curve.slot
  rw [hk, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith), sl_eq c i hT]
  exact read_eq_wordsVal m base c.n _

/-- The flag's word is the one at the code's slot. -/
theorem flag_sl {C : Impl.Weierstrass.CheckPoint.Curve} (hk : C.k = c.n) (m : Mem) (base : Addr) :
    C.flag base m = word m base (c.sl FLAG) := by
  unfold Impl.Weierstrass.CheckPoint.Curve.flag Impl.Weierstrass.CheckPoint.Curve.flagAt
    Impl.Weierstrass.CheckPoint.Curve.slot
  rw [hk, sl_eq c FLAG (by decide)]
  simp only [Mem.readW, BitVec.setWidth_eq]
  rfl

/-- The curve's equation, as the specification and the proofs state it. -/
theorem onCurve_iff (x y : Fe c.C) : Spec.Weierstrass.onCurve c.C (.affine x y) = true ↔ OnCurve c x y := by
  simp only [Spec.Weierstrass.onCurve, decide_eq_true_eq]
  constructor <;> intro h <;> grind

/-- The bytes `checkBody` may change are the own working space's and the results'. -/
theorem keeps_of_unch {C : Impl.Weierstrass.CheckPoint.Curve} (hk : C.k = c.n) (h7 : c.n < 10) {ws : Addr}
    {m m' : Mem} (hu : Unch ws (slW c [QXM, QYM, TMP, W0, W1, W2, W3, PY] ++ [(c.sl FLAG, 8)]) m m') :
    C.Keeps ws m m' := by
  intro i hi hown hp
  have h8 : Impl.Weierstrass.Mont.wsBytes = 8192 := rfl
  refine hu _ fun w hw => ?_
  show (ws + BitVec.ofNat 64 i - ws).toNat < _ ∨ _ ≤ (ws + BitVec.ofNat 64 i - ws).toNat
  rw [Mem.sub_ofNat_toNat ws (by omega_arith)]
  simp only [Impl.Weierstrass.CheckPoint.Curve.Own, Impl.Weierstrass.CheckPoint.Curve.Out,
    Impl.Weierstrass.CheckPoint.Curve.slot, Impl.Weierstrass.CheckPoint.Curve.flagAt,
    Impl.Weierstrass.Mont.ownAt, Impl.Weierstrass.Mont.ownBytes, hk, List.mem_cons, List.not_mem_nil,
    or_false, exists_eq_or_imp, exists_eq_left, not_or, not_and_or, Nat.not_lt, Nat.not_le] at hown hp
  simp only [slW, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hw
  have hT : c.sl TMP = 64 + 8 * c.n * 2 ∨ c.sl TMP = 4096 - 16 * c.n ∧ (c.n = 6 ∨ c.n = 8 ∨ c.n = 9) := by
    by_cases hr : c.n = 6 ∨ c.n = 8 ∨ c.n = 9
    · exact .inr ⟨sl_tmp c hr, hr⟩
    · exact .inl (sl_aff c hr TMP)
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;>
    (try simp only [QXM, QYM, W0, W1, W2, W3, PY, XM, X, KM, TT, SM, RM, SS, FLAG,
      sl_eq c 34 (by decide), sl_eq c 35 (by decide), sl_eq c 37 (by decide), sl_eq c 41 (by decide),
      sl_eq c 42 (by decide), sl_eq c 38 (by decide), sl_eq c 43 (by decide), sl_eq c 44 (by decide)] at hT ⊢) <;>
    first | (simp only [hown, hp]; done) | omega_arith

/-- The contract's postcondition, from `checkBodyR_ok`'s facts. -/
theorem post_of_raw (hc : BaseCfgOk c) {C : Impl.Weierstrass.CheckPoint.Curve} (hW : C.W = c.C)
    (hk : C.k = c.n) {base : Addr} {t t' : State}
    (U : Unch base (slW c [QXM, QYM, TMP, W0, W1, W2, W3, PY] ++ [(c.sl FLAG, 8)]) t.mem t'.mem)
    (f' : word t'.mem base (c.sl FLAG) = mask (PeerOk c base t
      (((word t.mem base (c.sl FLAG) = BitVec.allOnes 64) ∧ sv c base t E < c.C.p) ∧ sv c base t QY < c.C.p)))
    (hf : word t.mem base (c.sl FLAG) = 0 ∨ word t.mem base (c.sl FLAG) = BitVec.allOnes 64)
    (x_lt : sv c base t' QXM < c.C.p)
    (x : toM c.C.p (2 ^ (64 * c.n)) (sv c base t' QXM) = Fin.ofNat c.C.p (sv c base t E))
    (y_lt : sv c base t' QYM < c.C.p)
    (y : toM c.C.p (2 ^ (64 * c.n)) (sv c base t' QYM) = Fin.ofNat c.C.p (sv c base t QY))
    (px : sv c base t' PX = (if PeerOk c base t
      (((word t.mem base (c.sl FLAG) = BitVec.allOnes 64) ∧ sv c base t E < c.C.p) ∧ sv c base t QY < c.C.p)
        then sv c base t' QXM else sv c base t GX))
    (py : sv c base t' PY = (if PeerOk c base t
      (((word t.mem base (c.sl FLAG) = BitVec.allOnes 64) ∧ sv c base t E < c.C.p) ∧ sv c base t QY < c.C.p)
        then sv c base t' QYM else sv c base t GY)) :
    C.post base t.mem t'.mem := by
  have h7 := hc.n10
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have ns : ∀ {i} (m : Mem), i < 45 → i ≠ TMP → C.num base m (C.slot i) = wordsVal m base (c.sl i) c.n :=
    fun m hi hT => num_sl hk h7 hi hT m base
  have nE : C.num base t.mem C.xAt = sv c base t E := ns t.mem (by decide) (by decide)
  have nY : C.num base t.mem C.yAt = sv c base t QY := ns t.mem (by decide) (by decide)
  have nXM : C.num base t'.mem C.xmAt = sv c base t' QXM := ns t'.mem (by decide) (by decide)
  have nYM : C.num base t'.mem C.ymAt = sv c base t' QYM := ns t'.mem (by decide) (by decide)
  have nPX : C.num base t'.mem C.pxAt = sv c base t' PX := ns t'.mem (by decide) (by decide)
  have nPY : C.num base t'.mem C.pyAt = sv c base t' PY := ns t'.mem (by decide) (by decide)
  have nGX : C.num base t.mem C.gxAt = sv c base t GX := ns t.mem (by decide) (by decide)
  have nGY : C.num base t.mem C.gyAt = sv c base t GY := ns t.mem (by decide) (by decide)
  have hR : C.R = 2 ^ (64 * c.n) := by unfold Impl.Weierstrass.CheckPoint.Curve.R; rw [hk]
  have hp : C.W.p = c.C.p := by rw [hW]
  have hP₀ : word t.mem base (c.sl FLAG) = mask (word t.mem base (c.sl FLAG) = BitVec.allOnes 64) := by
    rcases hf with h | h <;> rw [h] <;> decide
  have hV : C.Valid (sv c base t E) (sv c base t QY) ↔
      (sv c base t E < c.C.p ∧ sv c base t QY < c.C.p) ∧
        OnCurve c (Fin.ofNat c.C.p (sv c base t E)) (Fin.ofNat c.C.p (sv c base t QY)) := by
    obtain ⟨W, curve, k, desc⟩ := C
    dsimp only at hW
    subst hW
    simp only [Impl.Weierstrass.CheckPoint.Curve.Valid, onCurve_iff, and_assoc]
  have hfeq : word t.mem base (c.sl FLAG) &&&
      Impl.Weierstrass.CheckPoint.Curve.mask (C.Valid (sv c base t E) (sv c base t QY)) =
      word t'.mem base (c.sl FLAG) := by
    rw [f']
    conv => lhs; arg 1; rw [hP₀]
    simp only [Impl.Weierstrass.CheckPoint.Curve.mask]
    rw [show (if C.Valid (sv c base t E) (sv c base t QY) then BitVec.allOnes 64 else 0) =
        mask ((sv c base t E < c.C.p ∧ sv c base t QY < c.C.p) ∧
        OnCurve c (Fin.ofNat c.C.p (sv c base t E)) (Fin.ofNat c.C.p (sv c base t QY))) from if_congr hV rfl rfl,
      mask_and]
    exact if_congr (by
      constructor
      · rintro ⟨h₁, h₂, h₃⟩; exact ⟨⟨⟨h₁, h₂.1⟩, h₂.2⟩, h₃⟩
      · rintro ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩; exact ⟨h₁, ⟨h₂, h₃⟩, h₄⟩) rfl rfl
  have hz : ∀ {Q : Prop} [Decidable Q], (mask Q = 0) ↔ ¬Q := fun {Q} _ => by
    by_cases h : Q <;> simp only [mask, h, ite_true, ite_false, not_true, not_false_eq_true]; decide
  have xm : sv c base t' QXM = sv c base t E * 2 ^ (64 * c.n) % c.C.p :=
    toM_inj hpR x_lt (Nat.mod_lt _ (by have := hc.p_ge; omega_arith)) (by rw [x, toM_mont hpR])
  have ym : sv c base t' QYM = sv c base t QY * 2 ^ (64 * c.n) % c.C.p :=
    toM_inj hpR y_lt (Nat.mod_lt _ (by have := hc.p_ge; omega_arith)) (by rw [y, toM_mont hpR])
  unfold Impl.Weierstrass.CheckPoint.Curve.post
  dsimp only
  rw [nE, nY, nXM, nYM, nPX, nPY, nGX, nGY, hR, hp, flag_sl hk, flag_sl hk, hfeq, f']
  refine ⟨rfl, xm, ym, ?_, ?_, keeps_of_unch hk h7 U⟩
  · rw [px]
    by_cases hQ : PeerOk c base t
      (((word t.mem base (c.sl FLAG) = BitVec.allOnes 64) ∧ sv c base t E < c.C.p) ∧ sv c base t QY < c.C.p)
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hQ), ite_eq_right_of_eq_false _ _ (eq_false fun h => hz.mp h hQ), xm]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hQ), ite_eq_left_of_eq_true _ _ (eq_true (hz.mpr hQ))]
  · rw [py]
    by_cases hQ : PeerOk c base t
      (((word t.mem base (c.sl FLAG) = BitVec.allOnes 64) ∧ sv c base t E < c.C.p) ∧ sv c base t QY < c.C.p)
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hQ), ite_eq_right_of_eq_false _ _ (eq_false fun h => hz.mp h hQ), ym]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hQ), ite_eq_left_of_eq_true _ _ (eq_true (hz.mpr hQ))]

/-- `vg_<curve>_check_point` meets its contract, for a curve of the specification with the
code's prime, size and coefficients. -/
theorem check_correct (hc : BaseCfgOk c) {C : Impl.Weierstrass.CheckPoint.Curve}
    (hC : Impl.Ecdh.AArch64.Cfg.checkCurve c = some C) (hW : C.W = c.C) (hk : C.k = c.n)
    (s : State) (hs : (ptK C).pre s) :
    ∃ t s', Exec isa (Impl.Ecdh.AArch64.Cfg.checkFn c) s t s' ∧ abiPreserved s s' ∧ (ptK C).post s s' := by
  obtain ⟨-, hwr, hfit, hmp, hr2, hap, hbp, hf⟩ := hs
  have h7 := hc.n10
  have hck : Impl.Ecdh.AArch64.Cfg.checkCurve c ≠ none := by rw [hC]; exact Option.some_ne_none _
  have hS : Scr s (s.gpr .x0) size := ⟨rfl, by rw [hwr]; simp, hfit, by decide⟩
  have hR : C.R = c.R := by
    unfold Impl.Weierstrass.CheckPoint.Curve.R Cfg.R; rw [hk]
  have ns : ∀ {i}, i < 45 → i ≠ TMP → C.num (s.gpr .x0) s.mem (C.slot i) = sv c (s.gpr .x0) s i :=
    fun hi hT => num_sl hk h7 hi hT s.mem _
  have hmp' : sv c (s.gpr .x0) s MP = c.C.p := by
    rw [← ns (i := MP) (by decide) (by decide), ← hW]; exact hmp
  have hr2' : sv c (s.gpr .x0) s R2P = c.R * c.R % c.C.p := by
    rw [← ns (i := R2P) (by decide) (by decide), ← hW, ← hR]; exact hr2
  have hap' : sv c (s.gpr .x0) s AP = c.mont c.C.a := by
    rw [← ns (i := AP) (by decide) (by decide), Cfg.mont, ← hW, ← hR]; exact hap
  have hbp' : sv c (s.gpr .x0) s BP = c.mont c.C.b := by
    rw [← ns (i := BP) (by decide) (by decide), Cfg.mont, ← hW, ← hR]; exact hbp
  rw [flag_sl hk] at hf
  have hP₀ : word s.mem (s.gpr .x0) (c.sl FLAG) = mask (word s.mem (s.gpr .x0) (c.sl FLAG) = BitVec.allOnes 64) := by
    rcases hf with h | h <;> rw [h] <;> decide
  obtain ⟨hv, -, -⟩ := hc.check_fn hck
  have hkv : (Impl.Ecdh.AArch64.Cfg.checkFn c).allInstrs keepsV = true := by
    rw [Code.allInstrs_eq]
    exact List.all_eq_true.mpr fun i hi => by
      have := List.all_eq_true.mp ((Code.allInstrs_eq _ _) ▸ hv) i hi
      simp only [Bool.and_eq_true] at this
      exact this.2
  obtain ⟨t, s', he, K, P⟩ := checkFn_ok hc hck hS (R := fun _ m' => C.post (s.gpr .x0) s.mem m')
    fun u hu hum hug => by
      have e : ∀ i, sv c (s.gpr .x0) u i = sv c (s.gpr .x0) s i := fun i => by
        show wordsVal u.mem _ _ _ = wordsVal s.mem _ _ _; rw [hum]
      obtain ⟨tr, u', he', g', rd', wr', U', f', x_lt, x, y_lt, y, px, py⟩ :=
        checkBodyR_ok hc hu (by rw [e]; exact hmp') (by rw [e]; exact hap') (by rw [e]; exact hr2')
          (by rw [e]; exact hbp') (by rw [hum]; exact hP₀)
      refine ⟨tr, u', he', g', rd', wr', Exec.sp he', ?_⟩
      rw [← hum]
      rw [← hum] at hf
      exact post_of_raw hc hW hk U' (by rw [hum]; simpa only [e] using f') hf x_lt
        (by rw [x, e]) y_lt (by rw [y, e]) (by rw [px]; simp only [e, hum]) (by rw [py]; simp only [e, hum])
  exact ⟨t, s', he, ⟨fun r hr => K.gpr r fun h => (List.mem_filter.mp h).elim fun h₁ h₂ =>
      (checkKept_pres hc r hr).elim (· h₁) (by simpa using h₂), K.sp, Exec.preservedV he hkv⟩, P⟩

/-- The memory of `satState`: `p`, `R² mod p`, `a R mod p` and `b R mod p` at their
offsets of `ws = 0x1000`, zeros elsewhere. -/
@[irreducible] def satMem (C : Impl.Weierstrass.CheckPoint.Curve) : Mem := fun a =>
  let o := a.toNat - 0x1000
  let w (d v : Nat) (e : BitVec 8) : BitVec 8 :=
    if 0x1000 ≤ a.toNat ∧ d ≤ o ∧ o < d + 8 * C.k then BitVec.ofNat 8 (v >>> (8 * (o - d))) else e
  w C.pAt C.W.p <| w C.r2At (C.R * C.R % C.W.p) <| w C.aAt (C.W.a * C.R % C.W.p) <|
    w C.bAt (C.W.b * C.R % C.W.p) 0

/-- A state satisfying the precondition. -/
def satState (C : Impl.Weierstrass.CheckPoint.Curve) : State where
  gpr r := match r with
    | .x0 => 0x1000 | _ => 0
  sp := 0x10000
  mem := satMem C
  rd := []
  wr := [⟨0x1000, 8192⟩]

/-- The contract by name is the specification's, given a state satisfying it. -/
theorem check_implies (C : Impl.Weierstrass.CheckPoint.Curve) (hsat : C.pre 0x1000 (satMem C)) :
    (ptK C).Implies (C.checkContract AArch64.abi) where
  pre s h := by
    sig_pre [Impl.Weierstrass.CheckPoint.Curve.checkContract, Impl.Weierstrass.CheckPoint.sig,
      AArch64.abi, AArch64.argRegs, stackBelow] at h
    exact h
  post s s' _ h := by
    sig_post [Impl.Weierstrass.CheckPoint.Curve.checkContract, Impl.Weierstrass.CheckPoint.sig,
      AArch64.abi, AArch64.argRegs]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Impl.Weierstrass.CheckPoint.Curve.checkContract, Impl.Weierstrass.CheckPoint.sig,
      AArch64.abi, AArch64.argRegs] at h
    exact ⟨h.2, h.1⟩
  sat := ⟨satState C, by
    sig_pre [Impl.Weierstrass.CheckPoint.Curve.checkContract, Impl.Weierstrass.CheckPoint.sig,
      AArch64.abi, AArch64.argRegs, stackBelow]
    exact ⟨by decide, hsat⟩⟩

theorem agree (C : Impl.Weierstrass.CheckPoint.Curve) (s₁ s₂ : State) (_ : (ptK C).pre s₁)
    (_ : (ptK C).pre s₂) (h : (ptK C).pub s₁ s₂) :
    VG.AArch64.Taint.Agree (Taint.ofRegs [.x0]) s₁ s₂ :=
  ⟨h.2, fun r hr => by
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact h.1⟩

end VG.Proof.Ecdh.AArch64.CheckPoint
