module

public import VerifiedGarbage.Proof.Ecdh.RISCV64.P224.Tail
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Proof.Framework.RISCV64.Consts
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P224.CombLit
import VerifiedGarbage.Proof.Weierstrass.PointFacts
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Ecdsa.RISCV64.Comb.Tail
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.P224.Tail
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintSym
meta import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
meta import VerifiedGarbage.Proof.Framework.RISCV64.Consts
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P224.CombLit
meta import VerifiedGarbage.Proof.Weierstrass.PointFacts
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.RISCV64.Syms
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.Comb.Tail
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Comb.Main
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Comb.P224
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P224.MulFn
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.P224.Comb7
import VerifiedGarbage.Proof.P224.Point
import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.Comb.Main
meta import VerifiedGarbage.Impl.Ecdsa.RISCV64.Comb.P224
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P224.MulFn
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
meta import VerifiedGarbage.Proof.Weierstrass.Words
meta import VerifiedGarbage.Proof.P224.Comb7
meta import VerifiedGarbage.Proof.P224.Point
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes

/-! ### `Ecdsa.RISCV64.P224.Comb`, which only this module used -/

section

/-!
# The comb on RISC-V over P-224: the body

`vg_p224_mul_g`'s body, as `Proof/Ecdsa/RISCV64/Comb/Main.lean` proves
P-256's. P-224's words, slots and table's shape (37 rows of 64 entries of
eight quadwords) are P-256's, so the selection of an entry is Main's
(`select_okW`, for P-224's table); what differs is the curve: the entries'
points, the field's functions of the negation and the addition, and the
start.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.P224.Comb

open VG.Proof.Ecdsa.RISCV64.Comb (TabOkW tabWordsOf montOf kOf selRegs select_okW combSl addV stepW bodyW)

/-! ## The entry -/

section

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ecdsa.RISCV64.Comb VG.Proof.Mont VG.Impl.Ecdsa.RISCV64
open VG.Proof.Weierstrass.RISCV64 (maskOf WsReg)
open VG.Proof.Weierstrass (Unch combWin magH)
open VG.Proof.X25519.RISCV64 (Rest)

/-- The words of P-224's tables. -/
abbrev tabWords : List (BitVec 64) := tabWordsOf Spec.P224.curve.p Impl.P224.p224Comb7

/-- What the comb needs of P-224's table at `T`. -/
abbrev TabOk : State → Addr → Addr → Prop := TabOkW tabWords

theorem comb7_len : Impl.P224.p224Comb7.length = 37 := by decide

theorem comb7_lenH : ∀ j < 37, (Impl.P224.p224Comb7.getD j []).length = 64 := by decide

/-- `x R mod p`. -/
abbrev montP (x : Nat) : Nat := montOf Spec.P224.curve.p x

/-- Entry `e` of row `j`. -/
abbrev entOf (j e : Nat) : Nat × Nat := Proof.Weierstrass.combAt Impl.P224.p224Comb7 j e

/-- The selection depends on the curve only through its words. -/
theorem select_eq : Cfg.select p224 = Cfg.select p256 := rfl

/-- The entry of digit `j` of P-224's table in `D` (`select_okW`). -/
theorem select_ok {s : State} {base T : Addr} (hw : WsReg s base) {j : Nat} (hj : j < 37)
    (h1 : s.gpr .s1 = BitVec.ofNat 64 j) (h2 : s.gpr .s4 = T) (hT : TabOk s base T)
    (hz : word s.mem base (1536 + 32) = 0) (hZ : wordsVal s.mem base 160 4 = 0) :
    WP isa (.block (Cfg.select p224)) s fun s' =>
      wordsVal s'.mem base 608 4 = (if magH 64 (combWin 7 (kOf s.mem base) j) = 0 then 0
        else montP (entOf j (magH 64 (combWin 7 (kOf s.mem base) j) - 1)).1) ∧
      wordsVal s'.mem base 640 4 = (if magH 64 (combWin 7 (kOf s.mem base) j) = 0 then wordsVal s.mem base 224 4
        else montP (entOf j (magH 64 (combWin 7 (kOf s.mem base) j) - 1)).2) ∧
      wordsVal s'.mem base 672 4 = (if magH 64 (combWin 7 (kOf s.mem base) j) = 0 then 0
        else wordsVal s.mem base 224 4) ∧
      word s'.mem base 1024 = maskOf (decide (combWin 7 (kOf s.mem base) j < 64)) ∧
      Unch base [(608, 96), (1024, 16)] s.mem s'.mem ∧ Rest selRegs s s' := by
  rw [select_eq]
  exact select_okW comb7_len comb7_lenH (by decide) (by decide) hw hj h1 h2 hT hz hZ

end

/-! ## A step -/

section

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ecdsa.RISCV64.Comb VG.Proof.Mont VG.Impl.Ecdsa.RISCV64
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.Ecdsa.RISCV64.P224 (W field_ok unit)
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Curve Fe Point)

theorem mul_zero_pt (P : Point W) : Spec.Weierstrass.mul 0 P = .infinity := by
  rw [Spec.Weierstrass.mul]; simp

/-- `R mod p`, one in Montgomery's form. -/
abbrev oneM : Nat := 2 ^ 256 % W.p

/-- The value in `D.y` before the negation. -/
abbrev yDig (i v : Nat) : Nat := if magH 64 v = 0 then oneM else montP (entOf i (magH 64 v - 1)).2

theorem toM_montP (x : Nat) : toM W.p (2 ^ 256) (montP x) = Fin.ofNat W.p x := toM_mont unit

/-- The entry of digit `i`, `y` negated for a negative digit, represents the
digit's signed point. -/
theorem entry_rep (hL : Law W) {k i : Nat} (hi : i < 37) :
    Rep W (toM W.p (2 ^ 256) (if magH 64 (combWin 7 k i) = 0 then 0
        else montP (entOf i (magH 64 (combWin 7 k i) - 1)).1))
      (toM W.p (2 ^ 256) (if combWin 7 k i < 64 then (0 + W.p - yDig i (combWin 7 k i)) % W.p
        else yDig i (combWin 7 k i)))
      (toM W.p (2 ^ 256) (if magH 64 (combWin 7 k i) = 0 then 0 else oneM))
      (signedPtW W 7 k i) := by
  obtain hC := VG.Proof.P224.combOk7 hL
  obtain hv := combWin_lt 7 k i
  unfold signedPtW yDig
  generalize combWin 7 k i = v at hv ⊢
  simp only [show 2 ^ (7 - 1) = 64 from rfl]
  by_cases h64 : 64 ≤ v
  · have hmg : magH 64 v = v - 64 := by unfold magH; simp [h64]
    simp only [h64, ↓reduceIte, show ¬ v < 64 by omega_using [h64], hmg]
    by_cases h0 : v - 64 = 0
    · simp only [h0, ↓reduceIte, toM_zero, combPtW, Nat.zero_mul, mul_zero_pt]
      rw [toM_one unit]; exact rep_infinity' hL
    · obtain ⟨m, hm⟩ : ∃ m, v - 64 = m + 1 := ⟨v - 64 - 1, by omega_using [h0]⟩
      simp only [hm, Nat.add_one_ne_zero, ↓reduceIte, combPtW, Nat.add_sub_cancel]
      rw [hC.entry i hi m (by simp; omega_using [hv, hm]), toM_montP, toM_montP, toM_one unit]
      exact rep_affine' hL _ _
  · have hmg : magH 64 v = 64 - v := by unfold magH; simp [h64]
    obtain ⟨m, hm⟩ : ∃ m, 64 - v = m + 1 := ⟨64 - v - 1, by omega_using [h64]⟩
    simp only [h64, ↓reduceIte, show v < 64 by omega_using [h64], hmg, hm, Nat.add_one_ne_zero, combPtW, Nat.add_sub_cancel]
    rw [hC.entry i hi m (by simp; omega_using [hm]), toM_montP, toM_one unit,
      toM_sub (A := 0) (B := montP (entOf i m).2) (Nat.le_of_lt (Nat.lt_of_lt_of_le
        (Nat.mod_lt _ (by decide)) (Nat.le_of_eq (Nat.zero_add _).symm))),
      toM_zero, toM_montP]
    have := rep_affine' hL (Fin.ofNat W.p (entOf i m).1) (-Fin.ofNat W.p (entOf i m).2)
    simp only [negPt]
    rwa [show (0 : Fe W) - Fin.ofNat W.p (entOf i m).2 = -Fin.ofNat W.p (entOf i m).2 by grind]


/-! ## The negation and the addition -/

/-- `y = -y` by the sign's mask in `PT`. -/
theorem negate_ok {s : State} {base : Addr} (hw : WsReg s base) (hZ : wordsVal s.mem base 160 4 = 0)
    (hY : wordsVal s.mem base 640 4 < W.p) {c : Bool} (hPT : word s.mem base 1024 = maskOf c) :
    WP isa (Cfg.negate p224) s fun s' =>
      wordsVal s'.mem base 640 4 = (if c then (0 + W.p - wordsVal s.mem base 640 4) % W.p
        else wordsVal s.mem base 640 4) ∧
      Unch base [(992, 32), (3840, 256), (640, 32)] s.mem s'.mem ∧ Kp s s' := by
  have hn := hw.nowrap
  rw [Cfg.negate]
  refine WP.seq (WP.mono (subCall_ok field_ok hw (o := p224.sl ACC) (a := p224.sl ZERO) (b := p224.sl DY)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by show wordsVal s.mem base 160 4 < _; rw [hZ]; decide) hY) fun s₁ ⟨K₁, v₁⟩ => ?_)
  obtain hw₁ := hw.of_kp K₁.kp
  obtain U₁ : Unch base [(992, 32), (3840, 256)] s.mem s₁.mem := fun x hx => K₁.mem x hx
  rw [List.cons_append, List.nil_append]
  refine ld_ws hw₁ (d := 1024) (by decide) (by decide) fun s₂ u₂ => ?_
  obtain a7 : s₂.gpr .a7 = maskOf c := by
    rw [u₂.gpr, U₁.word (by simp) (by omega_using []), hPT]
  obtain hw₂ := hw₁.of_rest (u₂.rest (ws := [.a7]) (by decide))
  refine WP.mono (sel_ok c 4 hw₂ a7 (o := 640) (a := 640) (b := 992) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)) fun s₃ ⟨e₃, r₃, O₃⟩ => ⟨?_, ?_, ?_⟩
  · have hacc : wordsVal s₂.mem base 992 4 = (0 + W.p - wordsVal s.mem base 640 4) % W.p := by
      rw [u₂.mem]
      have : wordsVal s₁.mem base 992 4 =
          (wordsVal s.mem base 160 4 + W.p - wordsVal s.mem base 640 4) % W.p := v₁
      rw [hZ] at this
      exact this
    obtain hy : wordsVal s₂.mem base 640 4 = wordsVal s.mem base 640 4 := by
      rw [u₂.mem]; exact U₁.wordsVal (by simp) (by omega_using [])
    rw [e₃, hacc, hy]
  · have O₃' := O₃; rw [u₂.mem] at O₃'; exact U₁.trans O₃'.unch
  · exact K₁.kp.trans (Kp.of_rest ((u₂.rest (ws := [.a7]) (by decide)).mono (by decide) |>.trans
      (r₃.mono (by decide))) (ws := [.a7, .t0, .t1]) (by decide))

theorem combLay : Lay p224.MP' (own 4) (· ∈ combSl) :=
  ⟨by decide, fun x y hx hy => (by decide : ∀ x ∈ combSl, ∀ y ∈ combSl, x ≠ y → x + 8 * 4 ≤ y ∨ y + 8 * 4 ≤ x)
    x hx y hy, by decide, by decide⟩

/-- P-224's `a` is `-3`. -/
theorem am3 : AM3 W := by unfold AM3; decide

/-- `T = R + D` by the complete addition for `a = -3`, then `R = T`. -/
theorem addR_ok {s : State} {base : Addr} (hw : WsReg s base) (hlt : ∀ x ∈ addV, wordsVal s.mem base x 4 < W.p) :
    WP isa (.seq (fprog p224.FP (rcb3 p224.rcb3Slots (p224.pt RX RY RZ) (p224.pt DX DY DZ) (p224.pt TX TY TZ)))
      (.block (copy 4 (p224.sl RX) (p224.sl TX) ++ copy 4 (p224.sl RY) (p224.sl TY) ++
        copy 4 (p224.sl RZ) (p224.sl TZ)))) s fun s' =>
      Kp s s' ∧ Unch base [(512, 512), (3840, 256)] s.mem s'.mem ∧
      (∀ x ∈ [512, 544, 576], wordsVal s'.mem base x 4 < W.p) ∧
      (tmv W 4 base s' 512, tmv W 4 base s' 544, tmv W 4 base s' 576) =
        rcbAdd3 (tmv W 4 base s 1344) (tmv W 4 base s 512) (tmv W 4 base s 544)
          (tmv W 4 base s 576) (tmv W 4 base s 608) (tmv W 4 base s 640) (tmv W 4 base s 672) := by
  have hn := hw.nowrap
  obtain hI : Inv 4 base W.p (· ∈ combSl) addV (fun x => tmv W 4 base s x) s :=
    ⟨hw, by decide, hlt, fun _ _ => rfl⟩
  refine WP.seq (WP.mono (rcb3_ok (M := p224.MP') (F := p224Field) field_ok rfl combLay
    (fun x hx => by have := (by decide : ∀ x ∈ combSl, x < 4095) x hx; exact this) unit
    (S := p224.rcb3Slots) (p := p224.pt RX RY RZ) (q := p224.pt DX DY DZ) (o := p224.pt TX TY TZ)
    ⟨by decide, by decide⟩ (by decide) hI (by decide)) fun s₁ ⟨K₁, I₁, v₁⟩ => ?_)
  obtain hw₁ := hw.of_kp K₁.kp
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (copy_ok 4 hw₁ (o := 512) (a := 704) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₂ ⟨e₂, r₂, O₂⟩ => ?_)
  obtain hw₂ := hw₁.of_rest r₂
  refine WP.block_append (WP.mono (copy_ok 4 hw₂ (o := 544) (a := 736) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₃ ⟨e₃, r₃, O₃⟩ => ?_)
  obtain hw₃ := hw₂.of_rest r₃
  refine WP.mono (copy_ok 4 hw₃ (o := 576) (a := 768) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₄ ⟨e₄, r₄, O₄⟩ => ?_
  obtain tx : wordsVal s₄.mem base 512 4 = wordsVal s₁.mem base 704 4 := by
    rw [O₄.wordsVal (by omega_using []) (by omega_using []), O₃.wordsVal (by omega_using []) (by omega_using []), e₂]
  obtain ty : wordsVal s₄.mem base 544 4 = wordsVal s₁.mem base 736 4 := by
    rw [O₄.wordsVal (by omega_using []) (by omega_using []), e₃, O₂.wordsVal (by omega_using []) (by omega_using [])]
  obtain tz : wordsVal s₄.mem base 576 4 = wordsVal s₁.mem base 768 4 := by
    rw [e₄, O₃.wordsVal (by omega_using []) (by omega_using []), O₂.wordsVal (by omega_using []) (by omega_using [])]
  obtain hT : ∀ x ∈ [704, 736, 768], x ∈ [(p224.pt TX TY TZ).x, (p224.pt TX TY TZ).y, (p224.pt TX TY TZ).z] ++ addV := by
    decide
  refine ⟨K₁.kp.trans (Kp.of_rest ((r₂.trans r₃).trans r₄)), ?_, ?_, ?_⟩
  · have U₁ : Unch base ((rcbW p224.rcb3Slots (p224.pt TX TY TZ)).map (fun w => (w, 8 * 4)) ++ [(own 4, 64 * 4)])
        s.mem s₁.mem := fun x hx => K₁.mem x hx
    exact (((U₁.trans O₂.unch).trans O₃.unch).trans O₄.unch).cover (by decide)
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [tx]; exact I₁.lt 704 (hT 704 (by simp))
    · rw [ty]; exact I₁.lt 736 (hT 736 (by simp))
    · rw [tz]; exact I₁.lt 768 (hT 768 (by simp))
  · simp only [tmv]
    obtain h704 : toM W.p (2 ^ (64 * 4)) (wordsVal s₁.mem base 704 4) = _ := I₁.val 704 (hT 704 (by simp))
    obtain h736 : toM W.p (2 ^ (64 * 4)) (wordsVal s₁.mem base 736 4) = _ := I₁.val 736 (hT 736 (by simp))
    obtain h768 : toM W.p (2 ^ (64 * 4)) (wordsVal s₁.mem base 768 4) = _ := I₁.val 768 (hT 768 (by simp))
    rw [tx, ty, tz, h704, h736, h768]
    exact v₁


/-! ## A step -/

/-- What the steps read, as the loop's start `s₀` holds it. -/
structure CombPre (base T : Addr) (s₀ : State) : Prop where
  s4 : s₀.gpr .s4 = T
  kz : word s₀.mem base (1536 + 32) = 0
  zero : wordsVal s₀.mem base 160 4 = 0
  one : wordsVal s₀.mem base 224 4 = oneM
  a : tmv W 4 base s₀ 256 = Fin.ofNat W.p W.a
  b : tmv W 4 base s₀ 1344 = Fin.ofNat W.p W.b
  alt : wordsVal s₀.mem base 256 4 < W.p
  blt : wordsVal s₀.mem base 1344 4 < W.p

/-- The loop's invariant at `s1 = j`: `R` represents `[combEW j]G`, for the
scalar the start holds. -/
structure CombInv (base T : Addr) (s₀ s : State) (j : Nat) : Prop where
  ws : WsReg s base
  ctr : s.gpr .s1 = BitVec.ofNat 64 j
  keep : Kc s₀ s
  unch : Unch base stepW s₀.mem s.mem
  tab : TabOk s base T
  lt : ∀ x ∈ [512, 544, 576], wordsVal s.mem base x 4 < W.p
  rep : Rep W (tmv W 4 base s 512) (tmv W 4 base s 544) (tmv W 4 base s 576)
    (Spec.Weierstrass.mul (combEW 7 (kOf s₀.mem base) 37 j) (Spec.Weierstrass.G W))

theorem signed_onCurve (hL : Law W) (k i : Nat) : Spec.Weierstrass.onCurve W (signedPtW W 7 k i) = true := by
  unfold signedPtW combPtW
  split
  · exact hL.onCurve_mul VG.Proof.P224.onCurve_G _
  · exact onCurve_negPt (hL.onCurve_mul VG.Proof.P224.onCurve_G _)

/-- A step: from `[combEW j]G` to `[combEW (j - 1)]G`. -/
theorem step_ok (hL : Law W) {base T : Addr} {s₀ : State} (hP : CombPre base T s₀) {j : Nat} (hj1 : 1 ≤ j)
    (hj : j ≤ 37) {s : State} (hI : CombInv base T s₀ s j) :
    WP isa (Cfg.step p224) s fun s' => CombInv base T s₀ s' (j - 1) := by
  have hn := hI.ws.nowrap
  obtain uS : ∀ d, d + 32 ≤ 512 ∨ 1056 ≤ d → d + 32 ≤ 3840 →
      wordsVal s.mem base d 4 = wordsVal s₀.mem base d 4 := fun d h h' =>
    hI.unch.wordsVal (by simp; omega_using [h, h']) (by omega_using [h'])
  obtain hk : kOf s.mem base = kOf s₀.mem base := uS 1536 (by omega_using []) (by omega_using [])
  rw [Cfg.step]
  -- `s1 -= 1` and the entry.
  refine WP.seq (wp_decCounter hj1 hI.ctr fun s₁ u₁ => ?_)
  obtain hw₁ := hI.ws.of_kc (Kc.of_rest (u₁.rest (ws := [.s1]) (by decide)))
  refine WP.mono (select_ok hw₁ (j := j - 1) (by omega_using [hj]) u₁.gpr
    (by rw [u₁.other _ (by decide), hI.keep.gpr _ (by decide) (by decide), hP.s4])
    (hI.tab.of_mem u₁.rd fun x _ => by rw [u₁.mem])
    (by rw [u₁.mem, hI.unch.word (by simp) (by omega_using []), hP.kz])
    (by rw [u₁.mem, uS 160 (by omega_using []) (by omega_using []), hP.zero])) fun s₂ ⟨dx₂, dy₂, dz₂, pt₂, U₂, r₂⟩ => ?_
  rw [u₁.mem, hk] at dx₂ dy₂ dz₂ pt₂
  rw [u₁.mem] at U₂
  rw [uS 224 (by omega_using []) (by omega_using []), hP.one] at dy₂ dz₂
  obtain hw₂ := hw₁.of_rest r₂
  generalize hv : combWin 7 (kOf s₀.mem base) (j - 1) = v at dx₂ dy₂ dz₂ pt₂
  obtain hv128 : v < 128 := hv ▸ combWin_lt 7 _ _
  -- What the slots hold so far.
  obtain uS₂ : ∀ d, d + 32 ≤ 512 ∨ 1056 ≤ d → d + 32 ≤ 3840 →
      wordsVal s₂.mem base d 4 = wordsVal s₀.mem base d 4 := fun d h h' => by
    rw [U₂.wordsVal (by simp; omega_using [h]) (by omega_using [h']), uS d h h']
  obtain hR₂ : ∀ d ∈ [512, 544, 576], wordsVal s₂.mem base d 4 = wordsVal s.mem base d 4 := by
    intro d hd; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;> exact U₂.wordsVal (by simp) (by omega_using [])
  obtain hlt1 : oneM < W.p := Nat.mod_lt _ (by decide)
  obtain hlty : yDig (j - 1) v < W.p := by
    unfold yDig; split
    · exact hlt1
    · exact Nat.mod_lt _ (by decide)
  -- The negation.
  refine WP.seq (WP.mono (negate_ok hw₂ (by rw [uS₂ 160 (by omega_using []) (by omega_using []), hP.zero])
    (by rw [dy₂]; exact hlty) pt₂) fun s₃ ⟨dy₃, U₃, K₃⟩ => ?_)
  rw [dy₂] at dy₃
  obtain hw₃ := hw₂.of_kp K₃
  obtain e₃ : ∀ d, (d + 32 ≤ 640 ∨ 672 ≤ d) → (d + 32 ≤ 992 ∨ 1024 ≤ d) → d + 32 ≤ 3840 →
      wordsVal s₃.mem base d 4 = wordsVal s₂.mem base d 4 := fun d h1 h2 h3 =>
    U₃.wordsVal (by simp; omega_using [h1, h2, h3]) (by omega_using [h3])
  -- The addition.
  obtain hlt₃ : ∀ x ∈ addV, wordsVal s₃.mem base x 4 < W.p := by
    intro x hx
    simp only [addV, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [e₃ _ (by omega_using []) (by omega_using []) (by omega_using []), uS₂ _ (by omega_using []) (by omega_using [])]; exact hP.alt
    · rw [e₃ _ (by omega_using []) (by omega_using []) (by omega_using []), uS₂ _ (by omega_using []) (by omega_using [])]; exact hP.blt
    · rw [e₃ _ (by omega_using []) (by omega_using []) (by omega_using []), hR₂ 512 (by simp)]; exact hI.lt 512 (by simp)
    · rw [e₃ _ (by omega_using []) (by omega_using []) (by omega_using []), hR₂ 544 (by simp)]; exact hI.lt 544 (by simp)
    · rw [e₃ _ (by omega_using []) (by omega_using []) (by omega_using []), hR₂ 576 (by simp)]; exact hI.lt 576 (by simp)
    · rw [e₃ _ (by omega_using []) (by omega_using []) (by omega_using []), dx₂]; split
      · decide
      · exact Nat.mod_lt _ (by decide)
    · rw [dy₃]; split
      · exact Nat.mod_lt _ (by decide)
      · exact hlty
    · rw [e₃ _ (by omega_using []) (by omega_using []) (by omega_using []), dz₂]; split
      · decide
      · exact hlt1
  refine WP.mono (addR_ok hw₃ hlt₃) fun s₄ ⟨K₄, U₄, lt₄, v₄⟩ => ?_
  -- The invariant.
  obtain hU : Unch base stepW s₀.mem s₄.mem :=
    (((hI.unch.trans U₂).trans U₃).trans U₄).cover (by decide)
  refine ⟨hw₃.of_kp K₄, ?_, ?_, hU, ?_, lt₄, ?_⟩
  · rw [K₄.gpr _ (by decide), K₃.gpr _ (by decide), r₂.gpr _ (by decide), u₁.gpr]
  · exact ((hI.keep.trans (Kc.of_rest (u₁.rest (ws := [.s1]) (by decide)))).trans
      (Kc.of_rest r₂)).trans (K₃.kc.trans K₄.kc)
  · exact (hI.tab.of_unch (by rw [K₄.rd, K₃.rd, r₂.rd, u₁.rd]) (W := [(608, 96), (1024, 16)] ++
      [(992, 32), (3840, 256), (640, 32)] ++ [(512, 512), (3840, 256)]) (by decide)
      ((U₂.trans U₃).trans U₄))
  · -- `T = R + D`, with `D` the signed entry.
    obtain eb : tmv W 4 base s₃ 1344 = Fin.ofNat W.p W.b := by
      simp only [tmv]; rw [e₃ _ (by omega_using []) (by omega_using []) (by omega_using []), uS₂ _ (by omega_using []) (by omega_using [])]; exact hP.b
    obtain eR : ∀ d ∈ [512, 544, 576], tmv W 4 base s₃ d = tmv W 4 base s d := by
      intro d hd
      simp only [tmv]
      have := hR₂ d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rw [e₃ d (by omega_using [hd]) (by omega_using [hd]) (by omega_using [hd]), this]
    obtain hD := entry_rep hL (k := kOf s₀.mem base) (i := j - 1) (by omega_using [hj])
    rw [hv] at hD
    obtain ex : tmv W 4 base s₃ 608 = toM W.p (2 ^ 256) (if magH 64 v = 0 then 0
        else montP (entOf (j - 1) (magH 64 v - 1)).1) := by
      simp only [tmv]; rw [e₃ _ (by omega_using []) (by omega_using []) (by omega_using []), dx₂]
    obtain ey : tmv W 4 base s₃ 640 = toM W.p (2 ^ 256) (if v < 64 then (0 + W.p - yDig (j - 1) v) % W.p
        else yDig (j - 1) v) := by
      simp only [tmv]; rw [dy₃]; simp only [decide_eq_true_eq, yDig]
    obtain ez : tmv W 4 base s₃ 672 = toM W.p (2 ^ 256) (if magH 64 v = 0 then 0 else oneM) := by
      simp only [tmv]; rw [e₃ _ (by omega_using []) (by omega_using []) (by omega_using []), dz₂]
    rw [eb, eR 512 (by simp), eR 544 (by simp), eR 576 (by simp), ex, ey, ez] at v₄
    obtain hS := hL.add3 am3 (hL.onCurve_mul VG.Proof.P224.onCurve_G _) (signed_onCurve hL (kOf s₀.mem base) (j - 1))
      hI.rep hD v₄.symm
    obtain hadd := combW_add hL VG.Proof.P224.onCurve_G (w := 7) (k := kOf s₀.mem base) (J := 37) (j := j - 1) (by omega_using [hj])
    rw [Nat.sub_add_cancel hj1] at hadd
    unfold signedPtW at hS
    rw [hadd] at hS
    exact hS

end

/-! ## The body -/

section

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ecdsa.RISCV64.Comb VG.Proof.Mont VG.Impl.Ecdsa.RISCV64
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.Ecdsa.RISCV64.P224 (W field_ok unit)
open VG.Proof.X25519.RISCV64 (Rest)


/-- The body: `R = [k]G`, for the number `k` at `K`'s slot. -/
theorem body_ok (hL : Law W) {s : State} {base T : Addr} (hw : WsReg s base) (h2 : s.gpr .s4 = T)
    (hT : TabOk s base T) (hz : wordsVal s.mem base 160 4 = 0) (hone : wordsVal s.mem base 224 4 = oneM)
    (ha : tmv W 4 base s 256 = Fin.ofNat W.p W.a) (hb : tmv W 4 base s 1344 = Fin.ofNat W.p W.b)
    (hap : wordsVal s.mem base 256 4 < W.p) (hbp : wordsVal s.mem base 1344 4 < W.p) :
    WP isa (Cfg.body p224 Impl.P224.p224Comb7Start) s fun s' =>
      Kc s s' ∧ Unch base bodyW s.mem s'.mem ∧ TabOk s' base T ∧
      (∀ x ∈ [512, 544, 576], wordsVal s'.mem base x 4 < W.p) ∧
      Rep W (tmv W 4 base s' 512) (tmv W 4 base s' 544) (tmv W 4 base s' 576)
        (Spec.Weierstrass.mul (wordsVal s.mem base 1056 4) (Spec.Weierstrass.G W)) := by
  have hn := hw.nowrap
  obtain hC := VG.Proof.P224.combOk7 hL
  rw [Cfg.body]
  simp only [List.append_assoc]
  -- The copy of `k`, and its zero word.
  refine WP.seq ?_
  refine WP.block_append (WP.mono (copy_ok 4 hw (o := 1536) (a := 1056) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₁ ⟨e₁, r₁, O₁⟩ => ?_)
  obtain hw₁ := hw.of_rest r₁
  rw [VG.Proof.Weierstrass.RISCV64.sdAt_lo (by decide)]
  simp only [List.cons_append, List.nil_append]
  refine wp_li (imm := 0) (by decide) fun s₂ u₂ => ?_
  obtain hw₂ := hw₁.of_rest (u₂.rest (ws := [.t0]) (by decide))
  refine sd_ws hw₂ (d := 1568) (by decide) (by decide) fun s₃ u₃ => ?_
  obtain hw₃ := hw₂.of_rest (u₃.rest [])
  obtain O₃ : Outside base 1568 8 s₂.mem s₃.mem := by rw [u₃.mem]; exact writeW_outside _ _ _ (by omega_using [])
  -- `R = S`.
  refine WP.block_append (WP.mono (setConst_ok 4 hw₃ (o := 512) (x := VG.Impl.Ecdh.RISCV64.Cfg.mont p224
    Impl.P224.p224Comb7Start.1) (by decide) (by decide)) fun s₄ ⟨r₄, O₄, e₄⟩ => ?_)
  obtain hw₄ := hw₃.of_rest r₄
  refine WP.block_append (WP.mono (setConst_ok 4 hw₄ (o := 544) (x := VG.Impl.Ecdh.RISCV64.Cfg.mont p224
    Impl.P224.p224Comb7Start.2) (by decide) (by decide)) fun s₅ ⟨r₅, O₅, e₅⟩ => ?_)
  obtain hw₅ := hw₄.of_rest r₅
  refine WP.block_append (WP.mono (copy_ok 4 hw₅ (o := 576) (a := 224) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₆ ⟨e₆, r₆, O₆⟩ => ?_)
  obtain hw₆ := hw₅.of_rest r₆
  refine wp_li (imm := 37) (by decide) fun s₇ u₇ => WP.block_nil ?_
  obtain r₇ : Rest [.t0, .t1] s s₆ :=
    ((r₁.mono (by decide)).trans ((u₂.rest (ws := [.t0, .t1]) (by decide)).trans (u₃.rest _))).trans
      ((r₄.trans r₅).trans (r₆.mono (by decide)))
  obtain hw₇ : WsReg s₇ base := hw₆.of_kc (Kc.of_rest (u₇.rest (ws := [.s1]) (by decide)))
  obtain U₆ : Unch base [(1536, 32), (1568, 8), (512, 32), (544, 32), (576, 32)] s.mem s₆.mem := by
    obtain O₃' : Outside base 1568 8 s₁.mem s₃.mem := by rw [← u₂.mem]; exact O₃
    exact (((O₁.unch.trans O₃'.unch).trans O₄.unch).trans O₅.unch).trans O₆.unch
  obtain U₇ : Unch base [(1536, 32), (1568, 8), (512, 32), (544, 32), (576, 32)] s.mem s₇.mem := by
    rw [u₇.mem]; exact U₆
  obtain e7 : ∀ d, (d + 32 ≤ 512 ∨ 608 ≤ d) → (d + 32 ≤ 1536 ∨ 1576 ≤ d) → d + 32 ≤ 3840 →
      wordsVal s₇.mem base d 4 = wordsVal s.mem base d 4 := fun d h1 h2 h3 =>
    U₇.wordsVal (by simp; omega_using [h1, h2]) (by omega_using [h3])
  -- The loop's start.
  obtain hP : CombPre base T s₇ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₇.other _ (by decide), r₇.gpr _ (by decide), h2]
    · show word s₇.mem base 1568 = 0
      rw [u₇.mem, O₆.word (by omega_using []) (by omega_using []), O₅.word (by omega_using []) (by omega_using []), O₄.word (by omega_using []) (by omega_using []),
        u₃.mem, word_writeW_self, u₂.gpr]; rfl
    · rw [e7 160 (by omega_using []) (by omega_using []) (by omega_using [])]; exact hz
    · rw [e7 224 (by omega_using []) (by omega_using []) (by omega_using [])]; exact hone
    · simp only [tmv]; rw [e7 256 (by omega_using []) (by omega_using []) (by omega_using [])]; exact ha
    · simp only [tmv]; rw [e7 1344 (by omega_using []) (by omega_using []) (by omega_using [])]; exact hb
    · rw [e7 256 (by omega_using []) (by omega_using []) (by omega_using [])]; exact hap
    · rw [e7 1344 (by omega_using []) (by omega_using []) (by omega_using [])]; exact hbp
  obtain hk : kOf s₇.mem base = wordsVal s.mem base 1056 4 := by
    show wordsVal s₇.mem base 1536 4 = _
    rw [u₇.mem, O₆.wordsVal (by omega_using []) (by omega_using []), O₅.wordsVal (by omega_using []) (by omega_using []),
      O₄.wordsVal (by omega_using []) (by omega_using []), O₃.wordsVal (by omega_using []) (by omega_using []), u₂.mem, e₁]
  obtain hT₇ : TabOk s₇ base T := hT.of_unch (by rw [u₇.rd, r₆.rd, r₅.rd, r₄.rd, u₃.rd, u₂.rd, r₁.rd])
    (by decide) U₇
  obtain ex : wordsVal s₇.mem base 512 4 = montP Impl.P224.p224Comb7Start.1 := by
    rw [u₇.mem, O₆.wordsVal (by omega_using []) (by omega_using []), O₅.wordsVal (by omega_using []) (by omega_using []), e₄]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))
  obtain ey : wordsVal s₇.mem base 544 4 = montP Impl.P224.p224Comb7Start.2 := by
    rw [u₇.mem, O₆.wordsVal (by omega_using []) (by omega_using []), e₅]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))
  obtain ez : wordsVal s₇.mem base 576 4 = oneM := by
    rw [u₇.mem, e₆, O₅.wordsVal (by omega_using []) (by omega_using []), O₄.wordsVal (by omega_using []) (by omega_using []),
      O₃.wordsVal (by omega_using []) (by omega_using []), u₂.mem, O₁.wordsVal (by omega_using []) (by omega_using [])]; exact hone
  obtain hI : CombInv base T s₇ s₇ 37 := by
    refine ⟨hw₇, u₇.gpr, Kc.refl _, Unch.refl _ _ _, hT₇, ?_, ?_⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · rw [ex]; exact Nat.mod_lt _ (by decide)
      · rw [ey]; exact Nat.mod_lt _ (by decide)
      · rw [ez]; exact Nat.mod_lt _ (by decide)
    · simp only [tmv]
      rw [ex, ey, ez, toM_montP, toM_montP, show 2 ^ (64 * 4) = 2 ^ 256 from rfl, toM_one unit,
        combEW_top, show 7 - 1 = 6 from rfl, show 2 ^ 6 = 2 ^ (7 - 1) from rfl, hC.start]
      exact rep_affine' hL _ _
  -- The steps.
  refine countLoop_ok (Inv := fun j s' => CombInv base T s₇ s' j) (n := 37) (fun j s' hi => hi.ctr)
    (fun j s' h1 h2 hi => step_ok hL hP h1 h2 hi) (fun s' hi => ?_) (by decide) (by decide) hI
  refine ⟨(Kc.of_rest r₇).trans ((Kc.of_rest (u₇.rest (ws := [.s1]) (by decide))).trans hi.keep),
    ((U₇.trans hi.unch).cover (by decide)), hi.tab, hi.lt, ?_⟩
  have hr := hi.rep
  rw [hk, combEW_zero (by have := wordsVal_lt s.mem base 1056 4; omega_using [this])] at hr
  exact hr

end

end VG.Proof.Ecdsa.RISCV64.P224.Comb

end

end

/-!
# `vg_p224_mul_g` on RISC-V: the contract, and ECDH's `tail` with it

`vg_p224_mul_g(ws = a0)`, an internal function: `vg_p224_mul`'s contract
(`mulRVc`) for `Q = G`, with the table of the comb (`VG_P224_COMB`, its only
readable region): `mulGRVc`, which `mulG_rv` proves from `body_ok` around the
table's address (`lla`), the saves past the numbered slots and their loads.
`tailG_ok` is ECDH's
`tail` with `R = [k]G` by a call of it, for P-224's signatures and public
keys, as `Proof/Ecdsa/RISCV64/Comb/Tail.lean` gives P-256's.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.P224.Comb

open VG.Proof.Ecdsa.RISCV64.Comb (WP.mono_syms WP.of_syms wp_syms_frame bodyW)

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ecdsa.RISCV64.Comb VG.Proof.Mont VG.Impl.Ecdsa.RISCV64
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.Ecdsa.RISCV64.P224 (W MC coordAt_eq represents_of_rep unit)
open VG.Spec.Weierstrass (Curve Fe Point)

/-- The table's region, at the address `lla` gives its symbol. -/
abbrev tabRegion (s : State) : Region := ⟨s.syms p224Sym, 151552⟩

/-- `vg_p224_mul_g(ws = a0)`: the table its only readable region, its words
there, at a multiple of 64, apart from the working space; `b` in Montgomery's
form at slot 40 (byte 1344), for the complete addition for `a = -3`. -/
def mulGRVc : Contract isa where
  pre s := s.rd = [tabRegion s] ∧ s.wr = [⟨s.gpr .a0, 8192⟩] ∧ (s.gpr .a0).toNat + 8192 ≤ 2 ^ 64 ∧
    (s.gpr .a0).toNat % 8 = 0 ∧ MC.ConstsOk (s.gpr .a0) s.mem ∧
    wordsVal s.mem (s.gpr .a0) 1344 4 = W.b * 2 ^ 256 % W.p ∧
    (∀ i < 18944, s.mem.readW (s.syms p224Sym + BitVec.ofNat 64 (8 * i)) 64 = p224CombWords.getD i 0) ∧
    (s.syms p224Sym).toNat % 64 = 0 ∧ (s.syms p224Sym).toNat + 151552 ≤ 2 ^ 64 ∧
    Region.Disjoint (tabRegion s) ⟨s.gpr .a0, 8192⟩
  post s s' := MC.ResultInRange (MC.scalar (s.gpr .a0) s.mem) (Spec.Weierstrass.G W) (s.gpr .a0) s.mem s'.mem
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.syms p224Sym = s₂.syms p224Sym

theorem combWords_eq : p224CombWords = tabWords := by unfold p224CombWords; rfl

/-- The table, apart from the working space. -/
theorem tabOk_of_pre {s : State} {base : Addr} (hrd : (tabRegion s) ∈ s.rd)
    (hheld : ∀ i < 18944, s.mem.readW (s.syms p224Sym + BitVec.ofNat 64 (8 * i)) 64 = p224CombWords.getD i 0)
    (hal : (s.syms p224Sym).toNat % 64 = 0) (hfit : (s.syms p224Sym).toNat + 151552 ≤ 2 ^ 64)
    (hd : Region.Disjoint (tabRegion s) ⟨base, 8192⟩) : TabOk s base (s.syms p224Sym) where
  held i hi := by rw [hheld i hi, combWords_eq]
  al := hal
  rd := hrd
  fit := hfit
  far d hd' := by
    obtain hc : (tabRegion s).Contains (s.syms p224Sym + BitVec.ofNat 64 d) 1 :=
      Offset.contains_base _ (by omega_using [hd']) (by omega_using [hd'])
    have := hd _ hc
    simp only [Region.Contains, Nat.not_le] at this
    simp only [ofs]; omega_using [this]

/-- The saves, at `mulSave = 1504`. -/
abbrev savesG : List (Nat × Nat) := [(1504, 8), (1512, 8), (1520, 8), (1528, 8)]

/-- What the function writes is its own working space or the result's. -/
theorem keepsG_of_unch {ws : Addr} {m m' : Mem} (hu : Unch ws (savesG ++ bodyW) m m') : MC.Keeps ws m m' := by
  intro i hi hown hp
  have h8 : Impl.Weierstrass.Mont.wsBytes = 8192 := rfl
  refine hu _ fun w hw => ?_
  rw [show ws + BitVec.ofNat 64 i = off ws i from rfl, ofs_off0 ws (by omega_using [hi, h8])]
  obtain hw' := (by decide : ∀ w ∈ savesG ++ bodyW, (w.1 = 512 ∧ w.2 = 544) ∨ 1504 ≤ w.1) w hw
  simp only [Impl.Weierstrass.Mul.Curve.Own, Impl.Weierstrass.Mul.Curve.slot, Impl.Weierstrass.Mul.Curve.tmpAt,
    Impl.Weierstrass.Mul.Curve.bitsAt, Impl.Weierstrass.Mul.Curve.pAt, Impl.Weierstrass.Mul.Curve.ptBytes,
    MC, Impl.Weierstrass.Mul.p224, true_and] at hown hp
  omega_using [hp, hw', hown]

/-- `vg_p224_mul_g` meets `mulGRVc`, given the group law. -/
theorem mulG_rv (hL : Law W) (s : State) (hs : mulGRVc.pre s) :
    ∃ t s', Exec isa mulGP224 s t s' ∧ abiPreserved s s' ∧ mulGRVc.post s s' := by
  obtain ⟨hrd, hwr, hfit, hal, ⟨-, hz, hone, ha, -⟩, hbp, hheld, htal, htfit, hdisj⟩ := hs
  generalize hb : s.gpr .a0 = base at hwr hfit hal hz hone ha hbp hdisj
  have hT₀ : TabOk s base (s.syms p224Sym) :=
    tabOk_of_pre (by rw [hrd]; exact List.mem_singleton_self _) hheld htal htfit hdisj
  have hwr' : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hwr]; exact List.mem_singleton_self _
  have dq : ∀ x, MC.toPoint.dec x = toM W.p (2 ^ 256) x :=
    VG.Proof.Weierstrass.Point.dec_eq MC.toPoint hL.one_ne_zero (VG.Proof.Weierstrass.Point.fermat_of_law hL) unit
  suffices h : WP isa mulGP224 s fun s' => abiPreserved s s' ∧ mulGRVc.post s s' by
    obtain ⟨t, s', he, h⟩ := h; exact ⟨t, s', he, h⟩
  rw [mulGP224, Cfg.combFn, show p224.mulSave = 1504 from rfl]
  refine WP.seq (WP.cons exec_lla ?_)
  generalize hs₀ : s.write .t0 (s.syms p224Sym) = s₀
  have u₀ : Upd s s₀ .t0 (s.syms p224Sym) := hs₀ ▸ Upd.write _ _ _
  have b₀ : s₀.gpr .a0 = base := by rw [u₀.other _ (by decide), hb]
  refine sd_a0 b₀ (by rw [u₀.wr]; exact hwr') hal (d := 1504) (by decide) (by decide) fun s₁ u₁ => ?_
  refine sd_a0 (by rw [u₁.gpr]; exact b₀) (by rw [u₁.wr, u₀.wr]; exact hwr') hal (d := 1512) (by decide)
    (by decide) fun s₂ u₂ => ?_
  refine sd_a0 (by rw [u₂.gpr, u₁.gpr]; exact b₀) (by rw [u₂.wr, u₁.wr, u₀.wr]; exact hwr') hal (d := 1520)
    (by decide) (by decide) fun s₃ u₃ => ?_
  refine sd_a0 (by rw [u₃.gpr, u₂.gpr, u₁.gpr]; exact b₀) (by rw [u₃.wr, u₂.wr, u₁.wr, u₀.wr]; exact hwr') hal
    (d := 1528) (by decide) (by decide) fun s₄ u₄ => wp_mv fun s₅ u₅ => wp_mv fun s₆ u₆ => WP.block_nil ?_
  have g₄ : ∀ r, s₄.gpr r = s₀.gpr r := fun r => by rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]
  have g₆ : ∀ r, r ≠ .s0 → r ≠ .s4 → s₆.gpr r = s₀.gpr r := fun r h0 h2 => by
    rw [u₆.other r h2, u₅.other r h0, g₄]
  have hw₆ : WsReg s₆ base := ⟨by rw [u₆.other _ (by decide), u₅.gpr, g₄, b₀],
    by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, u₀.wr]; exact hwr', hfit, hal⟩
  have m₄ : s₄.mem = (((s.mem.writeW (off base 1504) (s.gpr .s0)).writeW (off base 1512) (s.gpr .s1)).writeW
      (off base 1520) (s.gpr .ra)).writeW (off base 1528) (s.gpr .s4) := by
    simp only [u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₃.gpr, u₂.gpr, u₁.gpr, u₀.mem]
    rw [u₀.other _ (by decide), u₀.other _ (by decide), u₀.other _ (by decide), u₀.other _ (by decide)]
  have m₆ : s₆.mem = s₄.mem := by rw [u₆.mem, u₅.mem]
  have O₄ : Unch base savesG s.mem s₆.mem := by
    rw [m₆, m₄]
    exact ((((writeW_outside _ _ _ (by omega_using [])).unch.trans (writeW_outside _ _ _ (by omega_using [])).unch).trans
      (writeW_outside _ _ _ (by omega_using [])).unch).trans (writeW_outside _ _ _ (by omega_using [])).unch)
  have e₆ : ∀ d, d + 32 ≤ 1504 → wordsVal s₆.mem base d 4 = wordsVal s.mem base d 4 := fun d hd =>
    O₄.wordsVal (by simp; omega_using [hd]) (by omega_using [hd])
  have cs : ∀ d, d < 4096 → MC.toPoint.coordAt s.mem base d = wordsVal s.mem base d 4 := fun d hd =>
    coordAt_eq s.mem base (by omega_using [hd])
  have tm : ∀ x, toM W.p (2 ^ 256) (x * 2 ^ (64 * 4) % W.p) = Fin.ofNat W.p x := fun x => toM_mont unit
  have hT₆ : TabOk s₆ base (s.syms p224Sym) :=
    hT₀.of_unch (by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, u₀.rd]) (by decide) O₄
  have hz₆ : wordsVal s₆.mem base 160 4 = 0 := by rw [e₆ 160 (by omega_using []), ← cs 160 (by omega_using [])]; exact hz
  have h1₆ : wordsVal s₆.mem base 224 4 = oneM := by
    rw [e₆ 224 (by omega_using []), ← cs 224 (by omega_using [])]
    refine hone.trans ?_
    simp only [Impl.Weierstrass.Mul.Curve.mont, Nat.one_mul]; rfl
  have ha₆ : wordsVal s₆.mem base 256 4 = W.a * 2 ^ (64 * 4) % W.p := by
    rw [e₆ 256 (by omega_using []), ← cs 256 (by omega_using [])]; exact ha
  have hb₆ : wordsVal s₆.mem base 1344 4 = W.b * 2 ^ (64 * 4) % W.p := by
    rw [e₆ 1344 (by omega_using [])]; exact hbp
  -- The body.
  refine WP.seq (WP.mono (body_ok hL hw₆ (by rw [u₆.gpr, u₅.other _ (by decide), g₄, u₀.gpr]) hT₆ hz₆ h1₆
    (by simp only [tmv]; rw [ha₆]; exact tm _) (by simp only [tmv]; rw [hb₆]; exact tm _)
    (by rw [ha₆]; exact Nat.mod_lt _ (by decide)) (by rw [hb₆]; exact Nat.mod_lt _ (by decide)))
    fun s₇ ⟨K₇, U₇, _, lt₇, R₇⟩ => ?_)
  have hw₇ := hw₆.of_kc K₇
  -- The loads.
  have far : ∀ d ∈ [1504, 1512, 1520, 1528], word s₇.mem base d = word s₄.mem base d := fun d hd => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rw [U₇.word (fun w hw => by
      simp only [bodyW, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> simp only <;> omega_using [hd]) (by omega_using [hd]), m₆]
  have w28 : word s₇.mem base 1528 = s.gpr .s4 := by rw [far 1528 (by simp), m₄, word_writeW_self]
  have w20 : word s₇.mem base 1520 = s.gpr .ra := by
    rw [far 1520 (by simp), m₄, (writeW_outside (d := 1528) _ base _ (by omega_using [])).word (by omega_using []) (by omega_using []),
      word_writeW_self]
  have w12 : word s₇.mem base 1512 = s.gpr .s1 := by
    rw [far 1512 (by simp), m₄, (writeW_outside (d := 1528) _ base _ (by omega_using [])).word (by omega_using []) (by omega_using []),
      (writeW_outside (d := 1520) _ base _ (by omega_using [])).word (by omega_using []) (by omega_using []), word_writeW_self]
  have w04 : word s₇.mem base 1504 = s.gpr .s0 := by
    rw [far 1504 (by simp), m₄, (writeW_outside (d := 1528) _ base _ (by omega_using [])).word (by omega_using []) (by omega_using []),
      (writeW_outside (d := 1520) _ base _ (by omega_using [])).word (by omega_using []) (by omega_using []),
      (writeW_outside (d := 1512) _ base _ (by omega_using [])).word (by omega_using []) (by omega_using []), word_writeW_self]
  refine ld_ws hw₇ (d := 1520) (by decide) (by decide) fun s₈ u₈ => ?_
  refine ld_ws (hw₇.of_kp (Kp.of_upd u₈)) (d := 1528) (by decide) (by decide) fun s₉ u₉ => ?_
  have hw₉ : WsReg s₉ base := ⟨by rw [u₉.other .s0 (by decide), u₈.other .s0 (by decide)]; exact hw₇.s0,
    by rw [u₉.wr, u₈.wr]; exact hw₇.wr, hfit, hal⟩
  refine ld_ws hw₉ (d := 1512) (by decide) (by decide) fun s₁₀ u₁₀ => ?_
  have hw₁₀ : WsReg s₁₀ base := ⟨by rw [u₁₀.other .s0 (by decide)]; exact hw₉.s0,
    by rw [u₁₀.wr]; exact hw₉.wr, hfit, hal⟩
  refine ld_ws hw₁₀ (d := 1504) (by decide) (by decide) fun s₁₁ u₁₁ => WP.block_nil ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · have m₁₀ : s₁₀.mem = s₇.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem]
    by_cases h0 : r = .s0
    · subst h0; rw [u₁₁.gpr, m₁₀, w04]
    by_cases h1 : r = .s1
    · subst h1; rw [u₁₁.other _ (by decide), u₁₀.gpr, u₉.mem, u₈.mem, w12]
    by_cases h2 : r = .s4
    · subst h2; rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr, u₈.mem, w28]
    rw [u₁₁.other _ h0, u₁₀.other _ h1, u₉.other _ h2, u₈.other _ (fun e => by subst e; revert hr; decide),
      K₇.gpr r hr h1, g₆ r h0 h2, u₀.other _ (fun e => by subst e; revert hr; decide)]
  · rw [u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, K₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, u₀.sp]
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, w20]
  · have m₁₁ : s₁₁.mem = s₇.mem := by rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem]
    show MC.ResultInRange _ _ (s.gpr .a0) s.mem s₁₁.mem
    rw [hb, m₁₁]
    refine ⟨fun _ _ => ?_, keepsG_of_unch (O₄.trans U₇)⟩
    have e : MC.scalar base s.mem = wordsVal s₆.mem base 1056 4 := by
      rw [e₆ 1056 (by omega_using [])]; exact cs 1056 (by omega_using [])
    have c7 : ∀ d, d < 4096 → MC.toPoint.coordAt s₇.mem base d = wordsVal s₇.mem base d 4 := fun d hd =>
      coordAt_eq s₇.mem base (by omega_using [hd])
    have x0 : MC.toPoint.coordAt s₇.mem base MC.pAt = wordsVal s₇.mem base 512 4 := c7 512 (by omega_using [])
    have x1 : MC.toPoint.coordAt s₇.mem base (MC.pAt + Impl.Weierstrass.Point.elemBytes MC.toPoint.k) =
        wordsVal s₇.mem base 544 4 := c7 544 (by omega_using [])
    have x2 : MC.toPoint.coordAt s₇.mem base (MC.pAt + 2 * Impl.Weierstrass.Point.elemBytes MC.toPoint.k) =
        wordsVal s₇.mem base 576 4 := c7 576 (by omega_using [])
    rw [e]
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at lt₇
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · show _ < W.p; rw [Impl.Weierstrass.Point.Curve.pointAt, x0]; exact lt₇.1
    · show _ < W.p; rw [Impl.Weierstrass.Point.Curve.pointAt, x1]; exact lt₇.2.1
    · show _ < W.p; rw [Impl.Weierstrass.Point.Curve.pointAt, x2]; exact lt₇.2.2
    · rw [Impl.Weierstrass.Point.Curve.pointAt, x0, x1, x2, dq, dq, dq]
      exact represents_of_rep R₇

/-! ## The table, for the callers -/

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ecdsa.RISCV64.Comb VG.Proof.Mont VG.Impl.Ecdsa.RISCV64
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdh.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.Ecdsa.RISCV64.P224 (W MC unit sv)
open VG.Spec.Weierstrass (Point)
open VG.Proof.Ecdh.RISCV64.P224 (TailConsts tailW tailWith_ok coord_sv point_eq sv_unch sl_eq FL)

/-- The table, as the callers of `vg_p224_mul_g` hold it, for the working
space at `base`. -/
structure TabAt (base : Addr) (s : State) : Prop where
  rd : tabRegion s ∈ s.rd
  held : ∀ i < 18944, s.mem.readW (s.syms p224Sym + BitVec.ofNat 64 (8 * i)) 64 = p224CombWords.getD i 0
  al : (s.syms p224Sym).toNat % 64 = 0
  fit : (s.syms p224Sym).toNat + 151552 ≤ 2 ^ 64
  disj : Region.Disjoint (tabRegion s) ⟨base, 8192⟩

/-- The table survives what changes memory only in the working space. -/
theorem TabAt.of_mem {base : Addr} {s s' : State} (h : TabAt base s) (hsy : s'.syms = s.syms) (hrd : s'.rd = s.rd)
    (hm : ∀ x, 8192 ≤ ofs base x → s'.mem x = s.mem x) : TabAt base s' := by
  obtain hT := tabOk_of_pre h.rd h.held h.al h.fit h.disj
  refine ⟨by rw [hrd, tabRegion, hsy]; exact h.rd, fun i hi => ?_, by rw [hsy]; exact h.al,
    by rw [hsy]; exact h.fit, by rw [tabRegion, hsy]; exact h.disj⟩
  rw [hsy, ← h.held i hi]
  refine Mem.readW_congr fun b hb => hm _ ?_
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact hT.far _ (by omega_using [hi, hb])

theorem TabAt.of_unch {base : Addr} {s s' : State} (h : TabAt base s) (hsy : s'.syms = s.syms) (hrd : s'.rd = s.rd)
    {W' : List (Nat × Nat)} (hW : ∀ w ∈ W', w.1 + w.2 ≤ 8192) (hu : Unch base W' s.mem s'.mem) : TabAt base s' :=
  h.of_mem hsy hrd fun x hx => hu.far fun w hw => by have := hW w hw; omega_using [hx, this]

/-- The table survives what keeps the symbols and changes memory only in
writable regions apart from it. -/
theorem TabAt.of_frame {base : Addr} {s s' : State} (h : TabAt base s) (hsy : s'.syms = s.syms) (hrd : s'.rd = s.rd)
    (hF : Frame s.wr s.mem s'.mem) (hd : ∀ r ∈ s.wr, Region.Disjoint (tabRegion s) r) : TabAt base s' := by
  refine ⟨by rw [hrd, tabRegion, hsy]; exact h.rd, fun i hi => ?_, by rw [hsy]; exact h.al,
    by rw [hsy]; exact h.fit, by rw [tabRegion, hsy]; exact h.disj⟩
  rw [hsy, ← h.held i hi]
  refine Mem.readW_congr fun b hb => hF _ fun r hr hc => hd r hr _ ?_ hc
  simp only [Region.Contains]
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Mem.sub_ofNat_toNat _ (by omega_using [hi, hb])]
  omega_using [hi, hb]

theorem combWords_length : p224CombWords.length = 18944 := by
  rw [combWords_eq]
  exact tcombWords_length comb7_len comb7_lenH

/-- A memory holding the table at `0x100000`, for the witnesses of the
contracts with it (irreducible: unfolding it in a definitional check would
evaluate the table). -/
@[irreducible] def combSatMem : Mem := constMem 0x100000 p224CombWords

theorem combSatMem_held : ∀ i < p224CombWords.length,
    combSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = p224CombWords.getD i 0 := by
  obtain h := constMem_held 0x100000 p224CombWords (by rw [combWords_length]; decide)
  unfold combSatMem
  exact h

/-- The table, as `abi.withConsts p224CombConsts` gives it, for a working space
among the writable regions. -/
theorem tabAt_of_consts {st : Nat} {s : State} {base : Addr} (h : ConstsOk p224CombConsts st s)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) : TabAt base s := by
  have h' : ConstsOk [(p224Sym, p224CombWords)] st s := h
  obtain hr := ConstsOk.rd1 h'
  obtain hw' := ConstsOk.wr1 h' _ hw
  obtain hf := ConstsOk.fit h' List.mem_cons_self
  rw [combWords_length] at hr hw' hf
  exact ⟨hr, fun i hi => ConstsOk.held1 h' i (by rw [combWords_length]; exact hi),
    ConstsOk.aligned h' List.mem_cons_self, hf, hw'⟩

theorem tab_wr_of_consts {st : Nat} {s : State} (h : ConstsOk p224CombConsts st s) :
    ∀ r ∈ s.wr, Region.Disjoint (tabRegion s) r := by
  have h' : ConstsOk [(p224Sym, p224CombWords)] st s := h
  obtain hw' := ConstsOk.wr1 h'
  rw [combWords_length] at hw'
  exact hw'

/-- `tail` with `vg_p224_mul_g`, from `G` in `R`'s first two slots. -/
theorem tailG_ok (hL : Law W) {s : State} {base : Addr} (hw : WsReg s base)
    (h3 : s.gpr .s3 = base) (hc : TailConsts base s) (hx : sv base s RX = W.gx * 2 ^ 256 % W.p)
    (hy : sv base s RY = W.gy * 2 ^ 256 % W.p) (hbp : sv base s BP = W.b * 2 ^ 256 % W.p) (hT : TabAt base s) :
    WP isa (Impl.Ecdh.RISCV64.Cfg.tail p224 mulGP224Name mulGP224) s fun s' =>
      Kc s s' ∧ Unch base tailW s.mem s'.mem ∧
      word s'.mem base FL = word s.mem base FL &&& maskOf (decide (sv base s K < W.n)) &&&
        maskOf (!decide (sv base s K = 0)) ∧
      (1 ≤ sv base s K → sv base s K < W.n →
        Rep W (toM W.p (2 ^ 256) (sv base s' RX)) (toM W.p (2 ^ 256) (sv base s' RY))
          (toM W.p (2 ^ 256) (sv base s' RZ))
          (Spec.Weierstrass.mul (sv base s K) (.affine (toM W.p (2 ^ 256) (sv base s RX))
            (toM W.p (2 ^ 256) (sv base s RY)))) ∧
        sv base s' RX < W.p ∧ sv base s' RY < W.p ∧ sv base s' RZ < W.p) ∧
      sv base s' XO < W.p ∧
      Fin.ofNat W.p (sv base s' XO) =
        toM W.p (2 ^ 256) (sv base s' RX) * toM W.p (2 ^ 256) (sv base s' RZ) ^ (W.p - 2) ∧
      sv base s' ACC < W.p ∧
      toM W.p (2 ^ 256) (sv base s' ACC) = toM W.p (2 ^ 256) (sv base s' RZ) ^ (W.p - 2) := by
  refine tailWith_ok hL hw h3 hc fun s₁ hw₁ h3₁ K₁ U₁ sy₁ => ?_
  obtain hc₁ := hc.of_unch U₁ (by decide)
  obtain e₁ : ∀ i, i < 44 → sv base s₁ i = sv base s i := fun i hi =>
    sv_unch U₁ i (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; rw [sl_eq, FL]; omega_using [hi])
      (by omega_using [hi])
  obtain hT₁ : TabAt base s₁ := hT.of_unch sy₁ K₁.rd (by decide) U₁
  obtain eG : MC.point base s₁.mem = Spec.Weierstrass.G W := by
    rw [point_eq hL]
    show Point.affine (toM _ _ (sv base s₁ RX)) (toM _ _ (sv base s₁ RY)) = _
    rw [e₁ RX (by decide), e₁ RY (by decide), hx, hy]
    exact congrArg₂ Point.affine (toM_mont unit) (toM_mont unit)
  -- The call, with the table its readable region.
  rw [Cfg.wsCall, eG]
  refine WP.seq (WP.seq (WP.cons (exec_addi (by decide)) (WP.block_nil ?_)))
  generalize hs₂ : s₁.write .a0 (s₁.gpr wb + BitVec.ofInt 64 0) = s₂
  obtain u₂ : Upd s₁ s₂ .a0 (s₁.gpr wb + BitVec.ofInt 64 0) := hs₂ ▸ Upd.write _ _ _
  obtain sy₂ : s₂.syms = s₁.syms := by rw [← hs₂]; rfl
  obtain K₂ : Kp s₁ s₂ := Kp.of_upd u₂
  obtain a0₂ : s₂.gpr .a0 = base := by rw [u₂.gpr, hw₁.s0]; simp
  obtain hcov : Covers [⟨base, 8192⟩] s₂.wr := Covers.of_mem fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [K₂.wr]; exact hw₁.wr
  obtain htab : Covers [tabRegion s₂] s₂.rd := Covers.of_mem fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [K₂.rd, tabRegion, sy₂]; exact hT₁.rd
  obtain e0 : (s₂.callEntry.withRegions [tabRegion s₂] [⟨base, 8192⟩]).gpr .a0 = base := by
    simp only [State.withRegions_gpr]; rw [State.callEntry_gpr _ (by decide), a0₂]
  obtain em : (s₂.callEntry.withRegions [tabRegion s₂] [⟨base, 8192⟩]).mem = s₁.mem := by
    simp only [State.withRegions_mem, State.callEntry_mem, u₂.mem]
  refine WP.call (mulG_rv hL) (rd := [tabRegion s₂]) (wr := [⟨base, 8192⟩]) ?_ (Covers.append htab hcov) hcov
    (fun s₃ r₃ w₃ p₃ _ G₃ _ hp => ?_) Impl.Ecdsa.RISCV64.Comb.mulGP224_noFrames
  · refine ⟨rfl, by rw [e0]; rfl, by rw [e0]; exact hw₁.nowrap, by rw [e0]; exact hw₁.al, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e0, em]
      exact ⟨(coord_sv _ _ MP).trans hc₁.mp, (coord_sv _ _ ZERO).trans hc₁.zero,
        (coord_sv _ _ ONEP).trans hc₁.onep, (coord_sv _ _ AP).trans hc₁.ap, (coord_sv _ _ B3P).trans hc₁.b3p⟩
    · rw [e0, em]; exact (e₁ BP (by decide)).trans hbp
    · rw [em]; exact fun i hi => by rw [show (s₂.callEntry.withRegions _ _).syms = s₁.syms from sy₂]; exact hT₁.held i hi
    · exact (show (s₂.callEntry.withRegions [tabRegion s₂] [⟨base, 8192⟩]).syms = s₁.syms from sy₂) ▸ hT₁.al
    · exact (show (s₂.callEntry.withRegions [tabRegion s₂] [⟨base, 8192⟩]).syms = s₁.syms from sy₂) ▸ hT₁.fit
    · rw [e0]
      simp only [tabRegion]
      rw [show (s₂.callEntry.withRegions [tabRegion s₂] [⟨base, 8192⟩]).syms = s₁.syms from sy₂]
      exact hT₁.disj
  -- `s0` from `s3`.
  refine wp_mv fun s₄ u₄ => WP.block_nil ⟨⟨fun r hr => ?_, by rw [u₄.rd, r₃, K₂.rd], by rw [u₄.wr, w₃, K₂.wr],
    by rw [u₄.sp, p₃, K₂.sp]⟩, ?_⟩
  · by_cases h : r = .s0
    · subst h; rw [u₄.gpr, G₃ _ (by decide), K₂.gpr _ (by decide), h3₁, hw₁.s0]
    · rw [u₄.other _ h, G₃ _ hr, K₂.gpr _ hr]
  · have := hp
    simp only [mulGRVc, State.withRegions_mem] at this
    rw [e0] at this
    rw [show s₂.callEntry.mem = s₁.mem by rw [State.callEntry_mem, u₂.mem]] at this
    rw [u₄.mem]
    exact this

end VG.Proof.Ecdsa.RISCV64.P224.Comb
