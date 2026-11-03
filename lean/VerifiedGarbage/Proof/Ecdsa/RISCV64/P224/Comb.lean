module

public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Comb.Main
public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Comb.P224
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P224.MulFn
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.P224.Comb7
import VerifiedGarbage.Proof.P224.Point
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes

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
  have hC := VG.Proof.P224.combOk7 hL
  have hv := combWin_lt 7 k i
  unfold signedPtW yDig
  generalize combWin 7 k i = v at hv ⊢
  simp only [show 2 ^ (7 - 1) = 64 from rfl]
  by_cases h64 : 64 ≤ v
  · have hmg : magH 64 v = v - 64 := by unfold magH; simp [h64]
    simp only [h64, ↓reduceIte, show ¬ v < 64 by omega, hmg]
    by_cases h0 : v - 64 = 0
    · simp only [h0, ↓reduceIte, toM_zero, combPtW, Nat.zero_mul, mul_zero_pt]
      rw [toM_one unit]; exact rep_infinity' hL
    · obtain ⟨m, hm⟩ : ∃ m, v - 64 = m + 1 := ⟨v - 64 - 1, by omega⟩
      simp only [hm, Nat.add_one_ne_zero, ↓reduceIte, combPtW, Nat.add_sub_cancel]
      rw [hC.entry i hi m (by simp; omega), toM_montP, toM_montP, toM_one unit]
      exact rep_affine' hL _ _
  · have hmg : magH 64 v = 64 - v := by unfold magH; simp [h64]
    obtain ⟨m, hm⟩ : ∃ m, 64 - v = m + 1 := ⟨64 - v - 1, by omega⟩
    simp only [h64, ↓reduceIte, show v < 64 by omega, hmg, hm, Nat.add_one_ne_zero, combPtW, Nat.add_sub_cancel]
    rw [hC.entry i hi m (by simp; omega), toM_montP, toM_one unit,
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
  have hw₁ := hw.of_kp K₁.kp
  have U₁ : Unch base [(992, 32), (3840, 256)] s.mem s₁.mem := fun x hx => K₁.mem x hx
  rw [List.cons_append, List.nil_append]
  refine ld_ws hw₁ (d := 1024) (by decide) (by decide) fun s₂ u₂ => ?_
  have a7 : s₂.gpr .a7 = maskOf c := by
    rw [u₂.gpr, U₁.word (by simp) (by omega), hPT]
  have hw₂ := hw₁.of_rest (u₂.rest (ws := [.a7]) (by decide))
  refine WP.mono (sel_ok c 4 hw₂ a7 (o := 640) (a := 640) (b := 992) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)) fun s₃ ⟨e₃, r₃, O₃⟩ => ⟨?_, ?_, ?_⟩
  · have hacc : wordsVal s₂.mem base 992 4 = (0 + W.p - wordsVal s.mem base 640 4) % W.p := by
      rw [u₂.mem]
      have : wordsVal s₁.mem base 992 4 =
          (wordsVal s.mem base 160 4 + W.p - wordsVal s.mem base 640 4) % W.p := v₁
      rw [hZ] at this
      exact this
    have hy : wordsVal s₂.mem base 640 4 = wordsVal s.mem base 640 4 := by
      rw [u₂.mem]; exact U₁.wordsVal (by simp) (by omega)
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
  have hI : Inv 4 base W.p (· ∈ combSl) addV (fun x => tmv W 4 base s x) s :=
    ⟨hw, by decide, hlt, fun _ _ => rfl⟩
  refine WP.seq (WP.mono (rcb3_ok (M := p224.MP') (F := p224Field) field_ok rfl combLay
    (fun x hx => by have := (by decide : ∀ x ∈ combSl, x < 4095) x hx; exact this) unit
    (S := p224.rcb3Slots) (p := p224.pt RX RY RZ) (q := p224.pt DX DY DZ) (o := p224.pt TX TY TZ)
    ⟨by decide, by decide⟩ (by decide) hI (by decide)) fun s₁ ⟨K₁, I₁, v₁⟩ => ?_)
  have hw₁ := hw.of_kp K₁.kp
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (copy_ok 4 hw₁ (o := 512) (a := 704) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₂ ⟨e₂, r₂, O₂⟩ => ?_)
  have hw₂ := hw₁.of_rest r₂
  refine WP.block_append (WP.mono (copy_ok 4 hw₂ (o := 544) (a := 736) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₃ ⟨e₃, r₃, O₃⟩ => ?_)
  have hw₃ := hw₂.of_rest r₃
  refine WP.mono (copy_ok 4 hw₃ (o := 576) (a := 768) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₄ ⟨e₄, r₄, O₄⟩ => ?_
  have tx : wordsVal s₄.mem base 512 4 = wordsVal s₁.mem base 704 4 := by
    rw [O₄.wordsVal (by omega) (by omega), O₃.wordsVal (by omega) (by omega), e₂]
  have ty : wordsVal s₄.mem base 544 4 = wordsVal s₁.mem base 736 4 := by
    rw [O₄.wordsVal (by omega) (by omega), e₃, O₂.wordsVal (by omega) (by omega)]
  have tz : wordsVal s₄.mem base 576 4 = wordsVal s₁.mem base 768 4 := by
    rw [e₄, O₃.wordsVal (by omega) (by omega), O₂.wordsVal (by omega) (by omega)]
  have hT : ∀ x ∈ [704, 736, 768], x ∈ [(p224.pt TX TY TZ).x, (p224.pt TX TY TZ).y, (p224.pt TX TY TZ).z] ++ addV := by
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
    have h704 : toM W.p (2 ^ (64 * 4)) (wordsVal s₁.mem base 704 4) = _ := I₁.val 704 (hT 704 (by simp))
    have h736 : toM W.p (2 ^ (64 * 4)) (wordsVal s₁.mem base 736 4) = _ := I₁.val 736 (hT 736 (by simp))
    have h768 : toM W.p (2 ^ (64 * 4)) (wordsVal s₁.mem base 768 4) = _ := I₁.val 768 (hT 768 (by simp))
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
  have uS : ∀ d, d + 32 ≤ 512 ∨ 1056 ≤ d → d + 32 ≤ 3840 →
      wordsVal s.mem base d 4 = wordsVal s₀.mem base d 4 := fun d h h' =>
    hI.unch.wordsVal (by simp; omega) (by omega)
  have hk : kOf s.mem base = kOf s₀.mem base := uS 1536 (by omega) (by omega)
  rw [Cfg.step]
  -- `s1 -= 1` and the entry.
  refine WP.seq (wp_decCounter hj1 hI.ctr fun s₁ u₁ => ?_)
  have hw₁ := hI.ws.of_kc (Kc.of_rest (u₁.rest (ws := [.s1]) (by decide)))
  refine WP.mono (select_ok hw₁ (j := j - 1) (by omega) u₁.gpr
    (by rw [u₁.other _ (by decide), hI.keep.gpr _ (by decide) (by decide), hP.s4])
    (hI.tab.of_mem u₁.rd fun x _ => by rw [u₁.mem])
    (by rw [u₁.mem, hI.unch.word (by simp) (by omega), hP.kz])
    (by rw [u₁.mem, uS 160 (by omega) (by omega), hP.zero])) fun s₂ ⟨dx₂, dy₂, dz₂, pt₂, U₂, r₂⟩ => ?_
  rw [u₁.mem, hk] at dx₂ dy₂ dz₂ pt₂
  rw [u₁.mem] at U₂
  rw [uS 224 (by omega) (by omega), hP.one] at dy₂ dz₂
  have hw₂ := hw₁.of_rest r₂
  generalize hv : combWin 7 (kOf s₀.mem base) (j - 1) = v at dx₂ dy₂ dz₂ pt₂
  have hv128 : v < 128 := hv ▸ combWin_lt 7 _ _
  -- What the slots hold so far.
  have uS₂ : ∀ d, d + 32 ≤ 512 ∨ 1056 ≤ d → d + 32 ≤ 3840 →
      wordsVal s₂.mem base d 4 = wordsVal s₀.mem base d 4 := fun d h h' => by
    rw [U₂.wordsVal (by simp; omega) (by omega), uS d h h']
  have hR₂ : ∀ d ∈ [512, 544, 576], wordsVal s₂.mem base d 4 = wordsVal s.mem base d 4 := by
    intro d hd; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;> exact U₂.wordsVal (by simp) (by omega)
  have hlt1 : oneM < W.p := Nat.mod_lt _ (by decide)
  have hlty : yDig (j - 1) v < W.p := by
    unfold yDig; split
    · exact hlt1
    · exact Nat.mod_lt _ (by decide)
  -- The negation.
  refine WP.seq (WP.mono (negate_ok hw₂ (by rw [uS₂ 160 (by omega) (by omega), hP.zero])
    (by rw [dy₂]; exact hlty) pt₂) fun s₃ ⟨dy₃, U₃, K₃⟩ => ?_)
  rw [dy₂] at dy₃
  have hw₃ := hw₂.of_kp K₃
  have e₃ : ∀ d, (d + 32 ≤ 640 ∨ 672 ≤ d) → (d + 32 ≤ 992 ∨ 1024 ≤ d) → d + 32 ≤ 3840 →
      wordsVal s₃.mem base d 4 = wordsVal s₂.mem base d 4 := fun d h1 h2 h3 =>
    U₃.wordsVal (by simp; omega) (by omega)
  -- The addition.
  have hlt₃ : ∀ x ∈ addV, wordsVal s₃.mem base x 4 < W.p := by
    intro x hx
    simp only [addV, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [e₃ _ (by omega) (by omega) (by omega), uS₂ _ (by omega) (by omega)]; exact hP.alt
    · rw [e₃ _ (by omega) (by omega) (by omega), uS₂ _ (by omega) (by omega)]; exact hP.blt
    · rw [e₃ _ (by omega) (by omega) (by omega), hR₂ 512 (by simp)]; exact hI.lt 512 (by simp)
    · rw [e₃ _ (by omega) (by omega) (by omega), hR₂ 544 (by simp)]; exact hI.lt 544 (by simp)
    · rw [e₃ _ (by omega) (by omega) (by omega), hR₂ 576 (by simp)]; exact hI.lt 576 (by simp)
    · rw [e₃ _ (by omega) (by omega) (by omega), dx₂]; split
      · decide
      · exact Nat.mod_lt _ (by decide)
    · rw [dy₃]; split
      · exact Nat.mod_lt _ (by decide)
      · exact hlty
    · rw [e₃ _ (by omega) (by omega) (by omega), dz₂]; split
      · decide
      · exact hlt1
  refine WP.mono (addR_ok hw₃ hlt₃) fun s₄ ⟨K₄, U₄, lt₄, v₄⟩ => ?_
  -- The invariant.
  have hU : Unch base stepW s₀.mem s₄.mem :=
    (((hI.unch.trans U₂).trans U₃).trans U₄).cover (by decide)
  refine ⟨hw₃.of_kp K₄, ?_, ?_, hU, ?_, lt₄, ?_⟩
  · rw [K₄.gpr _ (by decide), K₃.gpr _ (by decide), r₂.gpr _ (by decide), u₁.gpr]
  · exact ((hI.keep.trans (Kc.of_rest (u₁.rest (ws := [.s1]) (by decide)))).trans
      (Kc.of_rest r₂)).trans (K₃.kc.trans K₄.kc)
  · exact (hI.tab.of_unch (by rw [K₄.rd, K₃.rd, r₂.rd, u₁.rd]) (W := [(608, 96), (1024, 16)] ++
      [(992, 32), (3840, 256), (640, 32)] ++ [(512, 512), (3840, 256)]) (by decide)
      ((U₂.trans U₃).trans U₄))
  · -- `T = R + D`, with `D` the signed entry.
    have eb : tmv W 4 base s₃ 1344 = Fin.ofNat W.p W.b := by
      simp only [tmv]; rw [e₃ _ (by omega) (by omega) (by omega), uS₂ _ (by omega) (by omega)]; exact hP.b
    have eR : ∀ d ∈ [512, 544, 576], tmv W 4 base s₃ d = tmv W 4 base s d := by
      intro d hd
      simp only [tmv]
      have := hR₂ d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rw [e₃ d (by omega) (by omega) (by omega), this]
    have hD := entry_rep hL (k := kOf s₀.mem base) (i := j - 1) (by omega)
    rw [hv] at hD
    have ex : tmv W 4 base s₃ 608 = toM W.p (2 ^ 256) (if magH 64 v = 0 then 0
        else montP (entOf (j - 1) (magH 64 v - 1)).1) := by
      simp only [tmv]; rw [e₃ _ (by omega) (by omega) (by omega), dx₂]
    have ey : tmv W 4 base s₃ 640 = toM W.p (2 ^ 256) (if v < 64 then (0 + W.p - yDig (j - 1) v) % W.p
        else yDig (j - 1) v) := by
      simp only [tmv]; rw [dy₃]; simp only [decide_eq_true_eq, yDig]
    have ez : tmv W 4 base s₃ 672 = toM W.p (2 ^ 256) (if magH 64 v = 0 then 0 else oneM) := by
      simp only [tmv]; rw [e₃ _ (by omega) (by omega) (by omega), dz₂]
    rw [eb, eR 512 (by simp), eR 544 (by simp), eR 576 (by simp), ex, ey, ez] at v₄
    have hS := hL.add3 am3 (hL.onCurve_mul VG.Proof.P224.onCurve_G _) (signed_onCurve hL (kOf s₀.mem base) (j - 1))
      hI.rep hD v₄.symm
    have hadd := combW_add hL VG.Proof.P224.onCurve_G (w := 7) (k := kOf s₀.mem base) (J := 37) (j := j - 1) (by omega)
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
  have hC := VG.Proof.P224.combOk7 hL
  rw [Cfg.body]
  simp only [List.append_assoc]
  -- The copy of `k`, and its zero word.
  refine WP.seq ?_
  refine WP.block_append (WP.mono (copy_ok 4 hw (o := 1536) (a := 1056) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₁ ⟨e₁, r₁, O₁⟩ => ?_)
  have hw₁ := hw.of_rest r₁
  rw [VG.Proof.Weierstrass.RISCV64.sdAt_lo (by decide)]
  simp only [List.cons_append, List.nil_append]
  refine wp_li (imm := 0) (by decide) fun s₂ u₂ => ?_
  have hw₂ := hw₁.of_rest (u₂.rest (ws := [.t0]) (by decide))
  refine sd_ws hw₂ (d := 1568) (by decide) (by decide) fun s₃ u₃ => ?_
  have hw₃ := hw₂.of_rest (u₃.rest [])
  have O₃ : Outside base 1568 8 s₂.mem s₃.mem := by rw [u₃.mem]; exact writeW_outside _ _ _ (by omega)
  -- `R = S`.
  refine WP.block_append (WP.mono (setConst_ok 4 hw₃ (o := 512) (x := VG.Impl.Ecdh.RISCV64.Cfg.mont p224
    Impl.P224.p224Comb7Start.1) (by decide) (by decide)) fun s₄ ⟨r₄, O₄, e₄⟩ => ?_)
  have hw₄ := hw₃.of_rest r₄
  refine WP.block_append (WP.mono (setConst_ok 4 hw₄ (o := 544) (x := VG.Impl.Ecdh.RISCV64.Cfg.mont p224
    Impl.P224.p224Comb7Start.2) (by decide) (by decide)) fun s₅ ⟨r₅, O₅, e₅⟩ => ?_)
  have hw₅ := hw₄.of_rest r₅
  refine WP.block_append (WP.mono (copy_ok 4 hw₅ (o := 576) (a := 224) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₆ ⟨e₆, r₆, O₆⟩ => ?_)
  have hw₆ := hw₅.of_rest r₆
  refine wp_li (imm := 37) (by decide) fun s₇ u₇ => WP.block_nil ?_
  have r₇ : Rest [.t0, .t1] s s₆ :=
    ((r₁.mono (by decide)).trans ((u₂.rest (ws := [.t0, .t1]) (by decide)).trans (u₃.rest _))).trans
      ((r₄.trans r₅).trans (r₆.mono (by decide)))
  have hw₇ : WsReg s₇ base := hw₆.of_kc (Kc.of_rest (u₇.rest (ws := [.s1]) (by decide)))
  have U₆ : Unch base [(1536, 32), (1568, 8), (512, 32), (544, 32), (576, 32)] s.mem s₆.mem := by
    have O₃' : Outside base 1568 8 s₁.mem s₃.mem := by rw [← u₂.mem]; exact O₃
    exact (((O₁.unch.trans O₃'.unch).trans O₄.unch).trans O₅.unch).trans O₆.unch
  have U₇ : Unch base [(1536, 32), (1568, 8), (512, 32), (544, 32), (576, 32)] s.mem s₇.mem := by
    rw [u₇.mem]; exact U₆
  have e7 : ∀ d, (d + 32 ≤ 512 ∨ 608 ≤ d) → (d + 32 ≤ 1536 ∨ 1576 ≤ d) → d + 32 ≤ 3840 →
      wordsVal s₇.mem base d 4 = wordsVal s.mem base d 4 := fun d h1 h2 h3 =>
    U₇.wordsVal (by simp; omega) (by omega)
  -- The loop's start.
  have hP : CombPre base T s₇ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₇.other _ (by decide), r₇.gpr _ (by decide), h2]
    · show word s₇.mem base 1568 = 0
      rw [u₇.mem, O₆.word (by omega) (by omega), O₅.word (by omega) (by omega), O₄.word (by omega) (by omega),
        u₃.mem, word_writeW_self, u₂.gpr]; rfl
    · rw [e7 160 (by omega) (by omega) (by omega)]; exact hz
    · rw [e7 224 (by omega) (by omega) (by omega)]; exact hone
    · simp only [tmv]; rw [e7 256 (by omega) (by omega) (by omega)]; exact ha
    · simp only [tmv]; rw [e7 1344 (by omega) (by omega) (by omega)]; exact hb
    · rw [e7 256 (by omega) (by omega) (by omega)]; exact hap
    · rw [e7 1344 (by omega) (by omega) (by omega)]; exact hbp
  have hk : kOf s₇.mem base = wordsVal s.mem base 1056 4 := by
    show wordsVal s₇.mem base 1536 4 = _
    rw [u₇.mem, O₆.wordsVal (by omega) (by omega), O₅.wordsVal (by omega) (by omega),
      O₄.wordsVal (by omega) (by omega), O₃.wordsVal (by omega) (by omega), u₂.mem, e₁]
  have hT₇ : TabOk s₇ base T := hT.of_unch (by rw [u₇.rd, r₆.rd, r₅.rd, r₄.rd, u₃.rd, u₂.rd, r₁.rd])
    (by decide) U₇
  have ex : wordsVal s₇.mem base 512 4 = montP Impl.P224.p224Comb7Start.1 := by
    rw [u₇.mem, O₆.wordsVal (by omega) (by omega), O₅.wordsVal (by omega) (by omega), e₄]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))
  have ey : wordsVal s₇.mem base 544 4 = montP Impl.P224.p224Comb7Start.2 := by
    rw [u₇.mem, O₆.wordsVal (by omega) (by omega), e₅]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))
  have ez : wordsVal s₇.mem base 576 4 = oneM := by
    rw [u₇.mem, e₆, O₅.wordsVal (by omega) (by omega), O₄.wordsVal (by omega) (by omega),
      O₃.wordsVal (by omega) (by omega), u₂.mem, O₁.wordsVal (by omega) (by omega)]; exact hone
  have hI : CombInv base T s₇ s₇ 37 := by
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
  rw [hk, combEW_zero (by have := wordsVal_lt s.mem base 1056 4; omega)] at hr
  exact hr

end

end VG.Proof.Ecdsa.RISCV64.P224.Comb
