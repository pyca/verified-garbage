module

-- separate module: its proofs (about 7 s) cost more than its imports, and its importer's
-- changes need not re-check them

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Verify
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Comb.Main
public import VerifiedGarbage.Proof.Weierstrass.Joint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.P256.Point
import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder

/-!
# ECDSA verification on RISC-V: the joint ladder

`joint` (`Impl/Ecdsa/RISCV64/Verify.lean`) leaves in `R` a representative of
`[u]G + [v]Q` (`joint_ok`):

* `copyTo_ok`, `storePt_ok`: a point's slots to an entry of the table, through
  `a6 = s0 + JT`;
* `build_ok`: the table (`JTab`: entry `4 a + b` represents `[a]G + [b]Q`);
* `window_ok`, `select_ok`: the window's entry number `4 u_j + v_j`, its
  masks, and the entry to `E`, by the comb's tree (`tree_ok`);
* `step_ok`: `R = 4 R + E`, from `[u >>> 2 (j + 1)]G + [v >>> 2 (j + 1)]Q` to
  `[u >>> 2 j]G + [v >>> 2 j]Q` (`jstep`);
* `joint_ok`: the table, `R = O`, and the 128 steps.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.Joint

open VG VG.RISCV64 VG.RISCV64.Steps VG.Proof.Mont VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdsa.RISCV64.Verify
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdh.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.Ecdsa.RISCV64.P256 (W field_ok unit)
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Point mul onCurve)

/-! ## The table's stores -/

/-- `[a6 + o] = [s0 + a]`, through `t0`, for `a6 = s0 + JT`. -/
theorem copyTo_ok : ∀ (k : Nat) {s : State} {base : Addr} {o a : Nat},
    WsReg s base → s.gpr .a6 = base + BitVec.ofNat 64 2048 → o % 8 = 0 → a % 8 = 0 →
    o + 8 * k ≤ 2048 → a + 8 * k ≤ 2048 →
    WP isa (.block (Cfg.copyTo k o a)) s fun s' =>
      wordsVal s'.mem base (2048 + o) k = wordsVal s.mem base a k ∧ Rest [.t0] s s' ∧
      Outside base (2048 + o) (8 * k) s.mem s'.mem
  | 0, _, _, _, _, _, _, _, _, _, _ => WP.block_nil ⟨rfl, Rest.refl _ _, Outside.refl _ _ _ _⟩
  | k + 1, s, base, o, a, hw, h6, ho8, ha8, ho, ha => by
    have hn := hw.nowrap
    have hal := hw.al
    rw [Cfg.copyTo, List.cons_append, List.cons_append, List.nil_append]
    refine ld_ws hw (by omega) ha8 fun s₁ u₁ => ?_
    have K₁ := u₁.rest (ws := [.t0]) (by decide)
    have hw₁ := hw.of_rest K₁
    refine wp_sd (a := off base (2048 + o)) (by omega)
      (by rw [u₁.other _ (by decide), h6, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat])
      (by simp only [off]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
      ⟨_, hw₁.wr, Offset.contains_base base (by omega) (by omega)⟩ fun s₂ u₂ => ?_
    have K₂ : Rest [.t0] s s₂ := K₁.trans ((u₂.rest []).mono (by simp))
    have O₂ : Outside base (2048 + o) 8 s.mem s₂.mem := by
      rw [u₂.mem, u₁.mem]; exact writeW_outside _ _ _ (by omega)
    refine WP.mono (copyTo_ok k (hw.of_rest K₂) (o := o + 8) (a := a + 8)
      (by rw [K₂.gpr _ (by decide), h6]) (by omega) (by omega) (by omega) (by omega))
      fun s₃ ⟨e₃, K₃, O₃⟩ => ⟨?_, K₂.trans K₃,
        (O₂.mono (Nat.le_refl _) (by omega)).trans (O₃.mono (by omega) (by omega))⟩
    rw [show 2048 + (o + 8) = 2048 + o + 8 by omega] at e₃ O₃
    rw [wordsVal, wordsVal, O₃.word (by omega) (by omega), e₃, u₂.mem, u₁.mem, u₁.gpr,
      word_writeW_self]
    rw [(writeW_outside s.mem base (d := 2048 + o) (word s.mem base a) (by omega)).wordsVal (d := a + 8) (k := k)
      (by omega) (by omega)]

/-- Entry `e` of the table from the point `p` in slots below byte 2048. -/
theorem storePt_ok {s : State} {base : Addr} (hw : WsReg s base) {e : Nat} (he : e < 16) {p : Pt}
    (hx : p.x % 8 = 0 ∧ p.x + 32 ≤ 2048) (hy : p.y % 8 = 0 ∧ p.y + 32 ≤ 2048)
    (hz : p.z % 8 = 0 ∧ p.z + 32 ≤ 2048) :
    WP isa (.block (Cfg.storePt p256 e p)) s fun s' =>
      wordsVal s'.mem base (2048 + 96 * e) 4 = wordsVal s.mem base p.x 4 ∧
      wordsVal s'.mem base (2048 + 96 * e + 32) 4 = wordsVal s.mem base p.y 4 ∧
      wordsVal s'.mem base (2048 + 96 * e + 64) 4 = wordsVal s.mem base p.z 4 ∧
      Rest [.t0, .a6] s s' ∧ Outside base (2048 + 96 * e) 96 s.mem s'.mem := by
  have hn := hw.nowrap
  have hjb : Cfg.jb p256 = 96 := rfl
  rw [Cfg.storePt, hjb, show p256.n = 4 from rfl]
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_addi (by decide) fun s₁ u₁ => wp_addi (by decide) fun s₂ u₂ => ?_
  have r₂ : Rest [.t0, .a6] s s₂ := (u₁.rest (by decide)).trans (u₂.rest (by decide))
  have hw₂ := hw.of_rest r₂
  have h6 : s₂.gpr .a6 = base + BitVec.ofNat 64 2048 := by
    rw [u₂.gpr, u₁.gpr, hw.s0, BitVec.add_assoc]; rfl
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine WP.block_append (WP.mono (copyTo_ok 4 hw₂ (o := 96 * e) (a := p.x) h6 (by omega) hx.1 (by omega)
    (by omega)) fun s₃ ⟨e₃, r₃, O₃⟩ => ?_)
  have hw₃ := hw₂.of_rest r₃
  refine WP.block_append (WP.mono (copyTo_ok 4 hw₃ (o := 96 * e + 32) (a := p.y)
    (by rw [r₃.gpr _ (by decide), h6]) (by omega) hy.1 (by omega) (by omega)) fun s₄ ⟨e₄, r₄, O₄⟩ => ?_)
  have hw₄ := hw₃.of_rest r₄
  refine WP.mono (copyTo_ok 4 hw₄ (o := 96 * e + 64) (a := p.z)
    (by rw [r₄.gpr _ (by decide), r₃.gpr _ (by decide), h6]) (by omega) hz.1 (by omega) (by omega))
    fun s₅ ⟨e₅, r₅, O₅⟩ => ⟨?_, ?_, ?_, r₂.trans ((r₃.trans (r₄.trans r₅)).mono (by simp)), ?_⟩
  · rw [O₅.wordsVal (by omega) (by omega), O₄.wordsVal (by omega) (by omega), e₃, m₂]
  · rw [show 2048 + 96 * e + 32 = 2048 + (96 * e + 32) by omega, O₅.wordsVal (by omega) (by omega), e₄,
      O₃.wordsVal (by omega) (by omega), m₂]
  · rw [show 2048 + 96 * e + 64 = 2048 + (96 * e + 64) by omega, e₅, O₄.wordsVal (by omega) (by omega),
      O₃.wordsVal (by omega) (by omega), m₂]
  · rw [← m₂]
    exact ((O₃.mono (by omega) (by omega)).trans (O₄.mono (by omega) (by omega))).trans
      (O₅.mono (by omega) (by omega))

/-! ## The points -/

section
variable {C : Spec.Weierstrass.Curve}

/-- Entry `4 a + b`: `[a]G + [b]Q`. -/
def ent (G Q : Point C) (a b : Nat) : Point C := Spec.Weierstrass.add (mul a G) (mul b Q)

/-- `R` before window `j - 1`: `[u >>> 2 j]G + [v >>> 2 j]Q`. -/
def jp (G Q : Point C) (u v j : Nat) : Point C := ent G Q (u >>> (2 * j)) (v >>> (2 * j))

theorem ent_curve (hL : Law C) {G Q : Point C} (hG : onCurve C G = true) (hQ : onCurve C Q = true)
    (a b : Nat) : onCurve C (ent G Q a b) = true :=
  hL.onCurve_add (hL.onCurve_mul hG _) (hL.onCurve_mul hQ _)

theorem shr_two (u j : Nat) : u >>> (2 * j) = 4 * (u >>> (2 * (j + 1))) + (u >>> (2 * j)) % 4 := by
  rw [show 2 * (j + 1) = 2 * j + 2 by omega, Nat.shiftRight_add, Nat.shiftRight_eq_div_pow (u >>> (2 * j)) 2]
  omega

/-- A step: `4 R + E`, for `R` before the window and `E` its entry, is `R`
after it. -/
theorem jstep (hL : Law C) {G Q : Point C} (hG : onCurve C G = true) (hQ : onCurve C Q = true) (u v j : Nat) :
    Spec.Weierstrass.add
      (Spec.Weierstrass.add (Spec.Weierstrass.add (jp G Q u v (j + 1)) (jp G Q u v (j + 1)))
        (Spec.Weierstrass.add (jp G Q u v (j + 1)) (jp G Q u v (j + 1))))
      (ent G Q ((u >>> (2 * j)) % 4) ((v >>> (2 * j)) % 4)) = jp G Q u v j := by
  have eu := shr_two u j
  have ev := shr_two v j
  generalize (u >>> (2 * j)) % 4 = a at eu ⊢
  generalize (v >>> (2 * j)) % 4 = b at ev ⊢
  rw [show jp G Q u v j = ent G Q (u >>> (2 * j)) (v >>> (2 * j)) from rfl, eu, ev]
  simp only [jp]
  generalize u >>> (2 * (j + 1)) = m
  generalize v >>> (2 * (j + 1)) = n
  have hX := ent_curve hL hG hQ m n
  have hE := ent_curve hL hG hQ a b
  have h2 := hL.onCurve_add hX hX
  have h4 := hL.onCurve_add h2 h2
  obtain ⟨M, _, f, hf⟩ := hL.group
  apply hf.inj (hL.onCurve_add h4 hE) (ent_curve hL hG hQ _ _)
  simp only [ent] at *
  rw [hf.add h4 hE, hf.add h2 h2, hf.add hX hX, hf.add (hL.onCurve_mul hG _) (hL.onCurve_mul hQ _),
    hf.add (hL.onCurve_mul hG _) (hL.onCurve_mul hQ _), hf.add (hL.onCurve_mul hG _) (hL.onCurve_mul hQ _),
    hf.mul hG, hf.mul hQ, hf.mul hG, hf.mul hQ, hf.mul hG, hf.mul hQ]
  have hu : ((4 * m + a : Nat) : Int) = m + m + m + m + a := by omega
  have hv : ((4 * n + b : Nat) : Int) = n + n + n + n + b := by omega
  rw [hu, hv]
  simp only [Lean.Grind.IntModule.add_zsmul]
  grind

/-- After the last window: `[u]G + [v]Q`. -/
theorem jp_zero (G Q : Point C) (u v : Nat) : jp G Q u v 0 = Spec.Weierstrass.add (mul u G) (mul v Q) := by
  simp only [jp, ent, Nat.mul_zero, Nat.shiftRight_zero]

/-- Before the first: `O`. -/
theorem jp_top (G Q : Point C) {u v : Nat} (hu : u < 2 ^ 256) (hv : v < 2 ^ 256) :
    jp G Q u v 128 = .infinity := by
  have h0 : ∀ (k : Nat) (X : Point C), k < 2 ^ 256 → mul (k >>> (2 * 128)) X = .infinity := fun k X hk => by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (by simpa using hk), Spec.Weierstrass.mul]; rfl
  simp only [jp, ent, h0 u G hu, h0 v Q hv]
  rfl

end

/-! ## The complete additions -/

/-- A point in the slots `p`: its coordinates below `p`, representing `P`. -/
structure PtOk (base : Addr) (s : State) (p : Pt) (P : Point W) : Prop where
  rep : Rep W (tmv W 4 base s p.x) (tmv W 4 base s p.y) (tmv W 4 base s p.z) P
  x : wordsVal s.mem base p.x 4 < W.p
  y : wordsVal s.mem base p.y 4 < W.p
  z : wordsVal s.mem base p.z 4 < W.p

/-- The slots of the joint ladder's additions. -/
abbrev jSl : List Nat :=
  [p256.sl AP, p256.sl B3P, p256.sl T0, p256.sl T1, p256.sl T2, p256.sl T3, p256.sl T4, p256.sl T5,
    p256.sl RX, p256.sl RY, p256.sl RZ, p256.sl DX, p256.sl DY, p256.sl DZ, p256.sl TX, p256.sl TY, p256.sl TZ,
    p256.sl GX, p256.sl GY, p256.sl ONEP, p256.sl CPX, p256.sl CPY,
    p256.sl G2X, p256.sl G2Y, p256.sl G2Z, p256.sl G3X, p256.sl G3Y, p256.sl G3Z,
    p256.sl Q2X, p256.sl Q2Y, p256.sl Q2Z, p256.sl Q3X, p256.sl Q3Y, p256.sl Q3Z,
    p256.sl EX, p256.sl EY, p256.sl EZ]

theorem jLay : Lay p256.MP' (own 4) (· ∈ jSl) :=
  ⟨by decide, fun x y hx hy => (by decide : ∀ x ∈ jSl, ∀ y ∈ jSl, x ≠ y → x + 8 * 4 ≤ y ∨ y + 8 * 4 ≤ x)
    x hx y hy, by decide, by decide⟩

theorem jShort : Short (· ∈ jSl) := by decide

/-- What the additions write. -/
abbrev addW (o : Pt) : List (Nat × Nat) :=
  (rcbW p256.rcbSlots o).map (fun w => (w, 8 * 4)) ++ [(own 4, 64 * 4)]

/-- `o = p + q` by the complete addition, for points in slots of `jSl`. -/
theorem addPt_ok (hL : Law W) {base : Addr} {s : State} (hw : WsReg s base)
    (hap : wordsVal s.mem base (p256.sl AP) 4 = W.a * 2 ^ 256 % W.p)
    (hbp : wordsVal s.mem base (p256.sl B3P) 4 = 3 * W.b * 2 ^ 256 % W.p)
    {p q o : Pt} (hA : RcbApart p256.rcbSlots p q o)
    (hsl : ∀ x ∈ rcbW p256.rcbSlots o ++ rcbR p256.rcbSlots p q, x ∈ jSl)
    {P P' : Point W} (hP : onCurve W P = true) (hP' : onCurve W P' = true)
    (hp : PtOk base s p P) (hq : PtOk base s q P') :
    WP isa (Cfg.addPt p256 p q o) s fun s' =>
      Kp s s' ∧ Unch base (addW o) s.mem s'.mem ∧ PtOk base s' o (Spec.Weierstrass.add P P') := by
  have hp0 : 0 < W.p := by decide
  rw [Cfg.addPt]
  have hI : Inv 4 base W.p (· ∈ jSl) (rcbR p256.rcbSlots p q)
      (fun x => toM W.p (2 ^ (64 * 4)) (wordsVal s.mem base x 4)) s := by
    refine ⟨hw, fun x hx => hsl x (List.mem_append_right _ hx), fun x hx => ?_, fun x _ => rfl⟩
    simp only [rcbR, Cfg.rcbSlots, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hap]; exact Nat.mod_lt _ hp0
    · rw [hbp]; exact Nat.mod_lt _ hp0
    exacts [hp.x, hp.y, hp.z, hq.x, hq.y, hq.z]
  refine WP.mono (rcb_ok (F := p256Field) field_ok rfl jLay jShort unit hA hsl hI (fun x hx => hx))
    fun s₁ ⟨k₁, I₁, t₁, _⟩ => ?_
  have ea : toM W.p (2 ^ (64 * 4)) (wordsVal s.mem base (p256.sl AP) 4) = Fin.ofNat W.p W.a := by
    rw [hap, toM_mont unit]
  have eb : toM W.p (2 ^ (64 * 4)) (wordsVal s.mem base (p256.sl B3P) 4) = Fin.ofNat W.p (3 * W.b) := by
    rw [hbp, toM_mont unit]
  generalize hE : (fun x => toM W.p (2 ^ (64 * 4)) (wordsVal s.mem base x 4)) = E at I₁ t₁
  have hrep := hL.add hP hP' hp.rep hq.rep (X3 := runOps (rcb p256.rcbSlots p q o) E o.x)
    (Y3 := runOps (rcb p256.rcbSlots p q o) E o.y) (Z3 := runOps (rcb p256.rcbSlots p q o) E o.z)
    (by
      subst hE
      show rcbAdd (Fin.ofNat W.p W.a) (Fin.ofNat W.p (3 * W.b)) _ _ _ _ _ _ = _
      rw [← ea, ← eb]
      exact t₁.symm)
  have hm : ∀ x ∈ [o.x, o.y, o.z], x ∈ rcbW p256.rcbSlots o ++ rcbR p256.rcbSlots p q := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [rcbW]
  refine ⟨k₁.kp, k₁.mem, ⟨?_, I₁.lt _ (hm _ (by simp)), I₁.lt _ (hm _ (by simp)), I₁.lt _ (hm _ (by simp))⟩⟩
  have vx : tmv W 4 base s₁ o.x = _ := I₁.val _ (hm _ (by simp))
  have vy : tmv W 4 base s₁ o.y = _ := I₁.val _ (hm _ (by simp))
  have vz : tmv W 4 base s₁ o.z = _ := I₁.val _ (hm _ (by simp))
  rw [vx, vy, vz]
  exact hrep

theorem PtOk.of_eq {base : Addr} {s s' : State} {p : Pt} {P : Point W} (h : PtOk base s p P)
    (hx : wordsVal s'.mem base p.x 4 = wordsVal s.mem base p.x 4)
    (hy : wordsVal s'.mem base p.y 4 = wordsVal s.mem base p.y 4)
    (hz : wordsVal s'.mem base p.z 4 = wordsVal s.mem base p.z 4) : PtOk base s' p P :=
  ⟨by simp only [tmv]; rw [hx, hy, hz]; exact h.rep, hx ▸ h.x, hy ▸ h.y, hz ▸ h.z⟩

/-- A point copied to other slots. -/
theorem PtOk.move {base : Addr} {s s' : State} {p q : Pt} {P : Point W} (h : PtOk base s p P)
    (hx : wordsVal s'.mem base q.x 4 = wordsVal s.mem base p.x 4)
    (hy : wordsVal s'.mem base q.y 4 = wordsVal s.mem base p.y 4)
    (hz : wordsVal s'.mem base q.z 4 = wordsVal s.mem base p.z 4) : PtOk base s' q P :=
  ⟨by simp only [tmv]; rw [hx, hy, hz]; exact h.rep, hx ▸ h.x, hy ▸ h.y, hz ▸ h.z⟩

/-! ## The table -/

/-- Entry `e`'s coordinates. -/
abbrev entPt (e : Nat) : Pt := ⟨2048 + 96 * e, 2048 + 96 * e + 32, 2048 + 96 * e + 64⟩

/-- Entry `e` represents `[e / 4]G + [e % 4]Q`. -/
abbrev EntOk (base : Addr) (s : State) (G Q : Point W) (e : Nat) : Prop :=
  PtOk base s (entPt e) (ent G Q (e / 4) (e % 4))

/-- What the table's construction writes. -/
abbrev buildW : List (Nat × Nat) := [(704, 288), (1536, 384), (2048, 1536), (3840, 256)]

/-- While the table is built, from `s₀`: the entries of `L`. -/
structure BS (base : Addr) (s₀ s : State) (G Q : Point W) (L : List Nat) : Prop where
  ws : WsReg s base
  kp : Kp s₀ s
  unch : Unch base buildW s₀.mem s.mem
  ap : wordsVal s.mem base (p256.sl AP) 4 = W.a * 2 ^ 256 % W.p
  bp : wordsVal s.mem base (p256.sl B3P) 4 = 3 * W.b * 2 ^ 256 % W.p
  ents : ∀ e ∈ L, e < 16 ∧ EntOk base s G Q e

/-- A point to entry `e`: the entries so far are kept, and so is every slot. -/
theorem store_ok' {base : Addr} {s₀ s : State} {G Q : Point W} {L : List Nat} (h : BS base s₀ s G Q L)
    {e : Nat} (he : e < 16) {p : Pt}
    (hx : p.x % 8 = 0 ∧ p.x + 32 ≤ 2048) (hy : p.y % 8 = 0 ∧ p.y + 32 ≤ 2048)
    (hz : p.z % 8 = 0 ∧ p.z + 32 ≤ 2048) (hp : PtOk base s p (ent G Q (e / 4) (e % 4))) :
    WP isa (.block (Cfg.storePt p256 e p)) s fun s' => BS base s₀ s' G Q (e :: L) ∧
      ∀ d, d + 32 ≤ 2048 → wordsVal s'.mem base d 4 = wordsVal s.mem base d 4 := by
  have hn := h.ws.nowrap
  refine WP.mono (storePt_ok h.ws he hx hy hz) fun s' ⟨ex, ey, ez, r, O⟩ => ?_
  have hd : ∀ d, d + 32 ≤ 2048 → wordsVal s'.mem base d 4 = wordsVal s.mem base d 4 := fun d hd =>
    O.wordsVal (by omega) (by omega)
  refine ⟨⟨h.ws.of_rest r, h.kp.trans (Kp.of_rest r), ?_, ?_, ?_, ?_⟩, hd⟩
  · refine (h.unch.trans O.unch).cover fun w hw => ?_
    rcases List.mem_append.mp hw with hw | hw
    · exact ⟨w, hw, Nat.le_refl _, Nat.le_refl _⟩
    · rw [List.mem_singleton] at hw
      subst hw
      exact ⟨(2048, 1536), List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
        by show 2048 ≤ 2048 + 96 * e; omega, by show 2048 + 96 * e + 96 ≤ 2048 + 1536; omega⟩
  · rw [hd (p256.sl AP) (by show 256 + 32 ≤ 2048; omega)]; exact h.ap
  · rw [hd (p256.sl B3P) (by show 288 + 32 ≤ 2048; omega)]; exact h.bp
  · intro e' he'
    simp only [List.mem_cons] at he'
    rcases he' with rfl | he'
    · exact ⟨he, hp.move ex ey ez⟩
    · obtain ⟨hlt, hok⟩ := h.ents e' he'
      by_cases hee : e' = e
      · subst hee
        exact ⟨hlt, hp.move ex ey ez⟩
      · have h1 : e' < e ∨ e < e' := by omega
        refine ⟨hlt, hok.of_eq ?_ ?_ ?_⟩
        · exact O.wordsVal (d := 2048 + 96 * e') (by rcases h1 with h1 | h1 <;> omega) (by omega)
        · exact O.wordsVal (d := 2048 + 96 * e' + 32) (by rcases h1 with h1 | h1 <;> omega) (by omega)
        · exact O.wordsVal (d := 2048 + 96 * e' + 64) (by rcases h1 with h1 | h1 <;> omega) (by omega)

/-- `o = p + q`, for `o` among the slots the construction writes: the
entries are kept. -/
theorem add_ok' (hL : Law W) {base : Addr} {s₀ s : State} {G Q : Point W} {L : List Nat}
    (h : BS base s₀ s G Q L) {p q o : Pt} (hA : RcbApart p256.rcbSlots p q o)
    (hsl : ∀ x ∈ rcbW p256.rcbSlots o ++ rcbR p256.rcbSlots p q, x ∈ jSl)
    (hW : ∀ w ∈ addW o, ∃ w' ∈ buildW, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2)
    {P P' : Point W} (hP : onCurve W P = true) (hP' : onCurve W P' = true)
    (hp : PtOk base s p P) (hq : PtOk base s q P') :
    WP isa (Cfg.addPt p256 p q o) s fun s' => BS base s₀ s' G Q L ∧
      PtOk base s' o (Spec.Weierstrass.add P P') ∧ Unch base (addW o) s.mem s'.mem := by
  have hn := h.ws.nowrap
  refine WP.mono (addPt_ok hL h.ws h.ap h.bp hA hsl hP hP' hp hq) fun s' ⟨K, U, ok⟩ => ?_
  have hd : ∀ d, (∀ w ∈ addW o, d + 32 ≤ w.1 ∨ w.1 + w.2 ≤ d) → d + 32 ≤ 8192 →
      wordsVal s'.mem base d 4 = wordsVal s.mem base d 4 := fun d h1 h2 => U.wordsVal h1 (by omega)
  have hfar : ∀ d, 2048 ≤ d → d + 32 ≤ 3840 → ∀ w ∈ addW o, d + 32 ≤ w.1 ∨ w.1 + w.2 ≤ d := by
    intro d h1 h2 w hw
    obtain ⟨w', hw', l1, l2⟩ := hW w hw
    have hsl' : ∀ x ∈ rcbW p256.rcbSlots o, x + 32 ≤ 2048 := fun x hx =>
      (by decide : ∀ x ∈ jSl, x + 32 ≤ 2048) x (hsl x (List.mem_append_left _ hx))
    simp only [addW, List.mem_append, List.mem_map, List.mem_singleton] at hw
    rcases hw with ⟨x, hx, rfl⟩ | rfl
    · have := hsl' x hx; right; simp only; omega
    · left; show d + 32 ≤ 3840; omega
  refine ⟨⟨h.ws.of_kp K, h.kp.trans K, (h.unch.trans U).cover fun w hw => ?_, ?_, ?_, ?_⟩, ok, U⟩
  · rcases List.mem_append.mp hw with hw | hw
    · exact ⟨w, hw, Nat.le_refl _, Nat.le_refl _⟩
    · exact hW w hw
  · have hlow : ∀ w ∈ addW o, 704 ≤ w.1 := fun w hw => by
      obtain ⟨w', hw', l1, l2⟩ := hW w hw
      have : 704 ≤ w'.1 := by
        simp only [buildW, List.mem_cons, List.not_mem_nil, or_false] at hw'
        rcases hw' with rfl | rfl | rfl | rfl <;> decide
      omega
    rw [hd (p256.sl AP) (fun w hw => .inl (by have := hlow w hw; show 256 + 32 ≤ w.1; omega))
      (by show 256 + 32 ≤ 8192; omega)]
    exact h.ap
  · have hlow : ∀ w ∈ addW o, 704 ≤ w.1 := fun w hw => by
      obtain ⟨w', hw', l1, l2⟩ := hW w hw
      have : 704 ≤ w'.1 := by
        simp only [buildW, List.mem_cons, List.not_mem_nil, or_false] at hw'
        rcases hw' with rfl | rfl | rfl | rfl <;> decide
      omega
    rw [hd (p256.sl B3P) (fun w hw => .inl (by have := hlow w hw; show 288 + 32 ≤ w.1; omega))
      (by show 288 + 32 ≤ 8192; omega)]
    exact h.bp
  · intro e he
    obtain ⟨hlt, hok⟩ := h.ents e he
    exact ⟨hlt, hok.of_eq (hd (2048 + 96 * e) (hfar _ (by omega) (by omega)) (by omega))
      (hd (2048 + 96 * e + 32) (hfar _ (by omega) (by omega)) (by omega))
      (hd (2048 + 96 * e + 64) (hfar _ (by omega) (by omega)) (by omega))⟩

/-! ## The table's construction -/

section
variable {C : Spec.Weierstrass.Curve}

theorem mul_zero' (P : Point C) : mul 0 P = .infinity := by rw [Spec.Weierstrass.mul]; rfl

theorem add_inf (P : Point C) : Spec.Weierstrass.add P .infinity = P := by cases P <;> rfl

theorem mul_one' (P : Point C) : mul 1 P = P := by
  rw [Spec.Weierstrass.mul, ite_eq_right (by decide), show (1 : Nat) / 2 = 0 from rfl, mul_zero',
    ite_eq_right (by decide)]
  rfl

theorem mul_two' (P : Point C) : mul 2 P = Spec.Weierstrass.add P P := by
  rw [Spec.Weierstrass.mul, ite_eq_right (by decide), show (2 : Nat) / 2 = 1 from rfl, mul_one', ite_eq_left (by decide)]

theorem mul_three' (P : Point C) : mul 3 P = Spec.Weierstrass.add (mul 2 P) P := by
  rw [Spec.Weierstrass.mul, ite_eq_right (by decide), show (3 : Nat) / 2 = 1 from rfl, mul_one', ite_eq_right (by decide),
    mul_two']

theorem ent_a0 (G Q : Point C) (a : Nat) : ent G Q a 0 = mul a G := by
  rw [ent, mul_zero', add_inf]

theorem ent_0b (G Q : Point C) (b : Nat) : ent G Q 0 b = mul b Q := by
  rw [ent, mul_zero']; rfl

end

/-- What the construction reads: the constants, `G` and `Q`. -/
structure JPre (base : Addr) (s : State) (Q : Point W) : Prop where
  ws : WsReg s base
  ap : wordsVal s.mem base (p256.sl AP) 4 = W.a * 2 ^ 256 % W.p
  bp : wordsVal s.mem base (p256.sl B3P) 4 = 3 * W.b * 2 ^ 256 % W.p
  zero : wordsVal s.mem base (p256.sl ZERO) 4 = 0
  onep : wordsVal s.mem base (p256.sl ONEP) 4 = 1 * 2 ^ 256 % W.p
  gx : wordsVal s.mem base (p256.sl GX) 4 = W.gx * 2 ^ 256 % W.p
  gy : wordsVal s.mem base (p256.sl GY) 4 = W.gy * 2 ^ 256 % W.p
  qx : wordsVal s.mem base (p256.sl CPX) 4 < W.p
  qy : wordsVal s.mem base (p256.sl CPY) 4 < W.p
  q : Point.affine (tmv W 4 base s (p256.sl CPX)) (tmv W 4 base s (p256.sl CPY)) = Q
  on : onCurve W Q = true

/-- The coordinates of the multiples of `G` and `Q` in slots. -/
abbrev gqSl : List Nat :=
  [p256.sl GX, p256.sl GY, p256.sl ONEP, p256.sl CPX, p256.sl CPY,
    p256.sl G2X, p256.sl G2Y, p256.sl G2Z, p256.sl G3X, p256.sl G3Y, p256.sl G3Z,
    p256.sl Q2X, p256.sl Q2Y, p256.sl Q2Z, p256.sl Q3X, p256.sl Q3Y, p256.sl Q3Z]

theorem gPt_sl : ∀ a ∈ [1, 2, 3], (Cfg.gPt p256 a).x ∈ gqSl ∧ (Cfg.gPt p256 a).y ∈ gqSl ∧
    (Cfg.gPt p256 a).z ∈ gqSl := by decide

theorem qPt_sl : ∀ b ∈ [1, 2, 3], (Cfg.qPt p256 b).x ∈ gqSl ∧ (Cfg.qPt p256 b).y ∈ gqSl ∧
    (Cfg.qPt p256 b).z ∈ gqSl := by decide

/-- A point in slots of `gqSl`, kept where those slots are. -/
theorem PtOk.keep {base : Addr} {s s' : State} {p : Pt} {P : Point W} (h : PtOk base s p P)
    (hk : ∀ d ∈ gqSl, wordsVal s'.mem base d 4 = wordsVal s.mem base d 4)
    (hp : p.x ∈ gqSl ∧ p.y ∈ gqSl ∧ p.z ∈ gqSl) : PtOk base s' p P :=
  h.of_eq (hk _ hp.1) (hk _ hp.2.1) (hk _ hp.2.2)

theorem keep_addT {base : Addr} {m m' : Mem} (U : Unch base (addW (p256.pt TX TY TZ)) m m') :
    ∀ d ∈ gqSl, wordsVal m' base d 4 = wordsVal m base d 4 := by
  have h : ∀ d ∈ gqSl, ∀ w ∈ addW (p256.pt TX TY TZ), d + 8 * 4 ≤ w.1 ∨ w.1 + w.2 ≤ d := by decide
  intro d hd
  exact U.wordsVal (h d hd) (by have : d < 2048 := (by decide : ∀ d ∈ gqSl, d < 2048) d hd; omega)

theorem apart_mixed' : ∀ a ∈ [1, 2, 3], ∀ b ∈ [1, 2, 3],
    ((rcbW p256.rcbSlots (p256.pt TX TY TZ)).Nodup ∧
      ∀ x ∈ rcbR p256.rcbSlots (Cfg.gPt p256 a) (Cfg.qPt p256 b), x ∉ rcbW p256.rcbSlots (p256.pt TX TY TZ)) ∧
    (∀ x ∈ rcbW p256.rcbSlots (p256.pt TX TY TZ) ++ rcbR p256.rcbSlots (Cfg.gPt p256 a) (Cfg.qPt p256 b), x ∈ jSl) :=
  by decide

theorem apart_mixed {a b : Nat} (ha : a ∈ [1, 2, 3]) (hb : b ∈ [1, 2, 3]) :
    RcbApart p256.rcbSlots (Cfg.gPt p256 a) (Cfg.qPt p256 b) (p256.pt TX TY TZ) ∧
    (∀ x ∈ rcbW p256.rcbSlots (p256.pt TX TY TZ) ++ rcbR p256.rcbSlots (Cfg.gPt p256 a) (Cfg.qPt p256 b), x ∈ jSl) :=
  have h := apart_mixed' a ha b hb
  ⟨⟨h.1.1, h.1.2⟩, h.2⟩

theorem slots_mixed : ∀ x ∈ [p256.sl TX, p256.sl TY, p256.sl TZ], x % 8 = 0 ∧ x + 32 ≤ 2048 := by decide

/-- Entry `4 a + b`, from `[a]G` and `[b]Q` in slots. -/
theorem mixed_ok (hL : Law W) {base : Addr} {s₀ s : State} {G Q : Point W} (hG : onCurve W G = true)
    (hQ : onCurve W Q = true) {L : List Nat} (h : BS base s₀ s G Q L) {a b : Nat} (ha : a ∈ [1, 2, 3])
    (hb : b ∈ [1, 2, 3]) (hpa : PtOk base s (Cfg.gPt p256 a) (mul a G))
    (hpb : PtOk base s (Cfg.qPt p256 b) (mul b Q)) :
    WP isa (Cfg.mixed p256 a b) s fun s' => BS base s₀ s' G Q ((4 * a + b) :: L) ∧
      ∀ d ∈ gqSl, wordsVal s'.mem base d 4 = wordsVal s.mem base d 4 := by
  obtain ⟨hA, hsl⟩ := apart_mixed ha hb
  have hab : a < 4 ∧ b < 4 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb; omega
  rw [Cfg.mixed]
  refine WP.seq (WP.mono (add_ok' hL h hA hsl (by decide) (hL.onCurve_mul hG _) (hL.onCurve_mul hQ _) hpa hpb)
    fun s₁ ⟨h₁, ok₁, U₁⟩ => ?_)
  have k₁ := keep_addT U₁
  have e₁ : ent G Q ((4 * a + b) / 4) ((4 * a + b) % 4) = Spec.Weierstrass.add (mul a G) (mul b Q) := by
    rw [show (4 * a + b) / 4 = a by omega, show (4 * a + b) % 4 = b by omega]; rfl
  refine WP.mono (store_ok' h₁ (e := 4 * a + b) (by omega) (slots_mixed _ (by decide))
    (slots_mixed _ (by decide)) (slots_mixed _ (by decide)) (e₁ ▸ ok₁)) fun s₂ ⟨h₂, k₂⟩ => ⟨h₂, fun d hd => ?_⟩
  rw [k₂ d (by have := (by decide : ∀ d ∈ gqSl, d + 32 ≤ 2048) d hd; exact this), k₁ d hd]

/-- The nine entries of both. -/
theorem mixeds_ok (hL : Law W) {base : Addr} {s₀ : State} {G Q : Point W} (hG : onCurve W G = true)
    (hQ : onCurve W Q = true) :
    ∀ (l : List (Nat × Nat)) {s : State} {L : List Nat}, l ≠ [] → (∀ ab ∈ l, ab.1 ∈ [1, 2, 3] ∧ ab.2 ∈ [1, 2, 3]) →
    BS base s₀ s G Q L → (∀ a ∈ [1, 2, 3], PtOk base s (Cfg.gPt p256 a) (mul a G)) →
    (∀ b ∈ [1, 2, 3], PtOk base s (Cfg.qPt p256 b) (mul b Q)) →
    WP isa (progs (l.map fun ab => Cfg.mixed p256 ab.1 ab.2)) s fun s' =>
      BS base s₀ s' G Q ((l.map fun ab => 4 * ab.1 + ab.2).reverse ++ L)
  | [], _, _, h0, _, _, _, _ => absurd rfl h0
  | [ab], s, L, _, hl, h, hgs, hqs => by
    have hab := hl ab (by simp)
    simp only [List.map_cons, List.map_nil, progs, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append]
    exact WP.mono (mixed_ok hL hG hQ h hab.1 hab.2 (hgs _ hab.1) (hqs _ hab.2)) fun _ h' => h'.1
  | ab :: ab' :: l, s, L, _, hl, h, hgs, hqs => by
    have hab := hl ab (by simp)
    simp only [List.map_cons]
    rw [show progs (Cfg.mixed p256 ab.1 ab.2 :: Cfg.mixed p256 ab'.1 ab'.2 ::
      List.map (fun ab => Cfg.mixed p256 ab.1 ab.2) l) = .seq (Cfg.mixed p256 ab.1 ab.2)
        (progs (Cfg.mixed p256 ab'.1 ab'.2 :: List.map (fun ab => Cfg.mixed p256 ab.1 ab.2) l)) from rfl]
    refine WP.seq (WP.mono (mixed_ok hL hG hQ h hab.1 hab.2 (hgs _ hab.1) (hqs _ hab.2)) fun s₁ ⟨h₁, k₁⟩ => ?_)
    have := mixeds_ok hL hG hQ (ab' :: l) (L := (4 * ab.1 + ab.2) :: L) (by simp)
      (fun x hx => hl x (List.mem_cons_of_mem _ hx)) h₁
      (fun a ha => (hgs a ha).keep k₁ (gPt_sl a ha)) (fun b hb => (hqs b hb).keep k₁ (qPt_sl b hb))
    simp only [List.map_cons] at this
    simpa [List.reverse_cons, List.append_assoc] using this

/-- The table: entry `e` represents `[e / 4]G + [e % 4]Q`. -/
abbrev JTab (base : Addr) (s : State) (G Q : Point W) : Prop := ∀ e < 16, EntOk base s G Q e

/-- Slots apart from what code writes are kept. -/
theorem keepU {base : Addr} {Wl : List (Nat × Nat)} {m m' : Mem} (U : Unch base Wl m m') {D : List Nat}
    (hD : ∀ d ∈ D, (∀ w ∈ Wl, d + 8 * 4 ≤ w.1 ∨ w.1 + w.2 ≤ d) ∧ d + 32 ≤ 2048) :
    ∀ d ∈ D, wordsVal m' base d 4 = wordsVal m base d 4 := fun d hd =>
  U.wordsVal (hD d hd).1 (by have := (hD d hd).2; omega)

/-- `O`, `G` and `Q` to entries 0, 4 and 1. -/
theorem first3_ok {base : Addr} {s₀ s : State} {G Q : Point W} (h : BS base s₀ s G Q [])
    (pO : PtOk base s (p256.pt ZERO ONEP ZERO) (ent G Q (0 / 4) (0 % 4)))
    (pG : PtOk base s (Cfg.gPt p256 1) (ent G Q (4 / 4) (4 % 4)))
    (pQ : PtOk base s (Cfg.qPt p256 1) (ent G Q (1 / 4) (1 % 4))) {rest : Prog isa} {R : State → Prop}
    (k : ∀ s', BS base s₀ s' G Q [1, 4, 0] → (∀ d, d + 32 ≤ 2048 → wordsVal s'.mem base d 4 = wordsVal s.mem base d 4) →
      WP isa rest s' R) :
    WP isa (.seq (.block (Cfg.storePt p256 0 (p256.pt ZERO ONEP ZERO) ++ Cfg.storePt p256 4 (Cfg.gPt p256 1) ++
      Cfg.storePt p256 1 (Cfg.qPt p256 1))) rest) s R := by
  have sl8 : ∀ x ∈ [p256.sl ZERO, p256.sl ONEP, p256.sl GX, p256.sl GY, p256.sl CPX, p256.sl CPY],
      x % 8 = 0 ∧ x + 32 ≤ 2048 := by decide
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (store_ok' h (e := 0) (p := p256.pt ZERO ONEP ZERO) (by decide)
    (sl8 _ (by decide)) (sl8 _ (by decide)) (sl8 _ (by decide)) pO) fun s₁ ⟨h₁, k₁⟩ => ?_))
  have pG₁ := pG.of_eq (k₁ _ (by decide)) (k₁ _ (by decide)) (k₁ _ (by decide))
  refine WP.block_append (WP.mono (store_ok' h₁ (e := 4) (p := Cfg.gPt p256 1) (by decide) (sl8 _ (by decide))
    (sl8 _ (by decide)) (sl8 _ (by decide)) pG₁) fun s₂ ⟨h₂, k₂⟩ => ?_)
  have pQ₂ := pQ.of_eq ((k₂ _ (by decide)).trans (k₁ _ (by decide))) ((k₂ _ (by decide)).trans (k₁ _ (by decide)))
    ((k₂ _ (by decide)).trans (k₁ _ (by decide)))
  refine WP.mono (store_ok' h₂ (e := 1) (p := Cfg.qPt p256 1) (by decide) (sl8 _ (by decide)) (sl8 _ (by decide))
    (sl8 _ (by decide)) pQ₂) fun s₃ ⟨h₃, k₃⟩ => k s₃ h₃ fun d hd => ((k₃ d hd).trans (k₂ d hd)).trans (k₁ d hd)

/-- `2P` and `3P` from `P` in the slots `p₁`, to `p₂` and `p₃` and to the
entries `e₂` and `e₃`; the slots of `D` are kept. -/
theorem mult_ok (hL : Law W) {base : Addr} {s₀ s : State} {G Q P : Point W} (hP : onCurve W P = true)
    {L : List Nat} (h : BS base s₀ s G Q L) {p₁ p₂ p₃ : Pt} {e₂ e₃ : Nat} (he₂ : e₂ < 16) (he₃ : e₃ < 16)
    (hA₂ : RcbApart p256.rcbSlots p₁ p₁ p₂) (hA₃ : RcbApart p256.rcbSlots p₂ p₁ p₃)
    (hsl₂ : ∀ x ∈ rcbW p256.rcbSlots p₂ ++ rcbR p256.rcbSlots p₁ p₁, x ∈ jSl)
    (hsl₃ : ∀ x ∈ rcbW p256.rcbSlots p₃ ++ rcbR p256.rcbSlots p₂ p₁, x ∈ jSl)
    (hW₂ : ∀ w ∈ addW p₂, ∃ w' ∈ buildW, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2)
    (hW₃ : ∀ w ∈ addW p₃, ∃ w' ∈ buildW, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2)
    (hs₂ : ∀ x ∈ [p₂.x, p₂.y, p₂.z], x % 8 = 0 ∧ x + 32 ≤ 2048)
    (hs₃ : ∀ x ∈ [p₃.x, p₃.y, p₃.z], x % 8 = 0 ∧ x + 32 ≤ 2048)
    (hk₁ : ∀ d ∈ [p₁.x, p₁.y, p₁.z], (∀ w ∈ addW p₂ ++ addW p₃, d + 8 * 4 ≤ w.1 ∨ w.1 + w.2 ≤ d) ∧ d + 32 ≤ 2048)
    (hk₂ : ∀ d ∈ [p₂.x, p₂.y, p₂.z], (∀ w ∈ addW p₃, d + 8 * 4 ≤ w.1 ∨ w.1 + w.2 ≤ d) ∧ d + 32 ≤ 2048)
    {D : List Nat} (hD : ∀ d ∈ D, (∀ w ∈ addW p₂ ++ addW p₃, d + 8 * 4 ≤ w.1 ∨ w.1 + w.2 ≤ d) ∧ d + 32 ≤ 2048)
    (e2 : ent G Q (e₂ / 4) (e₂ % 4) = mul 2 P) (e3 : ent G Q (e₃ / 4) (e₃ % 4) = mul 3 P)
    (hp₁ : PtOk base s p₁ (mul 1 P)) {rest : Prog isa} {R : State → Prop}
    (k : ∀ s', BS base s₀ s' G Q (e₃ :: e₂ :: L) → PtOk base s' p₁ (mul 1 P) → PtOk base s' p₂ (mul 2 P) →
      PtOk base s' p₃ (mul 3 P) → (∀ d ∈ D, wordsVal s'.mem base d 4 = wordsVal s.mem base d 4) → WP isa rest s' R) :
    WP isa (.seq (Cfg.addPt p256 p₁ p₁ p₂) <| .seq (.block (Cfg.storePt p256 e₂ p₂)) <|
      .seq (Cfg.addPt p256 p₂ p₁ p₃) <| .seq (.block (Cfg.storePt p256 e₃ p₃)) rest) s R := by
  have h1 := hL.onCurve_mul hP 1
  refine WP.seq (WP.mono (add_ok' hL h hA₂ hsl₂ hW₂ h1 h1 hp₁ hp₁) fun s₁ ⟨h₁, ok₂, U₁⟩ => ?_)
  rw [mul_one', ← mul_two'] at ok₂
  have k₁ : ∀ d ∈ [p₁.x, p₁.y, p₁.z] ++ D, wordsVal s₁.mem base d 4 = wordsVal s.mem base d 4 :=
    keepU U₁ fun d hd => by
      rcases List.mem_append.mp hd with hd | hd
      · exact ⟨fun w hw => (hk₁ d hd).1 w (List.mem_append_left _ hw), (hk₁ d hd).2⟩
      · exact ⟨fun w hw => (hD d hd).1 w (List.mem_append_left _ hw), (hD d hd).2⟩
  refine WP.seq (WP.mono (store_ok' h₁ he₂ (hs₂ _ (by simp)) (hs₂ _ (by simp)) (hs₂ _ (by simp))
    (e2.symm ▸ ok₂)) fun s₂ ⟨h₂, k₂⟩ => ?_)
  have p₁₂ : PtOk base s₂ p₁ (mul 1 P) :=
    hp₁.of_eq ((k₂ _ (hk₁ _ (by simp)).2).trans (k₁ _ (by simp))) ((k₂ _ (hk₁ _ (by simp)).2).trans (k₁ _ (by simp)))
      ((k₂ _ (hk₁ _ (by simp)).2).trans (k₁ _ (by simp)))
  have ok₂' : PtOk base s₂ p₂ (mul 2 P) :=
    ok₂.of_eq (k₂ _ (hs₂ _ (by simp)).2) (k₂ _ (hs₂ _ (by simp)).2) (k₂ _ (hs₂ _ (by simp)).2)
  refine WP.seq (WP.mono (add_ok' hL h₂ hA₃ hsl₃ hW₃ (hL.onCurve_mul hP 2) h1 ok₂' p₁₂) fun s₃ ⟨h₃, ok₃, U₃⟩ => ?_)
  rw [mul_one', ← mul_three'] at ok₃
  have k₃ : ∀ d ∈ [p₁.x, p₁.y, p₁.z] ++ [p₂.x, p₂.y, p₂.z] ++ D,
      wordsVal s₃.mem base d 4 = wordsVal s₂.mem base d 4 :=
    keepU U₃ fun d hd => by
      rcases List.mem_append.mp hd with hd | hd
      · rcases List.mem_append.mp hd with hd | hd
        · exact ⟨fun w hw => (hk₁ d hd).1 w (List.mem_append_right _ hw), (hk₁ d hd).2⟩
        · exact hk₂ d hd
      · exact ⟨fun w hw => (hD d hd).1 w (List.mem_append_right _ hw), (hD d hd).2⟩
  refine WP.seq (WP.mono (store_ok' h₃ he₃ (hs₃ _ (by simp)) (hs₃ _ (by simp)) (hs₃ _ (by simp)) (e3.symm ▸ ok₃))
    fun s₄ ⟨h₄, k₄⟩ => k s₄ h₄ ?_ ?_ ?_ ?_)
  · exact p₁₂.of_eq ((k₄ _ (hk₁ _ (by simp)).2).trans (k₃ _ (by simp))) ((k₄ _ (hk₁ _ (by simp)).2).trans
      (k₃ _ (by simp))) ((k₄ _ (hk₁ _ (by simp)).2).trans (k₃ _ (by simp)))
  · exact ok₂'.of_eq ((k₄ _ (hk₂ _ (by simp)).2).trans (k₃ _ (by simp))) ((k₄ _ (hk₂ _ (by simp)).2).trans
      (k₃ _ (by simp))) ((k₄ _ (hk₂ _ (by simp)).2).trans (k₃ _ (by simp)))
  · exact ok₃.of_eq (k₄ _ (hs₃ _ (by simp)).2) (k₄ _ (hs₃ _ (by simp)).2) (k₄ _ (hs₃ _ (by simp)).2)
  · intro d hd
    rw [k₄ d (hD d hd).2, k₃ d (List.mem_append_right _ hd), k₂ d (hD d hd).2, k₁ d (List.mem_append_right _ hd)]

/-- The table, from `G` and `Q` in slots. -/
theorem build_ok (hL : Law W) {base : Addr} {s : State} {Q : Point W} (hp : JPre base s Q) :
    WP isa (Cfg.build p256) s fun s' =>
      Kp s s' ∧ Unch base buildW s.mem s'.mem ∧ JTab base s' (Spec.Weierstrass.G W) Q := by
  have hw := hp.ws
  have hp0 : 0 < W.p := by decide
  generalize hGG : Spec.Weierstrass.G W = G
  have hG : onCurve W G = true := hGG ▸ VG.Proof.P256.onCurve_G
  have hQ := hp.on
  have h1 : tmv W 4 base s (p256.sl ONEP) = 1 := by
    simp only [tmv]; rw [hp.onep, Nat.one_mul]; exact toM_one unit
  have pO : PtOk base s (p256.pt ZERO ONEP ZERO) (ent G Q (0 / 4) (0 % 4)) := by
    refine ⟨?_, show wordsVal _ _ (p256.sl ZERO) 4 < _ by rw [hp.zero]; exact hp0,
      show wordsVal _ _ (p256.sl ONEP) 4 < _ by rw [hp.onep]; exact Nat.mod_lt _ hp0,
      show wordsVal _ _ (p256.sl ZERO) 4 < _ by rw [hp.zero]; exact hp0⟩
    have h0 : tmv W 4 base s (p256.sl ZERO) = 0 := by simp only [tmv]; rw [hp.zero]; exact toM_zero _ _
    show Rep W (tmv W 4 base s (p256.sl ZERO)) (tmv W 4 base s (p256.sl ONEP)) (tmv W 4 base s (p256.sl ZERO)) _
    rw [h0, h1, show (0 : Nat) / 4 = 0 from rfl, ent_a0, mul_zero']
    exact rep_infinity' hL
  have pG : PtOk base s (Cfg.gPt p256 1) (mul 1 G) := by
    refine ⟨?_, show wordsVal _ _ (p256.sl GX) 4 < _ by rw [hp.gx]; exact Nat.mod_lt _ hp0,
      show wordsVal _ _ (p256.sl GY) 4 < _ by rw [hp.gy]; exact Nat.mod_lt _ hp0,
      show wordsVal _ _ (p256.sl ONEP) 4 < _ by rw [hp.onep]; exact Nat.mod_lt _ hp0⟩
    show Rep W (tmv W 4 base s (p256.sl GX)) (tmv W 4 base s (p256.sl GY)) (tmv W 4 base s (p256.sl ONEP)) _
    rw [h1, mul_one', ← hGG]
    have ex : tmv W 4 base s (p256.sl GX) = Fin.ofNat W.p W.gx := by simp only [tmv]; rw [hp.gx, toM_mont unit]
    have ey : tmv W 4 base s (p256.sl GY) = Fin.ofNat W.p W.gy := by simp only [tmv]; rw [hp.gy, toM_mont unit]
    rw [ex, ey]
    exact rep_affine' hL _ _
  have pQ : PtOk base s (Cfg.qPt p256 1) (mul 1 Q) := by
    refine ⟨?_, hp.qx, hp.qy, show wordsVal _ _ (p256.sl ONEP) 4 < _ by rw [hp.onep]; exact Nat.mod_lt _ hp0⟩
    show Rep W (tmv W 4 base s (p256.sl CPX)) (tmv W 4 base s (p256.sl CPY)) (tmv W 4 base s (p256.sl ONEP)) _
    rw [h1, mul_one', ← hp.q]
    exact rep_affine' hL _ _
  have h0 : BS base s s G Q [] :=
    ⟨hw, Kp.refl s, Unch.refl _ _ _, hp.ap, hp.bp, fun _ h => absurd h (List.not_mem_nil)⟩
  rw [Cfg.build]
  refine first3_ok h0 pO ((ent_a0 G Q 1).symm ▸ pG) ((ent_0b G Q 1).symm ▸ pQ) fun s₃ h₃ k₃ => ?_
  have pG₃ := pG.of_eq (k₃ _ (by decide)) (k₃ _ (by decide)) (k₃ _ (by decide))
  have pQ₃ := pQ.of_eq (k₃ _ (by decide)) (k₃ _ (by decide)) (k₃ _ (by decide))
  refine mult_ok hL hG h₃ (p₁ := Cfg.gPt p256 1) (p₂ := Cfg.gPt p256 2) (p₃ := Cfg.gPt p256 3) (e₂ := 8) (e₃ := 12)
    (by decide) (by decide) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (D := [p256.sl CPX, p256.sl CPY, p256.sl ONEP])
    (by decide) (ent_a0 G Q 2) (ent_a0 G Q 3) pG₃ fun s₇ h₇ g1 g2 g3 k₇ => ?_
  have pQ₇ := pQ₃.of_eq (k₇ _ (by decide)) (k₇ _ (by decide)) (k₇ _ (by decide))
  refine mult_ok hL hQ h₇ (p₁ := Cfg.qPt p256 1) (p₂ := Cfg.qPt p256 2) (p₃ := Cfg.qPt p256 3) (e₂ := 2) (e₃ := 3)
    (by decide) (by decide) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (D := [p256.sl GX, p256.sl GY, p256.sl ONEP, p256.sl G2X, p256.sl G2Y, p256.sl G2Z,
      p256.sl G3X, p256.sl G3Y, p256.sl G3Z])
    (by decide) (ent_0b G Q 2) (ent_0b G Q 3) pQ₇ fun s₁₁ h₁₁ q1 q2 q3 k₁₁ => ?_
  have hgs : ∀ a ∈ [1, 2, 3], PtOk base s₁₁ (Cfg.gPt p256 a) (mul a G) := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact g1.of_eq (k₁₁ _ (by decide)) (k₁₁ _ (by decide)) (k₁₁ _ (by decide))
    · exact g2.of_eq (k₁₁ _ (by decide)) (k₁₁ _ (by decide)) (k₁₁ _ (by decide))
    · exact g3.of_eq (k₁₁ _ (by decide)) (k₁₁ _ (by decide)) (k₁₁ _ (by decide))
  have hqs : ∀ b ∈ [1, 2, 3], PtOk base s₁₁ (Cfg.qPt p256 b) (mul b Q) := by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    exacts [q1, q2, q3]
  -- The nine.
  have hl : (List.range 3).flatMap (fun a => (List.range 3).map fun b => Cfg.mixed p256 (a + 1) (b + 1)) =
      ([(1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (3, 3)] : List (Nat × Nat)).map
        fun ab => Cfg.mixed p256 ab.1 ab.2 := rfl
  rw [hl]
  refine WP.mono (mixeds_ok hL hG hQ _ (by decide) (by decide) h₁₁ hgs hqs) fun s' h' => ⟨h'.kp, h'.unch, ?_⟩
  intro e he
  exact (h'.ents e ((by decide : ∀ e < 16, e ∈ ((([(1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2),
    (3, 3)] : List (Nat × Nat)).map fun ab => 4 * ab.1 + ab.2).reverse ++ [3, 2, 12, 8, 1, 4, 0])) e he)).2

/-! ## The window -/

/-- Two bits of `u` at `r = 2 j mod 64` in `x`: `(u >>> 2 j) mod 4`. -/
theorem two_bits (x : BitVec 64) (u : Nat) {j : Nat} (h0 : x.getLsbD (2 * j % 64) = u.testBit (2 * j))
    (h1 : x.getLsbD (2 * j % 64 + 1) = u.testBit (2 * j + 1)) :
    (x >>> (2 * j % 64)) &&& BitVec.ofInt 64 3 = BitVec.ofNat 64 ((u >>> (2 * j)) % 4) := by
  rw [show (u >>> (2 * j)) % 4 = (u >>> (2 * j)) % 2 ^ 2 from rfl]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, show (BitVec.ofInt 64 3) = BitVec.ofNat 64 (2 ^ 2 - 1) from rfl,
    BitVec.getLsbD_ofNat, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftRight]
  have : i = 0 ∨ i = 1 ∨ 2 ≤ i := by omega
  rcases this with rfl | rfl | h
  · simp only [Nat.add_zero, h0]; simp
  · simp only [h1]; simp [Nat.add_comm]
  · simp [show ¬ i < 2 by omega]

theorem combine4 : ∀ a < 4, ∀ b < 4, (BitVec.ofNat 64 a <<< 2) ||| BitVec.ofNat 64 b = BitVec.ofNat 64 (4 * a + b) := by
  decide

/-- The window's entry number, `4 u_j + v_j`, into `t2`, for `j` in `s1`. -/
theorem window_ok {s : State} {base : Addr} (hw : WsReg s base) {j : Nat} (hj : j < 128)
    (h1 : s.gpr .s1 = BitVec.ofNat 64 j) :
    WP isa (.block (Cfg.window p256)) s fun s' =>
      s'.gpr .t2 = BitVec.ofNat 64 (4 * ((wordsVal s.mem base (p256.sl UU) 4 >>> (2 * j)) % 4) +
        (wordsVal s.mem base (p256.sl VV) 4 >>> (2 * j)) % 4) ∧
      Rest [.t0, .t1, .t2, .t3] s s' ∧ s'.mem = s.mem := by
  have hn := hw.nowrap
  have hal := hw.al
  have hq : j / 32 ≤ 3 := by omega
  rw [Cfg.window]
  refine wp_srl (by decide) fun s₁ u₁ => wp_sll (by decide) fun s₂ u₂ => wp_add fun s₃ u₃ => ?_
  have e₃' : s₃.gpr .t1 = base + BitVec.ofNat 64 (8 * (j / 32)) := by
    rw [u₃.gpr, u₂.gpr, u₂.other .s0 (by decide), u₁.gpr, u₁.other .s0 (by decide), hw.s0, h1]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.reducePow]
    rw [Nat.mod_eq_of_lt (by omega : j < 18446744073709551616),
      Nat.mod_eq_of_lt (by omega : j / 32 * 8 < 18446744073709551616),
      Nat.mod_eq_of_lt (by omega : 8 * (j / 32) < 18446744073709551616)]
    omega
  have e₃ : ∀ d, s₃.gpr .t1 + BitVec.ofNat 64 d = off base (d + 8 * (j / 32)) := by
    intro d
    rw [e₃', BitVec.add_assoc, BitVec.ofNat_add_ofNat, off, Nat.add_comm]
  have r₃ : Rest [.t1] s s₃ := (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans (u₃.rest (by decide)))
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have inr : ∀ d, d + 8 ≤ 8192 → InRegions (s₃.rd ++ s₃.wr) (off base d) 8 := fun d hd =>
    ⟨_, List.mem_append_right _ (r₃.wr ▸ hw.wr), Offset.contains_base base hd (by omega)⟩
  have alg : ∀ d, d % 8 = 0 → d < 8192 → (off base d).toNat % 8 = 0 := fun d h8 hd => by
    simp only [off]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hUU : p256.sl UU = 1120 := rfl
  have hVV : p256.sl VV = 1216 := rfl
  refine wp_ld (by decide) (e₃ (p256.sl UU)) (alg _ (by rw [hUU]; omega) (by rw [hUU]; omega))
    (inr _ (by rw [hUU]; omega)) fun s₄ u₄ => ?_
  refine wp_ld (by decide) (by rw [u₄.other .t1 (by decide)]; exact e₃ (p256.sl VV))
    (alg _ (by rw [hVV]; omega) (by rw [hVV]; omega)) (by rw [u₄.rd, u₄.wr]; exact inr _ (by rw [hVV]; omega))
    fun s₅ u₅ => ?_
  refine wp_sll (by decide) fun s₆ u₆ => wp_srlReg fun s₇ u₇ => wp_srlReg fun s₈ u₈ => ?_
  refine wp_andi (by decide) fun s₉ u₉ => wp_andi (by decide) fun s₁₀ u₁₀ => wp_sll (by decide) fun s₁₁ u₁₁ => ?_
  refine wp_or fun s₁₂ u₁₂ => WP.block_nil ⟨?_, ?_, ?_⟩
  · have t0₆ : (s₆.gpr .t0).toNat % 64 = 2 * j % 64 := by
      rw [u₆.gpr, u₅.other .s1 (by decide), u₄.other .s1 (by decide), r₃.gpr .s1 (by decide), h1,
        BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
      simp only [Nat.shiftLeft_eq, Nat.reducePow]
      omega
    have t0₇ : (s₇.gpr .t0).toNat % 64 = 2 * j % 64 := by rw [u₇.other .t0 (by decide)]; exact t0₆
    have hu := two_bits (s₄.gpr .t2) (wordsVal s.mem base (p256.sl UU) 4) (j := j)
      (by
        rw [u₄.gpr, m₃, BitVec.getLsbD, ← testBit_wordsVal s.mem base 4 (p256.sl UU) (2 * j) (by omega),
          show 2 * j / 64 = j / 32 by omega, Nat.add_comm])
      (by
        rw [u₄.gpr, m₃, BitVec.getLsbD, show 2 * j % 64 + 1 = (2 * j + 1) % 64 by omega,
          ← testBit_wordsVal s.mem base 4 (p256.sl UU) (2 * j + 1) (by omega),
          show (2 * j + 1) / 64 = j / 32 by omega, Nat.add_comm])
    have hv := two_bits (s₅.gpr .t3) (wordsVal s.mem base (p256.sl VV) 4) (j := j)
      (by
        rw [u₅.gpr, u₄.mem, m₃, BitVec.getLsbD, ← testBit_wordsVal s.mem base 4 (p256.sl VV) (2 * j) (by omega),
          show 2 * j / 64 = j / 32 by omega, Nat.add_comm])
      (by
        rw [u₅.gpr, u₄.mem, m₃, BitVec.getLsbD, show 2 * j % 64 + 1 = (2 * j + 1) % 64 by omega,
          ← testBit_wordsVal s.mem base 4 (p256.sl VV) (2 * j + 1) (by omega),
          show (2 * j + 1) / 64 = j / 32 by omega, Nat.add_comm])
    have a₁₀ : s₁₀.gpr .t2 = BitVec.ofNat 64 ((wordsVal s.mem base (p256.sl UU) 4 >>> (2 * j)) % 4) := by
      rw [u₁₀.other .t2 (by decide), u₉.gpr, u₈.other .t2 (by decide), u₇.gpr, t0₆, u₆.other .t2 (by decide),
        u₅.other .t2 (by decide), hu]
    have b₁₀ : s₁₀.gpr .t3 = BitVec.ofNat 64 ((wordsVal s.mem base (p256.sl VV) 4 >>> (2 * j)) % 4) := by
      rw [u₁₀.gpr, u₉.other .t3 (by decide), u₈.gpr, t0₇, u₇.other .t3 (by decide), u₆.other .t3 (by decide), hv]
    rw [u₁₂.gpr, u₁₁.gpr, u₁₁.other .t3 (by decide), a₁₀, b₁₀]
    exact combine4 _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide))
  · exact (r₃.mono (by decide)).trans ((u₄.rest (by decide)).trans ((u₅.rest (by decide)).trans
      ((u₆.rest (by decide)).trans ((u₇.rest (by decide)).trans ((u₈.rest (by decide)).trans
        ((u₉.rest (by decide)).trans ((u₁₀.rest (by decide)).trans ((u₁₁.rest (by decide)).trans
          (u₁₂.rest (by decide))))))))))
  · rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, m₃]

/-! ## The entry -/

open VG.Proof.Ecdsa.RISCV64.Comb (tree_ok maskOfBit_ok)
open VG.Impl.Ecdsa.RISCV64.Comb (maskReg treeRegs)

/-- Quadword `q` of entry `t % 16`, to `E`'s word `q`. -/
theorem scanWordJ_ok {s : State} {base : Addr} (hw : WsReg s base) {q t : Nat} (hq : q < 12)
    (hm : ∀ c < 4, s.gpr (maskReg c) = maskOf (t.testBit c)) (h0 : s.gpr .a0 = base + BitVec.ofNat 64 2048) :
    WP isa (.block (Cfg.scanWord p256 q)) s fun s' =>
      s'.mem = s.mem.writeW (off base (1920 + 8 * q)) (word s.mem base (2048 + 8 * q + 96 * (t % 16))) ∧
      Keep treeRegs s s' := by
  have hn := hw.nowrap
  have hal := hw.al
  have hjb : Cfg.jb p256 = 96 := rfl
  have hEX : p256.sl EX = 1920 := rfl
  unfold Cfg.scanWord
  rw [hjb, hEX]
  have hne : ∀ r ∈ treeRegs, r ≠ .a0 ∧ ∀ c < 4, r ≠ maskReg c := by
    intro r hr
    simp only [treeRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨?_, fun c hc => ?_⟩
    · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · have : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have ea : ∀ e, s.gpr .a0 + BitVec.ofNat 64 (8 * q + 96 * e) = off base (2048 + 8 * q + 96 * e) := by
    intro e; rw [h0, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_assoc]
  refine WP.block_append (WP.mono (tree_ok .a0 96 t 4 (8 * q) .t0 [.t1, .t2, .t3, .t4, .t5, .t6] s (by decide)
    (by decide) hne hm (by omega)
    (fun e he => by
      rw [ea]
      refine ⟨by simp only [off]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega,
        ⟨_, List.mem_append_right _ hw.wr, Offset.contains_base base (by omega) (by omega)⟩⟩)) fun s₁ ⟨v₁, k₁, m₁⟩ => ?_)
  have hw₁ : WsReg s₁ base := ⟨by rw [k₁.gpr (by decide), hw.s0], by rw [k₁.2.2]; exact hw.wr, hw.nowrap, hw.al⟩
  refine sd_ws hw₁ (by omega) (by omega) fun s₂ u₂ => WP.block_nil ⟨?_, ?_⟩
  · rw [u₂.mem, m₁, v₁, ea]
  · exact ⟨fun r hr => by
      rw [u₂.gpr, k₁.gpr (by simpa only [treeRegs] using hr)],
      by rw [u₂.rd, k₁.2.1], by rw [u₂.wr, k₁.2.2]⟩

/-- The entry's `n` first quadwords to `E`. -/
theorem scansJ_ok {base : Addr} {t : Nat} : ∀ n ≤ 12, ∀ {s : State}, WsReg s base →
    s.gpr .a0 = base + BitVec.ofNat 64 2048 → (∀ c < 4, s.gpr (maskReg c) = maskOf (t.testBit c)) →
    WP isa (.block ((List.range n).flatMap (Cfg.scanWord p256))) s fun s' =>
      (∀ q < n, word s'.mem base (1920 + 8 * q) = word s.mem base (2048 + 8 * q + 96 * (t % 16))) ∧
      Outside base 1920 (8 * n) s.mem s'.mem ∧ Keep treeRegs s s'
  | 0, _, s, _, _, _ => WP.block_nil ⟨fun q hq => absurd hq (by omega), Outside.refl _ _ _ _, Keep.refl _ _⟩
  | n + 1, hn, s, hw, h0, hm => by
    have hnw := hw.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (scansJ_ok n (by omega) hw h0 hm) fun s₁ ⟨v₁, O₁, k₁⟩ => ?_)
    have ne : ∀ r ∈ [Reg.s0, .a0, .a1, .a2, .a3, .a4], r ∉ treeRegs := by decide
    have e0 : s₁.gpr .a0 = s.gpr .a0 := k₁.gpr (ne _ (by simp))
    have hw₁ : WsReg s₁ base := ⟨by rw [k₁.gpr (ne _ (by simp)), hw.s0], by rw [k₁.2.2]; exact hw.wr, hw.nowrap, hw.al⟩
    have hm₁ : ∀ c < 4, s₁.gpr (maskReg c) = maskOf (t.testBit c) := fun c hc => by
      rw [k₁.gpr (by
        have : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
        rcases this with rfl | rfl | rfl | rfl <;> decide)]
      exact hm c hc
    refine WP.mono (scanWordJ_ok hw₁ (q := n) (by omega) hm₁ (by rw [e0, h0])) fun s₂ ⟨m₂, k₂⟩ => ?_
    have ht := Nat.mod_lt t (show 16 > 0 by decide)
    have hr : word s₁.mem base (2048 + 8 * n + 96 * (t % 16)) = word s.mem base (2048 + 8 * n + 96 * (t % 16)) :=
      O₁.word (by omega) (by omega)
    have O₂ : Outside base (1920 + 8 * n) 8 s₁.mem s₂.mem := by rw [m₂]; exact writeW_outside _ _ _ (by omega)
    refine ⟨fun q hq => ?_, ?_, k₁.trans k₂ |>.mono (by simp [treeRegs])⟩
    · by_cases hqn : q < n
      · rw [O₂.word (by omega) (by omega), v₁ q hqn]
      · obtain rfl : q = n := by omega
        rw [m₂, word_writeW_self, hr]
    · exact (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))

/-- Numbers of words equal word by word. -/
theorem wordsVal_of_words {m m' : Mem} {base : Addr} : ∀ (k : Nat) {d d' : Nat},
    (∀ q < k, word m' base (d' + 8 * q) = word m base (d + 8 * q)) → wordsVal m' base d' k = wordsVal m base d k
  | 0, _, _, _ => rfl
  | k + 1, d, d', h => by
    rw [wordsVal, wordsVal, show d' = d' + 8 * 0 from rfl, show d = d + 8 * 0 from rfl, h 0 (by omega),
      wordsVal_of_words k (d := d + 8 * 0 + 8) (d' := d' + 8 * 0 + 8) fun q hq => by
        rw [show d' + 8 * 0 + 8 + 8 * q = d' + 8 * (q + 1) by omega, show d + 8 * 0 + 8 + 8 * q = d + 8 * (q + 1) by omega]
        exact h (q + 1) (by omega)]

/-- The masks of the four bits of `t2`. -/
theorem masks4_ok {s : State} :
    WP isa (.block ((List.range 4).flatMap Impl.Ecdsa.RISCV64.Comb.Cfg.maskOfBit)) s fun s' =>
      (∀ c < 4, s'.gpr (maskReg c) = maskOf ((s.gpr .t2).getLsbD c)) ∧
        Rest [.a1, .a2, .a3, .a4] s s' ∧ s'.mem = s.mem := by
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  refine maskOfBit_ok (b := 0) (by decide) fun s₁ v₁ r₁ m₁ => ?_
  refine maskOfBit_ok (b := 1) (by decide) fun s₂ v₂ r₂ m₂ => ?_
  refine maskOfBit_ok (b := 2) (by decide) fun s₃ v₃ r₃ m₃ => ?_
  refine maskOfBit_ok (b := 3) (by decide) fun s₄ v₄ r₄ m₄ => WP.block_nil ⟨?_, ?_, ?_⟩
  · simp only [maskReg] at v₁ v₂ v₃ v₄ r₁ r₂ r₃ r₄
    have t1 : s₁.gpr .t2 = s.gpr .t2 := r₁.gpr .t2 (by decide)
    have t2 : s₂.gpr .t2 = s.gpr .t2 := (r₂.gpr .t2 (by decide)).trans t1
    have t3 : s₃.gpr .t2 = s.gpr .t2 := (r₃.gpr .t2 (by decide)).trans t2
    intro c hc
    have : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> simp only [maskReg]
    · rw [r₄.gpr _ (by decide), r₃.gpr _ (by decide), r₂.gpr _ (by decide), v₁]
    · rw [r₄.gpr _ (by decide), r₃.gpr _ (by decide), v₂, t1]
    · rw [r₄.gpr _ (by decide), v₃, t2]
    · rw [v₄, t3]
  · simp only [maskReg] at r₁ r₂ r₃ r₄
    exact (r₁.mono (by decide)).trans ((r₂.mono (by decide)).trans ((r₃.mono (by decide)).trans (r₄.mono (by decide))))
  · rw [m₄, m₃, m₂, m₁]

/-- The registers `select` writes. -/
abbrev selRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a0, .a1, .a2, .a3, .a4]

/-- The window's entry to `E`. -/
theorem select_ok {s : State} {base : Addr} (hw : WsReg s base) {j : Nat} (hj : j < 128)
    (h1 : s.gpr .s1 = BitVec.ofNat 64 j) {G Q : Point W} (hT : JTab base s G Q) :
    WP isa (.block (Cfg.select p256)) s fun s' =>
      PtOk base s' (p256.pt EX EY EZ) (ent G Q ((wordsVal s.mem base (p256.sl UU) 4 >>> (2 * j)) % 4)
        ((wordsVal s.mem base (p256.sl VV) 4 >>> (2 * j)) % 4)) ∧
      Outside base 1920 96 s.mem s'.mem ∧ Rest selRegs s s' := by
  have hn := hw.nowrap
  rw [Cfg.select]
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (window_ok hw hj h1) fun s₁ ⟨v₁, r₁, m₁⟩ => ?_)
  generalize ha : (wordsVal s.mem base (p256.sl UU) 4 >>> (2 * j)) % 4 = a at v₁
  generalize hb : (wordsVal s.mem base (p256.sl VV) 4 >>> (2 * j)) % 4 = b at v₁
  have ha4 : a < 4 := ha ▸ Nat.mod_lt _ (by decide)
  have hb4 : b < 4 := hb ▸ Nat.mod_lt _ (by decide)
  have hw₁ := hw.of_rest r₁
  refine WP.block_append (WP.mono masks4_ok fun s₂ ⟨v₂, r₂, m₂⟩ => ?_)
  have hw₂ := hw₁.of_rest r₂
  rw [List.cons_append, List.cons_append, List.nil_append]
  refine wp_addi (by decide) fun s₃ u₃ => wp_addi (by decide) fun s₄ u₄ => ?_
  have r₄ : Rest [.a0] s₂ s₄ := (u₃.rest (by decide)).trans (u₄.rest (by decide))
  have hw₄ := hw₂.of_rest r₄
  have h0 : s₄.gpr .a0 = base + BitVec.ofNat 64 2048 := by
    rw [u₄.gpr, u₃.gpr, r₂.gpr _ (by decide), r₁.gpr _ (by decide), hw.s0, BitVec.add_assoc]; rfl
  have hm : ∀ c < 4, s₄.gpr (maskReg c) = maskOf ((4 * a + b).testBit c) := fun c hc => by
    rw [r₄.gpr _ (by
      have : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl <;> decide), v₂ c hc, v₁, BitVec.getLsbD_ofNat]
    simp [show c < 64 by omega]
  refine WP.mono (WP.rdwr (scansJ_ok 12 (Nat.le_refl _) hw₄ h0 hm)) fun s₅ ⟨⟨v₅, O₅, k₅⟩, rd₅, wr₅, sp₅⟩ => ?_
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, m₂, m₁]
  rw [m₄] at v₅ O₅
  have ht : (4 * a + b) % 16 = 4 * a + b := Nat.mod_eq_of_lt (by omega)
  rw [ht] at v₅
  have he : PtOk base s (entPt (4 * a + b)) (ent G Q ((4 * a + b) / 4) ((4 * a + b) % 4)) := hT (4 * a + b) (by omega)
  have e₁ : (4 * a + b) / 4 = a := by omega
  have e₂ : (4 * a + b) % 4 = b := by omega
  rw [e₁, e₂] at he
  have wv : ∀ c < 3, wordsVal s₅.mem base (1920 + 32 * c) 4 = wordsVal s.mem base (2048 + 96 * (4 * a + b) + 32 * c) 4 :=
    fun c hc => wordsVal_of_words 4 fun q hq => by
      rw [show 1920 + 32 * c + 8 * q = 1920 + 8 * (4 * c + q) by omega, v₅ _ (by omega)]
      congr 1; omega
  refine ⟨he.move (wv 0 (by decide)) (wv 1 (by decide)) (wv 2 (by decide)), O₅.mono (Nat.le_refl _) (by omega), ?_⟩
  exact ((r₁.mono (by decide)).trans ((r₂.mono (by decide)).trans ((r₄.mono (by decide)).trans
    ⟨fun r hr => k₅.1 r (fun h => hr ((by decide : ∀ r ∈ treeRegs, r ∈ selRegs) r h)),
      rd₅, wr₅, sp₅⟩)))

/-! ## The steps -/

/-- What the steps read, as the loop's start `s₀` holds it. -/
structure LPre (base : Addr) (s₀ : State) (G Q : Point W) (u v : Nat) : Prop where
  ap : wordsVal s₀.mem base (p256.sl AP) 4 = W.a * 2 ^ 256 % W.p
  bp : wordsVal s₀.mem base (p256.sl B3P) 4 = 3 * W.b * 2 ^ 256 % W.p
  uu : wordsVal s₀.mem base (p256.sl UU) 4 = u
  vv : wordsVal s₀.mem base (p256.sl VV) 4 = v
  tab : JTab base s₀ G Q
  g : onCurve W G = true
  q : onCurve W Q = true

/-- What the steps write. -/
abbrev stepW : List (Nat × Nat) := [(512, 480), (1920, 96), (3840, 256)]

/-- The loop's invariant at `s1 = j`: `R` represents `[u >>> 2 j]G + [v >>> 2 j]Q`. -/
structure LInv (base : Addr) (s₀ s : State) (G Q : Point W) (u v j : Nat) : Prop where
  ws : WsReg s base
  ctr : s.gpr .s1 = BitVec.ofNat 64 j
  keep : Kc s₀ s
  unch : Unch base stepW s₀.mem s.mem
  rep : PtOk base s (p256.pt RX RY RZ) (jp G Q u v j)

/-- The table, kept by memory unchanged there. -/
theorem JTab.of_eq {base : Addr} {s s' : State} {G Q : Point W} (h : JTab base s G Q)
    (he : ∀ d, 2048 ≤ d → d + 32 ≤ 3584 → wordsVal s'.mem base d 4 = wordsVal s.mem base d 4) : JTab base s' G Q :=
  fun e hlt => (h e hlt).of_eq (he (2048 + 96 * e) (by omega) (by omega)) (he (2048 + 96 * e + 32) (by omega) (by omega))
    (he (2048 + 96 * e + 64) (by omega) (by omega))

/-- A step: from `[u >>> 2 j]G + [v >>> 2 j]Q` to `[u >>> 2 (j - 1)]G + [v >>> 2 (j - 1)]Q`. -/
theorem step_ok (hL : Law W) {base : Addr} {s₀ : State} {G Q : Point W} {u v : Nat} (hP : LPre base s₀ G Q u v)
    {j : Nat} (hj1 : 1 ≤ j) (hj : j ≤ 128) {s : State} (hI : LInv base s₀ s G Q u v j) :
    WP isa (Cfg.step p256) s fun s' => LInv base s₀ s' G Q u v (j - 1) := by
  have hn := hI.ws.nowrap
  have uS : ∀ d, (d + 32 ≤ 512 ∨ 992 ≤ d) → (d + 32 ≤ 1920 ∨ 2016 ≤ d) → d + 32 ≤ 3840 →
      wordsVal s.mem base d 4 = wordsVal s₀.mem base d 4 := fun d h1 h2 h3 =>
    hI.unch.wordsVal (by simp; omega) (by omega)
  have hT : JTab base s G Q := hP.tab.of_eq fun d h1 h2 => uS d (by omega) (by omega) (by omega)
  rw [Cfg.step]
  refine WP.seq (wp_decCounter hj1 hI.ctr fun s₁ u₁ => ?_)
  have hw₁ := hI.ws.of_kc (Kc.of_rest (u₁.rest (ws := [.s1]) (by decide)))
  refine WP.mono (select_ok hw₁ (j := j - 1) (by omega) u₁.gpr (hT.of_eq fun d _ _ => by rw [u₁.mem]))
    fun s₂ ⟨pE, O₂, r₂⟩ => ?_
  rw [u₁.mem, uS _ (by decide) (by decide) (by decide), uS _ (by decide) (by decide) (by decide), hP.uu, hP.vv] at pE
  rw [u₁.mem] at O₂
  have hw₂ := hw₁.of_rest r₂
  have e₂ : ∀ d, (d + 32 ≤ 512 ∨ 992 ≤ d) → (d + 32 ≤ 1920 ∨ 2016 ≤ d) → d + 32 ≤ 3840 →
      wordsVal s₂.mem base d 4 = wordsVal s₀.mem base d 4 := fun d h1 h2 h3 => by
    rw [O₂.wordsVal (by omega) (by omega), uS d h1 h2 h3]
  have pR₂ : PtOk base s₂ (p256.pt RX RY RZ) (jp G Q u v j) :=
    hI.rep.of_eq (O₂.wordsVal (by decide) (by decide)) (O₂.wordsVal (by decide) (by decide))
      (O₂.wordsVal (by decide) (by decide))
  have ap₂ : wordsVal s₂.mem base (p256.sl AP) 4 = W.a * 2 ^ 256 % W.p := by
    rw [e₂ _ (by decide) (by decide) (by decide)]; exact hP.ap
  have bp₂ : wordsVal s₂.mem base (p256.sl B3P) 4 = 3 * W.b * 2 ^ 256 % W.p := by
    rw [e₂ _ (by decide) (by decide) (by decide)]; exact hP.bp
  have hX := ent_curve hL hP.g hP.q (u >>> (2 * j)) (v >>> (2 * j))
  have hD := hL.onCurve_add hX hX
  have hT4 := hL.onCurve_add hD hD
  have hE := ent_curve hL hP.g hP.q ((u >>> (2 * (j - 1))) % 4) ((v >>> (2 * (j - 1))) % 4)
  -- `D = R + R`.
  refine WP.seq (WP.mono (addPt_ok hL hw₂ ap₂ bp₂ (p := p256.pt RX RY RZ) (q := p256.pt RX RY RZ)
    (o := p256.pt DX DY DZ) ⟨by decide, by decide⟩ (by decide) hX hX pR₂ pR₂) fun s₃ ⟨K₃, U₃, pD⟩ => ?_)
  have hw₃ := hw₂.of_kp K₃
  have k₃ : ∀ d ∈ [p256.sl AP, p256.sl B3P, p256.sl EX, p256.sl EY, p256.sl EZ],
      wordsVal s₃.mem base d 4 = wordsVal s₂.mem base d 4 := keepU U₃ (by decide)
  -- `T = D + D`.
  refine WP.seq (WP.mono (addPt_ok hL hw₃ ((k₃ _ (by decide)).trans ap₂) ((k₃ _ (by decide)).trans bp₂)
    (p := p256.pt DX DY DZ) (q := p256.pt DX DY DZ) (o := p256.pt TX TY TZ) ⟨by decide, by decide⟩ (by decide)
    hD hD pD pD) fun s₄ ⟨K₄, U₄, pT⟩ => ?_)
  have hw₄ := hw₃.of_kp K₄
  have k₄ : ∀ d ∈ [p256.sl AP, p256.sl B3P, p256.sl EX, p256.sl EY, p256.sl EZ],
      wordsVal s₄.mem base d 4 = wordsVal s₃.mem base d 4 := keepU U₄ (by decide)
  have pE₄ := pE.of_eq ((k₄ _ (by decide)).trans (k₃ _ (by decide))) ((k₄ _ (by decide)).trans (k₃ _ (by decide)))
    ((k₄ _ (by decide)).trans (k₃ _ (by decide)))
  -- `R = T + E`.
  refine WP.mono (addPt_ok hL hw₄ (((k₄ _ (by decide)).trans (k₃ _ (by decide))).trans ap₂)
    (((k₄ _ (by decide)).trans (k₃ _ (by decide))).trans bp₂)
    (p := p256.pt TX TY TZ) (q := p256.pt EX EY EZ) (o := p256.pt RX RY RZ) ⟨by decide, by decide⟩ (by decide)
    hT4 hE pT pE₄) fun s₅ ⟨K₅, U₅, pR₅⟩ => ?_
  refine ⟨hw₄.of_kp K₅, ?_, ?_, ?_, ?_⟩
  · rw [K₅.gpr _ (by decide), K₄.gpr _ (by decide), K₃.gpr _ (by decide), r₂.gpr _ (by decide), u₁.gpr]
  · exact ((hI.keep.trans (Kc.of_rest (u₁.rest (ws := [.s1]) (by decide)))).trans (Kc.of_rest r₂)).trans
      (K₃.kc.trans (K₄.kc.trans K₅.kc))
  · exact ((((hI.unch.trans (show Unch base [(1920, 96)] s.mem s₂.mem from O₂.unch)).trans U₃).trans U₄).trans
      U₅).cover (by decide)
  · have e := jstep hL hP.g hP.q u v (j - 1)
    rw [show j - 1 + 1 = j by omega] at e
    rw [← e]
    exact pR₅

/-! ## The joint ladder -/

/-- What `joint` writes. -/
abbrev jointW : List (Nat × Nat) := [(512, 480), (1536, 480), (2048, 1536), (3840, 256)]

/-- `R = [u]G + [v]Q`, for `u` and `v` in their slots and `Q` in the check's. -/
theorem joint_ok (hL : Law W) {base : Addr} {s : State} {Q : Point W} (hp : JPre base s Q) :
    WP isa (Cfg.joint p256) s fun s' => Kc s s' ∧ Unch base jointW s.mem s'.mem ∧
      PtOk base s' (p256.pt RX RY RZ) (Spec.Weierstrass.add (mul (wordsVal s.mem base (p256.sl UU) 4)
        (Spec.Weierstrass.G W)) (mul (wordsVal s.mem base (p256.sl VV) 4) Q)) := by
  have hn := hp.ws.nowrap
  have hp0 : 0 < W.p := by decide
  rw [Cfg.joint]
  refine WP.seq (WP.mono (build_ok hL hp) fun s₁ ⟨K₁, U₁, T₁⟩ => ?_)
  have hw₁ := hp.ws.of_kp K₁
  have e₁ : ∀ d ∈ [p256.sl ZERO, p256.sl ONEP, p256.sl AP, p256.sl B3P, p256.sl UU, p256.sl VV],
      wordsVal s₁.mem base d 4 = wordsVal s.mem base d 4 := keepU U₁ (by decide)
  rw [show p256.n = 4 from rfl]
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (copy_ok 4 hw₁ (o := p256.sl RX) (a := p256.sl ZERO) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₂ ⟨x₂, r₂, O₂⟩ => ?_))
  have hw₂ := hw₁.of_rest r₂
  refine WP.block_append (WP.mono (copy_ok 4 hw₂ (o := p256.sl RY) (a := p256.sl ONEP) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₃ ⟨y₃, r₃, O₃⟩ => ?_)
  have hw₃ := hw₂.of_rest r₃
  refine WP.block_append (WP.mono (copy_ok 4 hw₃ (o := p256.sl RZ) (a := p256.sl ZERO) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₄ ⟨z₄, r₄, O₄⟩ => ?_)
  have hw₄ := hw₃.of_rest r₄
  refine wp_li (imm := 128) (by decide) fun s₅ u₅ => WP.block_nil ?_
  have r₅ : Rest [.t0, .s1] s₁ s₅ :=
    ((r₂.trans (r₃.trans r₄)).mono (by decide)).trans (u₅.rest (by decide))
  have hw₅ : WsReg s₅ base := hw₄.of_kc (Kc.of_rest (u₅.rest (ws := [.s1]) (by decide)))
  have U₅ : Unch base [(512, 96)] s₁.mem s₅.mem := by
    rw [u₅.mem]
    exact ((O₂.unch.trans O₃.unch).trans O₄.unch).cover (by decide)
  have e₅ : ∀ d ∈ [p256.sl ZERO, p256.sl ONEP, p256.sl AP, p256.sl B3P, p256.sl UU, p256.sl VV],
      wordsVal s₅.mem base d 4 = wordsVal s.mem base d 4 := fun d hd =>
    (keepU U₅ (D := [p256.sl ZERO, p256.sl ONEP, p256.sl AP, p256.sl B3P, p256.sl UU, p256.sl VV]) (by decide) d hd).trans
      (e₁ d hd)
  have T₅ : JTab base s₅ (Spec.Weierstrass.G W) Q := T₁.of_eq fun d h1 h2 => U₅.wordsVal (by simp; omega) (by omega)
  -- The start: `R = O`.
  generalize hu : wordsVal s.mem base (p256.sl UU) 4 = u
  generalize hv : wordsVal s.mem base (p256.sl VV) 4 = v
  have hu' : u < 2 ^ 256 := hu ▸ wordsVal_lt _ _ _ _
  have hv' : v < 2 ^ 256 := hv ▸ wordsVal_lt _ _ _ _
  have hP : LPre base s₅ (Spec.Weierstrass.G W) Q u v :=
    ⟨(e₅ _ (by decide)).trans hp.ap, (e₅ _ (by decide)).trans hp.bp, (e₅ _ (by decide)).trans hu,
      (e₅ _ (by decide)).trans hv, T₅, VG.Proof.P256.onCurve_G, hp.on⟩
  have rx : wordsVal s₅.mem base (p256.sl RX) 4 = 0 := by
    rw [u₅.mem, O₄.wordsVal (by decide) (by decide), O₃.wordsVal (by decide) (by decide), x₂,
      e₁ _ (by decide), hp.zero]
  have ry : wordsVal s₅.mem base (p256.sl RY) 4 = 1 * 2 ^ 256 % W.p := by
    rw [u₅.mem, O₄.wordsVal (by decide) (by decide), y₃, O₂.wordsVal (by decide) (by decide),
      e₁ _ (by decide), hp.onep]
  have rz : wordsVal s₅.mem base (p256.sl RZ) 4 = 0 := by
    rw [u₅.mem, z₄, O₃.wordsVal (by decide) (by decide), O₂.wordsVal (by decide) (by decide),
      e₁ _ (by decide), hp.zero]
  have hI : LInv base s₅ s₅ (Spec.Weierstrass.G W) Q u v 128 := by
    refine ⟨hw₅, u₅.gpr, ⟨fun _ _ _ => rfl, rfl, rfl, rfl⟩, Unch.refl _ _ _, ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [jp_top _ _ hu' hv']
      show Rep W (tmv W 4 base s₅ (p256.sl RX)) (tmv W 4 base s₅ (p256.sl RY)) (tmv W 4 base s₅ (p256.sl RZ)) _
      simp only [tmv]
      rw [rx, ry, rz, toM_zero, Nat.one_mul, toM_one unit]
      exact rep_infinity' hL
    · show wordsVal _ _ (p256.sl RX) 4 < _; rw [rx]; exact hp0
    · show wordsVal _ _ (p256.sl RY) 4 < _; rw [ry]; exact Nat.mod_lt _ hp0
    · show wordsVal _ _ (p256.sl RZ) 4 < _; rw [rz]; exact hp0
  -- The steps.
  refine countLoop_ok (Inv := fun j s' => LInv base s₅ s' (Spec.Weierstrass.G W) Q u v j) (n := 128)
    (fun j s' hi => hi.ctr) (fun j s' h1 h2 hi => step_ok hL hP h1 h2 hi) (fun s' hi => ?_) (by decide) (by decide) hI
  refine ⟨(K₁.kc.trans (Kc.of_rest r₅)).trans hi.keep, ((U₁.trans U₅).trans hi.unch).cover (by decide), ?_⟩
  rw [← jp_zero]
  exact hi.rep

end VG.Proof.Ecdsa.RISCV64.Joint
