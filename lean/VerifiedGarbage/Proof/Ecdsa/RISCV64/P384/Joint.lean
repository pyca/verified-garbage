module

-- separate module: its proofs (about 7 s) cost more than its imports, and its importer's
-- changes need not re-check them

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Verify
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Joint.Table
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Comb.Main
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.MulFn
public import VerifiedGarbage.Proof.Weierstrass.Joint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.P384.Point
import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder

/-!
# ECDSA verification over P-384 on RISC-V: the joint ladder

`joint` (`Impl/Ecdsa/RISCV64/Verify.lean`) leaves in `R` a representative of
`[u]G + [v]Q` (`joint_ok`):

* `copyTo_ok`, `storePt_ok`: a point's slots to an entry of the table, through
  `a6 = s0 + JT`;
* `build_ok`: the table (`JTab`: entry `4 a + b` represents `[a]G + [b]Q`);
* `window_ok`, `select_ok`: the window's entry number `4 u_j + v_j`, its
  masks, and the entry to `E`, by the comb's tree (`tree_ok`);
* `step_ok`: `R = 4 R + E`, from `[u >>> 2 (j + 1)]G + [v >>> 2 (j + 1)]Q` to
  `[u >>> 2 j]G + [v >>> 2 j]Q` (`jstep`);
* `joint_ok`: the table, `R = O`, and the 192 steps.
-/

@[expose] public section

-- `p`, below `2^384`, is evaluated.
set_option exponentiation.threshold 512

namespace VG.Proof.Ecdsa.RISCV64.P384.Joint

open VG VG.RISCV64 VG.RISCV64.Steps VG.Proof.Mont VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdsa.RISCV64.Verify
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdh.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.Ecdsa.RISCV64.P384 (W field_ok unit)
open VG.Proof.Ecdsa.RISCV64.Joint
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Point mul onCurve)
open VG.Impl.Ecdsa.RISCV64.Comb (maskReg treeRegs)

/-! ## The complete additions -/

/-- A point in the slots `p`: its coordinates below `p`, representing `P`. -/
structure PtOk (base : Addr) (s : State) (p : Pt) (P : Point W) : Prop where
  rep : Rep W (tmv W 6 base s p.x) (tmv W 6 base s p.y) (tmv W 6 base s p.z) P
  x : wordsVal s.mem base p.x 6 < W.p
  y : wordsVal s.mem base p.y 6 < W.p
  z : wordsVal s.mem base p.z 6 < W.p

/-- The slots of the joint ladder's additions. -/
abbrev jSl : List Nat :=
  [p384.sl AP, p384.sl B3P, p384.sl T0, p384.sl T1, p384.sl T2, p384.sl T3, p384.sl T4, p384.sl T5,
    p384.sl RX, p384.sl RY, p384.sl RZ, p384.sl DX, p384.sl DY, p384.sl DZ, p384.sl TX, p384.sl TY, p384.sl TZ,
    p384.sl GX, p384.sl GY, p384.sl ONEP, p384.sl CPX, p384.sl CPY,
    p384.sl G2X, p384.sl G2Y, p384.sl G2Z, p384.sl G3X, p384.sl G3Y, p384.sl G3Z,
    p384.sl Q2X, p384.sl Q2Y, p384.sl Q2Z, p384.sl Q3X, p384.sl Q3Y, p384.sl Q3Z,
    p384.sl EX, p384.sl EY, p384.sl EZ]

theorem jLay : Lay p384.MP' (own 6) (· ∈ jSl) :=
  ⟨by decide, fun x y hx hy => (by decide : ∀ x ∈ jSl, ∀ y ∈ jSl, x ≠ y → x + 8 * 6 ≤ y ∨ y + 8 * 6 ≤ x)
    x hx y hy, by decide, by decide⟩

theorem jShort : Short (· ∈ jSl) := by decide

/-- What the additions write. -/
abbrev addW (o : Pt) : List (Nat × Nat) :=
  (rcbW p384.rcbSlots o).map (fun w => (w, 8 * 6)) ++ [(own 6, 64 * 6)]

/-- `o = p + q` by the complete addition, for points in slots of `jSl`. -/
theorem addPt_ok (hL : Law W) {base : Addr} {s : State} (hw : WsReg s base)
    (hap : wordsVal s.mem base (p384.sl AP) 6 = W.a * 2 ^ 384 % W.p)
    (hbp : wordsVal s.mem base (p384.sl B3P) 6 = 3 * W.b * 2 ^ 384 % W.p)
    {p q o : Pt} (hA : RcbApart p384.rcbSlots p q o)
    (hsl : ∀ x ∈ rcbW p384.rcbSlots o ++ rcbR p384.rcbSlots p q, x ∈ jSl)
    {P P' : Point W} (hP : onCurve W P = true) (hP' : onCurve W P' = true)
    (hp : PtOk base s p P) (hq : PtOk base s q P') :
    WP isa (Cfg.addPt p384 p q o) s fun s' =>
      Kp s s' ∧ Unch base (addW o) s.mem s'.mem ∧ PtOk base s' o (Spec.Weierstrass.add P P') := by
  have hp0 : 0 < W.p := by decide
  rw [Cfg.addPt]
  have hI : Inv 6 base W.p (· ∈ jSl) (rcbR p384.rcbSlots p q)
      (fun x => toM W.p (2 ^ (64 * 6)) (wordsVal s.mem base x 6)) s := by
    refine ⟨hw, fun x hx => hsl x (List.mem_append_right _ hx), fun x hx => ?_, fun x _ => rfl⟩
    simp only [rcbR, Cfg.rcbSlots, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hap]; exact Nat.mod_lt _ hp0
    · rw [hbp]; exact Nat.mod_lt _ hp0
    exacts [hp.x, hp.y, hp.z, hq.x, hq.y, hq.z]
  refine WP.mono (rcb_ok (F := p384Field) field_ok rfl jLay jShort unit hA hsl hI (fun x hx => hx))
    fun s₁ ⟨k₁, I₁, t₁, _⟩ => ?_
  have ea : toM W.p (2 ^ (64 * 6)) (wordsVal s.mem base (p384.sl AP) 6) = Fin.ofNat W.p W.a := by
    rw [hap, toM_mont unit]
  have eb : toM W.p (2 ^ (64 * 6)) (wordsVal s.mem base (p384.sl B3P) 6) = Fin.ofNat W.p (3 * W.b) := by
    rw [hbp, toM_mont unit]
  generalize hE : (fun x => toM W.p (2 ^ (64 * 6)) (wordsVal s.mem base x 6)) = E at I₁ t₁
  have hrep := hL.add hP hP' hp.rep hq.rep (X3 := runOps (rcb p384.rcbSlots p q o) E o.x)
    (Y3 := runOps (rcb p384.rcbSlots p q o) E o.y) (Z3 := runOps (rcb p384.rcbSlots p q o) E o.z)
    (by
      subst hE
      show rcbAdd (Fin.ofNat W.p W.a) (Fin.ofNat W.p (3 * W.b)) _ _ _ _ _ _ = _
      rw [← ea, ← eb]
      exact t₁.symm)
  have hm : ∀ x ∈ [o.x, o.y, o.z], x ∈ rcbW p384.rcbSlots o ++ rcbR p384.rcbSlots p q := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [rcbW]
  refine ⟨k₁.kp, k₁.mem, ⟨?_, I₁.lt _ (hm _ (by simp)), I₁.lt _ (hm _ (by simp)), I₁.lt _ (hm _ (by simp))⟩⟩
  have vx : tmv W 6 base s₁ o.x = _ := I₁.val _ (hm _ (by simp))
  have vy : tmv W 6 base s₁ o.y = _ := I₁.val _ (hm _ (by simp))
  have vz : tmv W 6 base s₁ o.z = _ := I₁.val _ (hm _ (by simp))
  rw [vx, vy, vz]
  exact hrep

theorem PtOk.of_eq {base : Addr} {s s' : State} {p : Pt} {P : Point W} (h : PtOk base s p P)
    (hx : wordsVal s'.mem base p.x 6 = wordsVal s.mem base p.x 6)
    (hy : wordsVal s'.mem base p.y 6 = wordsVal s.mem base p.y 6)
    (hz : wordsVal s'.mem base p.z 6 = wordsVal s.mem base p.z 6) : PtOk base s' p P :=
  ⟨by simp only [tmv]; rw [hx, hy, hz]; exact h.rep, hx ▸ h.x, hy ▸ h.y, hz ▸ h.z⟩

/-- A point copied to other slots. -/
theorem PtOk.move {base : Addr} {s s' : State} {p q : Pt} {P : Point W} (h : PtOk base s p P)
    (hx : wordsVal s'.mem base q.x 6 = wordsVal s.mem base p.x 6)
    (hy : wordsVal s'.mem base q.y 6 = wordsVal s.mem base p.y 6)
    (hz : wordsVal s'.mem base q.z 6 = wordsVal s.mem base p.z 6) : PtOk base s' q P :=
  ⟨by simp only [tmv]; rw [hx, hy, hz]; exact h.rep, hx ▸ h.x, hy ▸ h.y, hz ▸ h.z⟩

/-! ## The table -/

/-- Entry `e`'s coordinates. -/
abbrev entPt (e : Nat) : Pt := ⟨4096 + 144 * e, 4096 + 144 * e + 48, 4096 + 144 * e + 96⟩

/-- Entry `e` represents `[e / 4]G + [e % 4]Q`. -/
abbrev EntOk (base : Addr) (s : State) (G Q : Point W) (e : Nat) : Prop :=
  PtOk base s (entPt e) (ent G Q (e / 4) (e % 4))

/-- What the table's construction writes. -/
abbrev buildW : List (Nat × Nat) := [(1024, 432), (2272, 576), (4096, 2304), (3712, 384)]

/-- While the table is built, from `s₀`: the entries of `L`. -/
structure BS (base : Addr) (s₀ s : State) (G Q : Point W) (L : List Nat) : Prop where
  ws : WsReg s base
  kp : Kp s₀ s
  unch : Unch base buildW s₀.mem s.mem
  ap : wordsVal s.mem base (p384.sl AP) 6 = W.a * 2 ^ 384 % W.p
  bp : wordsVal s.mem base (p384.sl B3P) 6 = 3 * W.b * 2 ^ 384 % W.p
  ents : ∀ e ∈ L, e < 16 ∧ EntOk base s G Q e

/-- A point to entry `e`: the entries so far are kept, and so is every slot. -/
theorem store_ok' {base : Addr} {s₀ s : State} {G Q : Point W} {L : List Nat} (h : BS base s₀ s G Q L)
    {e : Nat} (he : e < 16) {p : Pt}
    (hx : p.x % 8 = 0 ∧ p.x + 48 ≤ 4095) (hy : p.y % 8 = 0 ∧ p.y + 48 ≤ 4095)
    (hz : p.z % 8 = 0 ∧ p.z + 48 ≤ 4095) (hp : PtOk base s p (ent G Q (e / 4) (e % 4))) :
    WP isa (.block (Cfg.storePt p384 e p)) s fun s' => BS base s₀ s' G Q (e :: L) ∧
      ∀ d, d + 48 ≤ 4095 → wordsVal s'.mem base d 6 = wordsVal s.mem base d 6 := by
  have hn := h.ws.nowrap
  refine WP.mono (storePt_ok p384 h.ws (e := e) (by decide) (by show 4096 + 144 * e + 144 ≤ 8192; omega)
    (by show 144 * e + 144 ≤ 4095; omega) ⟨hx.1, by show _ + 48 ≤ 4095; omega, by show _ + 48 ≤ 4096; omega⟩
    ⟨hy.1, by show _ + 48 ≤ 4095; omega, by show _ + 48 ≤ 4096; omega⟩
    ⟨hz.1, by show _ + 48 ≤ 4095; omega, by show _ + 48 ≤ 4096; omega⟩) fun s' ⟨ex, ey, ez, r, O⟩ => ?_
  simp only [show p384.jt = 4096 from rfl, show Cfg.jb p384 = 144 from rfl, show p384.n = 6 from rfl,
    Nat.reduceMul] at ex ey ez O
  have hd : ∀ d, d + 48 ≤ 4095 → wordsVal s'.mem base d 6 = wordsVal s.mem base d 6 := fun d hd =>
    O.wordsVal (by omega) (by omega)
  refine ⟨⟨h.ws.of_rest r, h.kp.trans (Kp.of_rest r), ?_, ?_, ?_, ?_⟩, hd⟩
  · refine (h.unch.trans O.unch).cover fun w hw => ?_
    rcases List.mem_append.mp hw with hw | hw
    · exact ⟨w, hw, Nat.le_refl _, Nat.le_refl _⟩
    · rw [List.mem_singleton] at hw
      subst hw
      exact ⟨(4096, 2304), List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
        by show 4096 ≤ 4096 + 144 * e; omega, by show 4096 + 144 * e + 144 ≤ 4096 + 2304; omega⟩
  · rw [hd (p384.sl AP) (by show 352 + 48 ≤ 4095; omega)]; exact h.ap
  · rw [hd (p384.sl B3P) (by show 400 + 48 ≤ 4095; omega)]; exact h.bp
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
        · exact O.wordsVal (d := 4096 + 144 * e') (by rcases h1 with h1 | h1 <;> omega) (by omega)
        · exact O.wordsVal (d := 4096 + 144 * e' + 48) (by rcases h1 with h1 | h1 <;> omega) (by omega)
        · exact O.wordsVal (d := 4096 + 144 * e' + 96) (by rcases h1 with h1 | h1 <;> omega) (by omega)

/-- `o = p + q`, for `o` among the slots the construction writes: the
entries are kept. -/
theorem add_ok' (hL : Law W) {base : Addr} {s₀ s : State} {G Q : Point W} {L : List Nat}
    (h : BS base s₀ s G Q L) {p q o : Pt} (hA : RcbApart p384.rcbSlots p q o)
    (hsl : ∀ x ∈ rcbW p384.rcbSlots o ++ rcbR p384.rcbSlots p q, x ∈ jSl)
    (hW : ∀ w ∈ addW o, ∃ w' ∈ buildW, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2)
    {P P' : Point W} (hP : onCurve W P = true) (hP' : onCurve W P' = true)
    (hp : PtOk base s p P) (hq : PtOk base s q P') :
    WP isa (Cfg.addPt p384 p q o) s fun s' => BS base s₀ s' G Q L ∧
      PtOk base s' o (Spec.Weierstrass.add P P') ∧ Unch base (addW o) s.mem s'.mem := by
  have hn := h.ws.nowrap
  refine WP.mono (addPt_ok hL h.ws h.ap h.bp hA hsl hP hP' hp hq) fun s' ⟨K, U, ok⟩ => ?_
  have hd : ∀ d, (∀ w ∈ addW o, d + 48 ≤ w.1 ∨ w.1 + w.2 ≤ d) → d + 48 ≤ 8192 →
      wordsVal s'.mem base d 6 = wordsVal s.mem base d 6 := fun d h1 h2 => U.wordsVal h1 (by omega)
  have hfar : ∀ d, 4096 ≤ d → ∀ w ∈ addW o, d + 48 ≤ w.1 ∨ w.1 + w.2 ≤ d := by
    intro d h1 w hw
    have hsl' : ∀ x ∈ rcbW p384.rcbSlots o, x + 48 ≤ 4095 := fun x hx =>
      (by decide : ∀ x ∈ jSl, x + 48 ≤ 4095) x (hsl x (List.mem_append_left _ hx))
    simp only [addW, List.mem_append, List.mem_map, List.mem_singleton] at hw
    rcases hw with ⟨x, hx, rfl⟩ | rfl
    · have := hsl' x hx; right; simp only; omega
    · right; show 3712 + 384 ≤ d; omega
  refine ⟨⟨h.ws.of_kp K, h.kp.trans K, (h.unch.trans U).cover fun w hw => ?_, ?_, ?_, ?_⟩, ok, U⟩
  · rcases List.mem_append.mp hw with hw | hw
    · exact ⟨w, hw, Nat.le_refl _, Nat.le_refl _⟩
    · exact hW w hw
  · have hlow : ∀ w ∈ addW o, 1024 ≤ w.1 := fun w hw => by
      obtain ⟨w', hw', l1, l2⟩ := hW w hw
      have : 1024 ≤ w'.1 := by
        simp only [buildW, List.mem_cons, List.not_mem_nil, or_false] at hw'
        rcases hw' with rfl | rfl | rfl | rfl <;> decide
      omega
    rw [hd (p384.sl AP) (fun w hw => .inl (by have := hlow w hw; show 352 + 48 ≤ w.1; omega))
      (by show 352 + 48 ≤ 8192; omega)]
    exact h.ap
  · have hlow : ∀ w ∈ addW o, 1024 ≤ w.1 := fun w hw => by
      obtain ⟨w', hw', l1, l2⟩ := hW w hw
      have : 1024 ≤ w'.1 := by
        simp only [buildW, List.mem_cons, List.not_mem_nil, or_false] at hw'
        rcases hw' with rfl | rfl | rfl | rfl <;> decide
      omega
    rw [hd (p384.sl B3P) (fun w hw => .inl (by have := hlow w hw; show 400 + 48 ≤ w.1; omega))
      (by show 400 + 48 ≤ 8192; omega)]
    exact h.bp
  · intro e he
    obtain ⟨hlt, hok⟩ := h.ents e he
    exact ⟨hlt, hok.of_eq (hd (4096 + 144 * e) (hfar _ (by omega)) (by omega))
      (hd (4096 + 144 * e + 48) (hfar _ (by omega)) (by omega))
      (hd (4096 + 144 * e + 96) (hfar _ (by omega)) (by omega))⟩

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
  ap : wordsVal s.mem base (p384.sl AP) 6 = W.a * 2 ^ 384 % W.p
  bp : wordsVal s.mem base (p384.sl B3P) 6 = 3 * W.b * 2 ^ 384 % W.p
  zero : wordsVal s.mem base (p384.sl ZERO) 6 = 0
  onep : wordsVal s.mem base (p384.sl ONEP) 6 = 1 * 2 ^ 384 % W.p
  gx : wordsVal s.mem base (p384.sl GX) 6 = W.gx * 2 ^ 384 % W.p
  gy : wordsVal s.mem base (p384.sl GY) 6 = W.gy * 2 ^ 384 % W.p
  qx : wordsVal s.mem base (p384.sl CPX) 6 < W.p
  qy : wordsVal s.mem base (p384.sl CPY) 6 < W.p
  q : Point.affine (tmv W 6 base s (p384.sl CPX)) (tmv W 6 base s (p384.sl CPY)) = Q
  on : onCurve W Q = true

/-- The coordinates of the multiples of `G` and `Q` in slots. -/
abbrev gqSl : List Nat :=
  [p384.sl GX, p384.sl GY, p384.sl ONEP, p384.sl CPX, p384.sl CPY,
    p384.sl G2X, p384.sl G2Y, p384.sl G2Z, p384.sl G3X, p384.sl G3Y, p384.sl G3Z,
    p384.sl Q2X, p384.sl Q2Y, p384.sl Q2Z, p384.sl Q3X, p384.sl Q3Y, p384.sl Q3Z]

theorem gPt_sl : ∀ a ∈ [1, 2, 3], (Cfg.gPt p384 a).x ∈ gqSl ∧ (Cfg.gPt p384 a).y ∈ gqSl ∧
    (Cfg.gPt p384 a).z ∈ gqSl := by decide

theorem qPt_sl : ∀ b ∈ [1, 2, 3], (Cfg.qPt p384 b).x ∈ gqSl ∧ (Cfg.qPt p384 b).y ∈ gqSl ∧
    (Cfg.qPt p384 b).z ∈ gqSl := by decide

/-- A point in slots of `gqSl`, kept where those slots are. -/
theorem PtOk.keep {base : Addr} {s s' : State} {p : Pt} {P : Point W} (h : PtOk base s p P)
    (hk : ∀ d ∈ gqSl, wordsVal s'.mem base d 6 = wordsVal s.mem base d 6)
    (hp : p.x ∈ gqSl ∧ p.y ∈ gqSl ∧ p.z ∈ gqSl) : PtOk base s' p P :=
  h.of_eq (hk _ hp.1) (hk _ hp.2.1) (hk _ hp.2.2)

theorem keep_addT {base : Addr} {m m' : Mem} (U : Unch base (addW (p384.pt TX TY TZ)) m m') :
    ∀ d ∈ gqSl, wordsVal m' base d 6 = wordsVal m base d 6 := by
  have h : ∀ d ∈ gqSl, ∀ w ∈ addW (p384.pt TX TY TZ), d + 8 * 6 ≤ w.1 ∨ w.1 + w.2 ≤ d := by decide
  intro d hd
  exact U.wordsVal (h d hd) (by have : d < 4095 := (by decide : ∀ d ∈ gqSl, d < 4095) d hd; omega)

theorem apart_mixed' : ∀ a ∈ [1, 2, 3], ∀ b ∈ [1, 2, 3],
    ((rcbW p384.rcbSlots (p384.pt TX TY TZ)).Nodup ∧
      ∀ x ∈ rcbR p384.rcbSlots (Cfg.gPt p384 a) (Cfg.qPt p384 b), x ∉ rcbW p384.rcbSlots (p384.pt TX TY TZ)) ∧
    (∀ x ∈ rcbW p384.rcbSlots (p384.pt TX TY TZ) ++ rcbR p384.rcbSlots (Cfg.gPt p384 a) (Cfg.qPt p384 b), x ∈ jSl) :=
  by decide

theorem apart_mixed {a b : Nat} (ha : a ∈ [1, 2, 3]) (hb : b ∈ [1, 2, 3]) :
    RcbApart p384.rcbSlots (Cfg.gPt p384 a) (Cfg.qPt p384 b) (p384.pt TX TY TZ) ∧
    (∀ x ∈ rcbW p384.rcbSlots (p384.pt TX TY TZ) ++ rcbR p384.rcbSlots (Cfg.gPt p384 a) (Cfg.qPt p384 b), x ∈ jSl) :=
  have h := apart_mixed' a ha b hb
  ⟨⟨h.1.1, h.1.2⟩, h.2⟩

theorem slots_mixed : ∀ x ∈ [p384.sl TX, p384.sl TY, p384.sl TZ], x % 8 = 0 ∧ x + 48 ≤ 4095 := by decide

/-- Entry `4 a + b`, from `[a]G` and `[b]Q` in slots. -/
theorem mixed_ok (hL : Law W) {base : Addr} {s₀ s : State} {G Q : Point W} (hG : onCurve W G = true)
    (hQ : onCurve W Q = true) {L : List Nat} (h : BS base s₀ s G Q L) {a b : Nat} (ha : a ∈ [1, 2, 3])
    (hb : b ∈ [1, 2, 3]) (hpa : PtOk base s (Cfg.gPt p384 a) (mul a G))
    (hpb : PtOk base s (Cfg.qPt p384 b) (mul b Q)) :
    WP isa (Cfg.mixed p384 a b) s fun s' => BS base s₀ s' G Q ((4 * a + b) :: L) ∧
      ∀ d ∈ gqSl, wordsVal s'.mem base d 6 = wordsVal s.mem base d 6 := by
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
  rw [k₂ d (by have := (by decide : ∀ d ∈ gqSl, d + 48 ≤ 4095) d hd; exact this), k₁ d hd]

/-- The nine entries of both. -/
theorem mixeds_ok (hL : Law W) {base : Addr} {s₀ : State} {G Q : Point W} (hG : onCurve W G = true)
    (hQ : onCurve W Q = true) :
    ∀ (l : List (Nat × Nat)) {s : State} {L : List Nat}, l ≠ [] → (∀ ab ∈ l, ab.1 ∈ [1, 2, 3] ∧ ab.2 ∈ [1, 2, 3]) →
    BS base s₀ s G Q L → (∀ a ∈ [1, 2, 3], PtOk base s (Cfg.gPt p384 a) (mul a G)) →
    (∀ b ∈ [1, 2, 3], PtOk base s (Cfg.qPt p384 b) (mul b Q)) →
    WP isa (progs (l.map fun ab => Cfg.mixed p384 ab.1 ab.2)) s fun s' =>
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
    rw [show progs (Cfg.mixed p384 ab.1 ab.2 :: Cfg.mixed p384 ab'.1 ab'.2 ::
      List.map (fun ab => Cfg.mixed p384 ab.1 ab.2) l) = .seq (Cfg.mixed p384 ab.1 ab.2)
        (progs (Cfg.mixed p384 ab'.1 ab'.2 :: List.map (fun ab => Cfg.mixed p384 ab.1 ab.2) l)) from rfl]
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
    (hD : ∀ d ∈ D, (∀ w ∈ Wl, d + 8 * 6 ≤ w.1 ∨ w.1 + w.2 ≤ d) ∧ d + 48 ≤ 4095) :
    ∀ d ∈ D, wordsVal m' base d 6 = wordsVal m base d 6 := fun d hd =>
  U.wordsVal (hD d hd).1 (by have := (hD d hd).2; omega)

/-- `O`, `G` and `Q` to entries 0, 4 and 1. -/
theorem first3_ok {base : Addr} {s₀ s : State} {G Q : Point W} (h : BS base s₀ s G Q [])
    (pO : PtOk base s (p384.pt ZERO ONEP ZERO) (ent G Q (0 / 4) (0 % 4)))
    (pG : PtOk base s (Cfg.gPt p384 1) (ent G Q (4 / 4) (4 % 4)))
    (pQ : PtOk base s (Cfg.qPt p384 1) (ent G Q (1 / 4) (1 % 4))) {rest : Prog isa} {R : State → Prop}
    (k : ∀ s', BS base s₀ s' G Q [1, 4, 0] → (∀ d, d + 48 ≤ 4095 → wordsVal s'.mem base d 6 = wordsVal s.mem base d 6) →
      WP isa rest s' R) :
    WP isa (.seq (.block (Cfg.storePt p384 0 (p384.pt ZERO ONEP ZERO) ++ Cfg.storePt p384 4 (Cfg.gPt p384 1) ++
      Cfg.storePt p384 1 (Cfg.qPt p384 1))) rest) s R := by
  have sl8 : ∀ x ∈ [p384.sl ZERO, p384.sl ONEP, p384.sl GX, p384.sl GY, p384.sl CPX, p384.sl CPY],
      x % 8 = 0 ∧ x + 48 ≤ 4095 := by decide
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (store_ok' h (e := 0) (p := p384.pt ZERO ONEP ZERO) (by decide)
    (sl8 _ (by decide)) (sl8 _ (by decide)) (sl8 _ (by decide)) pO) fun s₁ ⟨h₁, k₁⟩ => ?_))
  have pG₁ := pG.of_eq (k₁ _ (by decide)) (k₁ _ (by decide)) (k₁ _ (by decide))
  refine WP.block_append (WP.mono (store_ok' h₁ (e := 4) (p := Cfg.gPt p384 1) (by decide) (sl8 _ (by decide))
    (sl8 _ (by decide)) (sl8 _ (by decide)) pG₁) fun s₂ ⟨h₂, k₂⟩ => ?_)
  have pQ₂ := pQ.of_eq ((k₂ _ (by decide)).trans (k₁ _ (by decide))) ((k₂ _ (by decide)).trans (k₁ _ (by decide)))
    ((k₂ _ (by decide)).trans (k₁ _ (by decide)))
  refine WP.mono (store_ok' h₂ (e := 1) (p := Cfg.qPt p384 1) (by decide) (sl8 _ (by decide)) (sl8 _ (by decide))
    (sl8 _ (by decide)) pQ₂) fun s₃ ⟨h₃, k₃⟩ => k s₃ h₃ fun d hd => ((k₃ d hd).trans (k₂ d hd)).trans (k₁ d hd)

/-- `2P` and `3P` from `P` in the slots `p₁`, to `p₂` and `p₃` and to the
entries `e₂` and `e₃`; the slots of `D` are kept. -/
theorem mult_ok (hL : Law W) {base : Addr} {s₀ s : State} {G Q P : Point W} (hP : onCurve W P = true)
    {L : List Nat} (h : BS base s₀ s G Q L) {p₁ p₂ p₃ : Pt} {e₂ e₃ : Nat} (he₂ : e₂ < 16) (he₃ : e₃ < 16)
    (hA₂ : RcbApart p384.rcbSlots p₁ p₁ p₂) (hA₃ : RcbApart p384.rcbSlots p₂ p₁ p₃)
    (hsl₂ : ∀ x ∈ rcbW p384.rcbSlots p₂ ++ rcbR p384.rcbSlots p₁ p₁, x ∈ jSl)
    (hsl₃ : ∀ x ∈ rcbW p384.rcbSlots p₃ ++ rcbR p384.rcbSlots p₂ p₁, x ∈ jSl)
    (hW₂ : ∀ w ∈ addW p₂, ∃ w' ∈ buildW, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2)
    (hW₃ : ∀ w ∈ addW p₃, ∃ w' ∈ buildW, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2)
    (hs₂ : ∀ x ∈ [p₂.x, p₂.y, p₂.z], x % 8 = 0 ∧ x + 48 ≤ 4095)
    (hs₃ : ∀ x ∈ [p₃.x, p₃.y, p₃.z], x % 8 = 0 ∧ x + 48 ≤ 4095)
    (hk₁ : ∀ d ∈ [p₁.x, p₁.y, p₁.z], (∀ w ∈ addW p₂ ++ addW p₃, d + 8 * 6 ≤ w.1 ∨ w.1 + w.2 ≤ d) ∧ d + 48 ≤ 4095)
    (hk₂ : ∀ d ∈ [p₂.x, p₂.y, p₂.z], (∀ w ∈ addW p₃, d + 8 * 6 ≤ w.1 ∨ w.1 + w.2 ≤ d) ∧ d + 48 ≤ 4095)
    {D : List Nat} (hD : ∀ d ∈ D, (∀ w ∈ addW p₂ ++ addW p₃, d + 8 * 6 ≤ w.1 ∨ w.1 + w.2 ≤ d) ∧ d + 48 ≤ 4095)
    (e2 : ent G Q (e₂ / 4) (e₂ % 4) = mul 2 P) (e3 : ent G Q (e₃ / 4) (e₃ % 4) = mul 3 P)
    (hp₁ : PtOk base s p₁ (mul 1 P)) {rest : Prog isa} {R : State → Prop}
    (k : ∀ s', BS base s₀ s' G Q (e₃ :: e₂ :: L) → PtOk base s' p₁ (mul 1 P) → PtOk base s' p₂ (mul 2 P) →
      PtOk base s' p₃ (mul 3 P) → (∀ d ∈ D, wordsVal s'.mem base d 6 = wordsVal s.mem base d 6) → WP isa rest s' R) :
    WP isa (.seq (Cfg.addPt p384 p₁ p₁ p₂) <| .seq (.block (Cfg.storePt p384 e₂ p₂)) <|
      .seq (Cfg.addPt p384 p₂ p₁ p₃) <| .seq (.block (Cfg.storePt p384 e₃ p₃)) rest) s R := by
  have h1 := hL.onCurve_mul hP 1
  refine WP.seq (WP.mono (add_ok' hL h hA₂ hsl₂ hW₂ h1 h1 hp₁ hp₁) fun s₁ ⟨h₁, ok₂, U₁⟩ => ?_)
  rw [mul_one', ← mul_two'] at ok₂
  have k₁ : ∀ d ∈ [p₁.x, p₁.y, p₁.z] ++ D, wordsVal s₁.mem base d 6 = wordsVal s.mem base d 6 :=
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
      wordsVal s₃.mem base d 6 = wordsVal s₂.mem base d 6 :=
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
    WP isa (Cfg.build p384) s fun s' =>
      Kp s s' ∧ Unch base buildW s.mem s'.mem ∧ JTab base s' (Spec.Weierstrass.G W) Q := by
  have hw := hp.ws
  have hp0 : 0 < W.p := by decide
  generalize hGG : Spec.Weierstrass.G W = G
  have hG : onCurve W G = true := hGG ▸ VG.Proof.P384.onCurve_G
  have hQ := hp.on
  have h1 : tmv W 6 base s (p384.sl ONEP) = 1 := by
    simp only [tmv]; rw [hp.onep, Nat.one_mul]; exact toM_one unit
  have pO : PtOk base s (p384.pt ZERO ONEP ZERO) (ent G Q (0 / 4) (0 % 4)) := by
    refine ⟨?_, show wordsVal _ _ (p384.sl ZERO) 6 < _ by rw [hp.zero]; exact hp0,
      show wordsVal _ _ (p384.sl ONEP) 6 < _ by rw [hp.onep]; exact Nat.mod_lt _ hp0,
      show wordsVal _ _ (p384.sl ZERO) 6 < _ by rw [hp.zero]; exact hp0⟩
    have h0 : tmv W 6 base s (p384.sl ZERO) = 0 := by simp only [tmv]; rw [hp.zero]; exact toM_zero _ _
    show Rep W (tmv W 6 base s (p384.sl ZERO)) (tmv W 6 base s (p384.sl ONEP)) (tmv W 6 base s (p384.sl ZERO)) _
    rw [h0, h1, show (0 : Nat) / 4 = 0 from rfl, ent_a0, mul_zero']
    exact rep_infinity' hL
  have pG : PtOk base s (Cfg.gPt p384 1) (mul 1 G) := by
    refine ⟨?_, show wordsVal _ _ (p384.sl GX) 6 < _ by rw [hp.gx]; exact Nat.mod_lt _ hp0,
      show wordsVal _ _ (p384.sl GY) 6 < _ by rw [hp.gy]; exact Nat.mod_lt _ hp0,
      show wordsVal _ _ (p384.sl ONEP) 6 < _ by rw [hp.onep]; exact Nat.mod_lt _ hp0⟩
    show Rep W (tmv W 6 base s (p384.sl GX)) (tmv W 6 base s (p384.sl GY)) (tmv W 6 base s (p384.sl ONEP)) _
    rw [h1, mul_one', ← hGG]
    have ex : tmv W 6 base s (p384.sl GX) = Fin.ofNat W.p W.gx := by simp only [tmv]; rw [hp.gx, toM_mont unit]
    have ey : tmv W 6 base s (p384.sl GY) = Fin.ofNat W.p W.gy := by simp only [tmv]; rw [hp.gy, toM_mont unit]
    rw [ex, ey]
    exact rep_affine' hL _ _
  have pQ : PtOk base s (Cfg.qPt p384 1) (mul 1 Q) := by
    refine ⟨?_, hp.qx, hp.qy, show wordsVal _ _ (p384.sl ONEP) 6 < _ by rw [hp.onep]; exact Nat.mod_lt _ hp0⟩
    show Rep W (tmv W 6 base s (p384.sl CPX)) (tmv W 6 base s (p384.sl CPY)) (tmv W 6 base s (p384.sl ONEP)) _
    rw [h1, mul_one', ← hp.q]
    exact rep_affine' hL _ _
  have h0 : BS base s s G Q [] :=
    ⟨hw, Kp.refl s, Unch.refl _ _ _, hp.ap, hp.bp, fun _ h => absurd h (List.not_mem_nil)⟩
  rw [Cfg.build]
  refine first3_ok h0 pO ((ent_a0 G Q 1).symm ▸ pG) ((ent_0b G Q 1).symm ▸ pQ) fun s₃ h₃ k₃ => ?_
  have pG₃ := pG.of_eq (k₃ _ (by decide)) (k₃ _ (by decide)) (k₃ _ (by decide))
  have pQ₃ := pQ.of_eq (k₃ _ (by decide)) (k₃ _ (by decide)) (k₃ _ (by decide))
  refine mult_ok hL hG h₃ (p₁ := Cfg.gPt p384 1) (p₂ := Cfg.gPt p384 2) (p₃ := Cfg.gPt p384 3) (e₂ := 8) (e₃ := 12)
    (by decide) (by decide) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (D := [p384.sl CPX, p384.sl CPY, p384.sl ONEP])
    (by decide) (ent_a0 G Q 2) (ent_a0 G Q 3) pG₃ fun s₇ h₇ g1 g2 g3 k₇ => ?_
  have pQ₇ := pQ₃.of_eq (k₇ _ (by decide)) (k₇ _ (by decide)) (k₇ _ (by decide))
  refine mult_ok hL hQ h₇ (p₁ := Cfg.qPt p384 1) (p₂ := Cfg.qPt p384 2) (p₃ := Cfg.qPt p384 3) (e₂ := 2) (e₃ := 3)
    (by decide) (by decide) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (D := [p384.sl GX, p384.sl GY, p384.sl ONEP, p384.sl G2X, p384.sl G2Y, p384.sl G2Z,
      p384.sl G3X, p384.sl G3Y, p384.sl G3Z])
    (by decide) (ent_0b G Q 2) (ent_0b G Q 3) pQ₇ fun s₁₁ h₁₁ q1 q2 q3 k₁₁ => ?_
  have hgs : ∀ a ∈ [1, 2, 3], PtOk base s₁₁ (Cfg.gPt p384 a) (mul a G) := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact g1.of_eq (k₁₁ _ (by decide)) (k₁₁ _ (by decide)) (k₁₁ _ (by decide))
    · exact g2.of_eq (k₁₁ _ (by decide)) (k₁₁ _ (by decide)) (k₁₁ _ (by decide))
    · exact g3.of_eq (k₁₁ _ (by decide)) (k₁₁ _ (by decide)) (k₁₁ _ (by decide))
  have hqs : ∀ b ∈ [1, 2, 3], PtOk base s₁₁ (Cfg.qPt p384 b) (mul b Q) := by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    exacts [q1, q2, q3]
  -- The nine.
  have hl : (List.range 3).flatMap (fun a => (List.range 3).map fun b => Cfg.mixed p384 (a + 1) (b + 1)) =
      ([(1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (3, 3)] : List (Nat × Nat)).map
        fun ab => Cfg.mixed p384 ab.1 ab.2 := rfl
  rw [hl]
  refine WP.mono (mixeds_ok hL hG hQ _ (by decide) (by decide) h₁₁ hgs hqs) fun s' h' => ⟨h'.kp, h'.unch, ?_⟩
  intro e he
  exact (h'.ents e ((by decide : ∀ e < 16, e ∈ ((([(1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2),
    (3, 3)] : List (Nat × Nat)).map fun ab => 4 * ab.1 + ab.2).reverse ++ [3, 2, 12, 8, 1, 4, 0])) e he)).2

/-- The registers `select` writes. -/
abbrev selRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a0, .a1, .a2, .a3, .a4]

/-- The window's entry to `E`. -/
theorem select_ok {s : State} {base : Addr} (hw : WsReg s base) {j : Nat} (hj : j < 192)
    (h1 : s.gpr .s1 = BitVec.ofNat 64 j) {G Q : Point W} (hT : JTab base s G Q) :
    WP isa (.block (Cfg.select p384)) s fun s' =>
      PtOk base s' (p384.pt EX EY EZ) (ent G Q ((wordsVal s.mem base (p384.sl UU) 6 >>> (2 * j)) % 4)
        ((wordsVal s.mem base (p384.sl VV) 6 >>> (2 * j)) % 4)) ∧
      Outside base 2848 144 s.mem s'.mem ∧ Rest selRegs s s' := by
  have hn := hw.nowrap
  rw [Cfg.select]
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (window_ok p384 hw hj (by decide) (by decide) h1) fun s₁ ⟨v₁, r₁, m₁⟩ => ?_)
  simp only [show p384.n = 6 from rfl] at v₁
  generalize ha : (wordsVal s.mem base (p384.sl UU) 6 >>> (2 * j)) % 4 = a at v₁
  generalize hb : (wordsVal s.mem base (p384.sl VV) 6 >>> (2 * j)) % 4 = b at v₁
  have ha4 : a < 4 := ha ▸ Nat.mod_lt _ (by decide)
  have hb4 : b < 4 := hb ▸ Nat.mod_lt _ (by decide)
  have hw₁ := hw.of_rest r₁
  refine WP.block_append (WP.mono masks4_ok fun s₂ ⟨v₂, r₂, m₂⟩ => ?_)
  have hw₂ := hw₁.of_rest r₂
  refine wp_addAt (by decide) fun s₄ u₄ => ?_
  have r₄ : Rest [.a0] s₂ s₄ := u₄.rest (by decide)
  have hw₄ := hw₂.of_rest r₄
  have h0 : s₄.gpr .a0 = base + BitVec.ofNat 64 p384.jt := by
    rw [u₄.gpr, r₂.gpr _ (by decide), r₁.gpr _ (by decide), hw.s0]
  have hm : ∀ c < 4, s₄.gpr (maskReg c) = maskOf ((4 * a + b).testBit c) := fun c hc => by
    rw [r₄.gpr _ (by
      have : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl <;> decide), v₂ c hc, v₁, BitVec.getLsbD_ofNat]
    simp [show c < 64 by omega]
  refine WP.mono (WP.rdwr (scansJ_ok p384 (by decide) (by decide) (by decide) (by decide) (by decide) 18
    (Nat.le_refl _) hw₄ h0 hm)) fun s₅ ⟨⟨v₅, O₅, k₅⟩, rd₅, wr₅, sp₅⟩ => ?_
  simp only [show p384.jt = 4096 from rfl, show p384.sl EX = 2848 from rfl, show p384.n = 6 from rfl,
    Nat.reduceMul] at v₅ O₅
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, m₂, m₁]
  rw [m₄] at v₅ O₅
  have ht : (4 * a + b) % 16 = 4 * a + b := Nat.mod_eq_of_lt (by omega)
  rw [ht] at v₅
  have he : PtOk base s (entPt (4 * a + b)) (ent G Q ((4 * a + b) / 4) ((4 * a + b) % 4)) := hT (4 * a + b) (by omega)
  have e₁ : (4 * a + b) / 4 = a := by omega
  have e₂ : (4 * a + b) % 4 = b := by omega
  rw [e₁, e₂] at he
  have wv : ∀ c < 3, wordsVal s₅.mem base (2848 + 48 * c) 6 = wordsVal s.mem base (4096 + 144 * (4 * a + b) + 48 * c) 6 :=
    fun c hc => wordsVal_of_words 6 fun q hq => by
      rw [show 2848 + 48 * c + 8 * q = 2848 + 8 * (6 * c + q) by omega, v₅ _ (by omega)]
      congr 1; omega
  refine ⟨he.move (wv 0 (by decide)) (wv 1 (by decide)) (wv 2 (by decide)), O₅.mono (Nat.le_refl _) (by omega), ?_⟩
  exact ((r₁.mono (by decide)).trans ((r₂.mono (by decide)).trans ((r₄.mono (by decide)).trans
    ⟨fun r hr => k₅.1 r (fun h => hr ((by decide : ∀ r ∈ treeRegs, r ∈ selRegs) r h)),
      rd₅, wr₅, sp₅⟩)))

/-! ## The steps -/

/-- What the steps read, as the loop's start `s₀` holds it. -/
structure LPre (base : Addr) (s₀ : State) (G Q : Point W) (u v : Nat) : Prop where
  ap : wordsVal s₀.mem base (p384.sl AP) 6 = W.a * 2 ^ 384 % W.p
  bp : wordsVal s₀.mem base (p384.sl B3P) 6 = 3 * W.b * 2 ^ 384 % W.p
  uu : wordsVal s₀.mem base (p384.sl UU) 6 = u
  vv : wordsVal s₀.mem base (p384.sl VV) 6 = v
  tab : JTab base s₀ G Q
  g : onCurve W G = true
  q : onCurve W Q = true

/-- What the steps write. -/
abbrev stepW : List (Nat × Nat) := [(736, 720), (2848, 144), (3712, 384)]

/-- The loop's invariant at `s1 = j`: `R` represents `[u >>> 2 j]G + [v >>> 2 j]Q`. -/
structure LInv (base : Addr) (s₀ s : State) (G Q : Point W) (u v j : Nat) : Prop where
  ws : WsReg s base
  ctr : s.gpr .s1 = BitVec.ofNat 64 j
  keep : Kc s₀ s
  unch : Unch base stepW s₀.mem s.mem
  rep : PtOk base s (p384.pt RX RY RZ) (jp G Q u v j)

/-- The table, kept by memory unchanged there. -/
theorem JTab.of_eq {base : Addr} {s s' : State} {G Q : Point W} (h : JTab base s G Q)
    (he : ∀ d, 4096 ≤ d → d + 48 ≤ 6400 → wordsVal s'.mem base d 6 = wordsVal s.mem base d 6) : JTab base s' G Q :=
  fun e hlt => (h e hlt).of_eq (he (4096 + 144 * e) (by omega) (by omega)) (he (4096 + 144 * e + 48) (by omega) (by omega))
    (he (4096 + 144 * e + 96) (by omega) (by omega))

/-- A step: from `[u >>> 2 j]G + [v >>> 2 j]Q` to `[u >>> 2 (j - 1)]G + [v >>> 2 (j - 1)]Q`. -/
theorem step_ok (hL : Law W) {base : Addr} {s₀ : State} {G Q : Point W} {u v : Nat} (hP : LPre base s₀ G Q u v)
    {j : Nat} (hj1 : 1 ≤ j) (hj : j ≤ 192) {s : State} (hI : LInv base s₀ s G Q u v j) :
    WP isa (Cfg.step p384) s fun s' => LInv base s₀ s' G Q u v (j - 1) := by
  have hn := hI.ws.nowrap
  have uS : ∀ d, (d + 48 ≤ 736 ∨ 1456 ≤ d) → (d + 48 ≤ 2848 ∨ 2992 ≤ d) → (d + 48 ≤ 3712 ∨ 4096 ≤ d) → d + 48 ≤ 6400 →
      wordsVal s.mem base d 6 = wordsVal s₀.mem base d 6 := fun d h1 h2 h3 h4 =>
    hI.unch.wordsVal (by simp; omega) (by omega)
  have hT : JTab base s G Q := hP.tab.of_eq fun d h1 h2 => uS d (by omega) (by omega) (.inr h1) h2
  rw [Cfg.step]
  refine WP.seq (wp_decCounter hj1 hI.ctr fun s₁ u₁ => ?_)
  have hw₁ := hI.ws.of_kc (Kc.of_rest (u₁.rest (ws := [.s1]) (by decide)))
  refine WP.mono (select_ok hw₁ (j := j - 1) (by omega) u₁.gpr (hT.of_eq fun d _ _ => by rw [u₁.mem]))
    fun s₂ ⟨pE, O₂, r₂⟩ => ?_
  rw [u₁.mem, uS _ (by decide) (by decide) (by decide) (by decide), uS _ (by decide) (by decide) (by decide) (by decide), hP.uu, hP.vv] at pE
  rw [u₁.mem] at O₂
  have hw₂ := hw₁.of_rest r₂
  have e₂ : ∀ d, (d + 48 ≤ 736 ∨ 1456 ≤ d) → (d + 48 ≤ 2848 ∨ 2992 ≤ d) → (d + 48 ≤ 3712 ∨ 4096 ≤ d) → d + 48 ≤ 6400 →
      wordsVal s₂.mem base d 6 = wordsVal s₀.mem base d 6 := fun d h1 h2 h3 h4 => by
    rw [O₂.wordsVal (by omega) (by omega), uS d h1 h2 h3 h4]
  have pR₂ : PtOk base s₂ (p384.pt RX RY RZ) (jp G Q u v j) :=
    hI.rep.of_eq (O₂.wordsVal (by decide) (by decide)) (O₂.wordsVal (by decide) (by decide))
      (O₂.wordsVal (by decide) (by decide))
  have ap₂ : wordsVal s₂.mem base (p384.sl AP) 6 = W.a * 2 ^ 384 % W.p := by
    rw [e₂ _ (by decide) (by decide) (by decide) (by decide)]; exact hP.ap
  have bp₂ : wordsVal s₂.mem base (p384.sl B3P) 6 = 3 * W.b * 2 ^ 384 % W.p := by
    rw [e₂ _ (by decide) (by decide) (by decide) (by decide)]; exact hP.bp
  have hX := ent_curve hL hP.g hP.q (u >>> (2 * j)) (v >>> (2 * j))
  have hD := hL.onCurve_add hX hX
  have hT4 := hL.onCurve_add hD hD
  have hE := ent_curve hL hP.g hP.q ((u >>> (2 * (j - 1))) % 4) ((v >>> (2 * (j - 1))) % 4)
  -- `D = R + R`.
  refine WP.seq (WP.mono (addPt_ok hL hw₂ ap₂ bp₂ (p := p384.pt RX RY RZ) (q := p384.pt RX RY RZ)
    (o := p384.pt DX DY DZ) ⟨by decide, by decide⟩ (by decide) hX hX pR₂ pR₂) fun s₃ ⟨K₃, U₃, pD⟩ => ?_)
  have hw₃ := hw₂.of_kp K₃
  have k₃ : ∀ d ∈ [p384.sl AP, p384.sl B3P, p384.sl EX, p384.sl EY, p384.sl EZ],
      wordsVal s₃.mem base d 6 = wordsVal s₂.mem base d 6 := keepU U₃ (by decide)
  -- `T = D + D`.
  refine WP.seq (WP.mono (addPt_ok hL hw₃ ((k₃ _ (by decide)).trans ap₂) ((k₃ _ (by decide)).trans bp₂)
    (p := p384.pt DX DY DZ) (q := p384.pt DX DY DZ) (o := p384.pt TX TY TZ) ⟨by decide, by decide⟩ (by decide)
    hD hD pD pD) fun s₄ ⟨K₄, U₄, pT⟩ => ?_)
  have hw₄ := hw₃.of_kp K₄
  have k₄ : ∀ d ∈ [p384.sl AP, p384.sl B3P, p384.sl EX, p384.sl EY, p384.sl EZ],
      wordsVal s₄.mem base d 6 = wordsVal s₃.mem base d 6 := keepU U₄ (by decide)
  have pE₄ := pE.of_eq ((k₄ _ (by decide)).trans (k₃ _ (by decide))) ((k₄ _ (by decide)).trans (k₃ _ (by decide)))
    ((k₄ _ (by decide)).trans (k₃ _ (by decide)))
  -- `R = T + E`.
  refine WP.mono (addPt_ok hL hw₄ (((k₄ _ (by decide)).trans (k₃ _ (by decide))).trans ap₂)
    (((k₄ _ (by decide)).trans (k₃ _ (by decide))).trans bp₂)
    (p := p384.pt TX TY TZ) (q := p384.pt EX EY EZ) (o := p384.pt RX RY RZ) ⟨by decide, by decide⟩ (by decide)
    hT4 hE pT pE₄) fun s₅ ⟨K₅, U₅, pR₅⟩ => ?_
  refine ⟨hw₄.of_kp K₅, ?_, ?_, ?_, ?_⟩
  · rw [K₅.gpr _ (by decide), K₄.gpr _ (by decide), K₃.gpr _ (by decide), r₂.gpr _ (by decide), u₁.gpr]
  · exact ((hI.keep.trans (Kc.of_rest (u₁.rest (ws := [.s1]) (by decide)))).trans (Kc.of_rest r₂)).trans
      (K₃.kc.trans (K₄.kc.trans K₅.kc))
  · exact ((((hI.unch.trans (show Unch base [(2848, 144)] s.mem s₂.mem from O₂.unch)).trans U₃).trans U₄).trans
      U₅).cover (by decide)
  · have e := jstep hL hP.g hP.q u v (j - 1)
    rw [show j - 1 + 1 = j by omega] at e
    rw [← e]
    exact pR₅

/-! ## The joint ladder -/

/-- What `joint` writes. -/
abbrev jointW : List (Nat × Nat) := [(736, 720), (2272, 720), (4096, 2304), (3712, 384)]

/-- `R = [u]G + [v]Q`, for `u` and `v` in their slots and `Q` in the check's. -/
theorem joint_ok (hL : Law W) {base : Addr} {s : State} {Q : Point W} (hp : JPre base s Q) :
    WP isa (Cfg.joint p384) s fun s' => Kc s s' ∧ Unch base jointW s.mem s'.mem ∧
      PtOk base s' (p384.pt RX RY RZ) (Spec.Weierstrass.add (mul (wordsVal s.mem base (p384.sl UU) 6)
        (Spec.Weierstrass.G W)) (mul (wordsVal s.mem base (p384.sl VV) 6) Q)) := by
  have hn := hp.ws.nowrap
  have hp0 : 0 < W.p := by decide
  rw [Cfg.joint]
  refine WP.seq (WP.mono (build_ok hL hp) fun s₁ ⟨K₁, U₁, T₁⟩ => ?_)
  have hw₁ := hp.ws.of_kp K₁
  have e₁ : ∀ d ∈ [p384.sl ZERO, p384.sl ONEP, p384.sl AP, p384.sl B3P, p384.sl UU, p384.sl VV],
      wordsVal s₁.mem base d 6 = wordsVal s.mem base d 6 := keepU U₁ (by decide)
  rw [show p384.n = 6 from rfl]
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (copy_ok 6 hw₁ (o := p384.sl RX) (a := p384.sl ZERO) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₂ ⟨x₂, r₂, O₂⟩ => ?_))
  have hw₂ := hw₁.of_rest r₂
  refine WP.block_append (WP.mono (copy_ok 6 hw₂ (o := p384.sl RY) (a := p384.sl ONEP) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₃ ⟨y₃, r₃, O₃⟩ => ?_)
  have hw₃ := hw₂.of_rest r₃
  refine WP.block_append (WP.mono (copy_ok 6 hw₃ (o := p384.sl RZ) (a := p384.sl ZERO) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₄ ⟨z₄, r₄, O₄⟩ => ?_)
  have hw₄ := hw₃.of_rest r₄
  refine wp_li (imm := 192) (by decide) fun s₅ u₅ => WP.block_nil ?_
  have r₅ : Rest [.t0, .s1] s₁ s₅ :=
    ((r₂.trans (r₃.trans r₄)).mono (by decide)).trans (u₅.rest (by decide))
  have hw₅ : WsReg s₅ base := hw₄.of_kc (Kc.of_rest (u₅.rest (ws := [.s1]) (by decide)))
  have U₅ : Unch base [(736, 144)] s₁.mem s₅.mem := by
    rw [u₅.mem]
    exact ((O₂.unch.trans O₃.unch).trans O₄.unch).cover (by decide)
  have e₅ : ∀ d ∈ [p384.sl ZERO, p384.sl ONEP, p384.sl AP, p384.sl B3P, p384.sl UU, p384.sl VV],
      wordsVal s₅.mem base d 6 = wordsVal s.mem base d 6 := fun d hd =>
    (keepU U₅ (D := [p384.sl ZERO, p384.sl ONEP, p384.sl AP, p384.sl B3P, p384.sl UU, p384.sl VV]) (by decide) d hd).trans
      (e₁ d hd)
  have T₅ : JTab base s₅ (Spec.Weierstrass.G W) Q := T₁.of_eq fun d h1 h2 => U₅.wordsVal (by simp; omega) (by omega)
  -- The start: `R = O`.
  generalize hu : wordsVal s.mem base (p384.sl UU) 6 = u
  generalize hv : wordsVal s.mem base (p384.sl VV) 6 = v
  have hu' : u < 2 ^ 384 := hu ▸ wordsVal_lt _ _ _ _
  have hv' : v < 2 ^ 384 := hv ▸ wordsVal_lt _ _ _ _
  have hP : LPre base s₅ (Spec.Weierstrass.G W) Q u v :=
    ⟨(e₅ _ (by decide)).trans hp.ap, (e₅ _ (by decide)).trans hp.bp, (e₅ _ (by decide)).trans hu,
      (e₅ _ (by decide)).trans hv, T₅, VG.Proof.P384.onCurve_G, hp.on⟩
  have rx : wordsVal s₅.mem base (p384.sl RX) 6 = 0 := by
    rw [u₅.mem, O₄.wordsVal (by decide) (by decide), O₃.wordsVal (by decide) (by decide), x₂,
      e₁ _ (by decide), hp.zero]
  have ry : wordsVal s₅.mem base (p384.sl RY) 6 = 1 * 2 ^ 384 % W.p := by
    rw [u₅.mem, O₄.wordsVal (by decide) (by decide), y₃, O₂.wordsVal (by decide) (by decide),
      e₁ _ (by decide), hp.onep]
  have rz : wordsVal s₅.mem base (p384.sl RZ) 6 = 0 := by
    rw [u₅.mem, z₄, O₃.wordsVal (by decide) (by decide), O₂.wordsVal (by decide) (by decide),
      e₁ _ (by decide), hp.zero]
  have hI : LInv base s₅ s₅ (Spec.Weierstrass.G W) Q u v 192 := by
    refine ⟨hw₅, u₅.gpr, ⟨fun _ _ _ => rfl, rfl, rfl, rfl⟩, Unch.refl _ _ _, ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [jp_top (n := 6) _ _ hu' hv']
      show Rep W (tmv W 6 base s₅ (p384.sl RX)) (tmv W 6 base s₅ (p384.sl RY)) (tmv W 6 base s₅ (p384.sl RZ)) _
      simp only [tmv]
      rw [rx, ry, rz, toM_zero, Nat.one_mul, toM_one unit]
      exact rep_infinity' hL
    · show wordsVal _ _ (p384.sl RX) 6 < _; rw [rx]; exact hp0
    · show wordsVal _ _ (p384.sl RY) 6 < _; rw [ry]; exact Nat.mod_lt _ hp0
    · show wordsVal _ _ (p384.sl RZ) 6 < _; rw [rz]; exact hp0
  -- The steps.
  refine countLoop_ok (Inv := fun j s' => LInv base s₅ s' (Spec.Weierstrass.G W) Q u v j) (n := 192)
    (fun j s' hi => hi.ctr) (fun j s' h1 h2 hi => step_ok hL hP h1 h2 hi) (fun s' hi => ?_) (by decide) (by decide) hI
  refine ⟨(K₁.kc.trans (Kc.of_rest r₅)).trans hi.keep, ((U₁.trans U₅).trans hi.unch).cover (by decide), ?_⟩
  rw [← jp_zero]
  exact hi.rep

end VG.Proof.Ecdsa.RISCV64.P384.Joint
