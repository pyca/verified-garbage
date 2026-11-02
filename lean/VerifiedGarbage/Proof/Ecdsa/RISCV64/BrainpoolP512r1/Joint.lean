module

-- separate module: its proofs (about 7 s) cost more than its imports, and its importer's
-- changes need not re-check them

public import VerifiedGarbage.Impl.Ecdsa.RISCV64.Verify
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Joint.Table
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.BrainpoolP512r1.MulFn
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.RISCV64.Ecdsa
public import VerifiedGarbage.Proof.Weierstrass.Joint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.BrainpoolP512r1.Point
import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
public import VerifiedGarbage.Proof.Weierstrass.Law3

/-!
# ECDSA verification over brainpoolP512r1 on RISC-V: the joint ladder

The pieces of the joint ladder of `Impl/Ecdsa/RISCV64/Verify.lean`, which
`JointJ.lean` puts together (`jointJ_ok`), with each step's `4 R` by Jacobian
doublings:

* `copyTo_ok`, `storePt_ok`: a point's slots to an entry of the table, through
  `a6 = s0 + JT`;
* `build_ok`: the table (`JTab`: entry `4 a + b` represents `[a]G + [b]Q`);
* `window_ok`, `select_ok`: the window's entry number `4 u_j + v_j`, its
  masks, and the entry to `E`, by the comb's tree (`tree_ok`);
-/

@[expose] public section

-- `p`, below `2^512`, is evaluated.
set_option exponentiation.threshold 1024

namespace VG.Proof.Ecdsa.RISCV64.BrainpoolP512r1.Joint

open VG VG.RISCV64 VG.RISCV64.Steps VG.Proof.Mont VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdsa.RISCV64.Verify
open VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdh.RISCV64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.Ecdsa.RISCV64.BrainpoolP512r1 (W field_ok unit)
open VG.Proof.Ecdsa.RISCV64.Joint
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Spec.Weierstrass (Point mul onCurve)
open VG.Impl.Ecdsa.RISCV64.Comb (maskReg treeRegs)

/-! ## The complete additions -/

/-- A point in the slots `p`: its coordinates below `p`, representing `P`. -/
structure PtOk (base : Addr) (s : State) (p : Pt) (P : Point W) : Prop where
  rep : Rep W (tmv W 8 base s p.x) (tmv W 8 base s p.y) (tmv W 8 base s p.z) P
  x : wordsVal s.mem base p.x 8 < W.p
  y : wordsVal s.mem base p.y 8 < W.p
  z : wordsVal s.mem base p.z 8 < W.p

/-- The slots of the joint ladder's additions. -/
abbrev jSl : List Nat :=
  [brainpoolp512r1.sl AP, brainpoolp512r1.sl B3P, brainpoolp512r1.sl T0, brainpoolp512r1.sl T1, brainpoolp512r1.sl T2, brainpoolp512r1.sl T3, brainpoolp512r1.sl T4, brainpoolp512r1.sl T5,
    brainpoolp512r1.sl RX, brainpoolp512r1.sl RY, brainpoolp512r1.sl RZ, brainpoolp512r1.sl DX, brainpoolp512r1.sl DY, brainpoolp512r1.sl DZ, brainpoolp512r1.sl TX, brainpoolp512r1.sl TY, brainpoolp512r1.sl TZ,
    brainpoolp512r1.sl GX, brainpoolp512r1.sl GY, brainpoolp512r1.sl ONEP, brainpoolp512r1.sl CPX, brainpoolp512r1.sl CPY,
    brainpoolp512r1.sl G2X, brainpoolp512r1.sl G2Y, brainpoolp512r1.sl G2Z, brainpoolp512r1.sl G3X, brainpoolp512r1.sl G3Y, brainpoolp512r1.sl G3Z,
    brainpoolp512r1.sl Q2X, brainpoolp512r1.sl Q2Y, brainpoolp512r1.sl Q2Z, brainpoolp512r1.sl Q3X, brainpoolp512r1.sl Q3Y, brainpoolp512r1.sl Q3Z,
    brainpoolp512r1.sl EX, brainpoolp512r1.sl EY, brainpoolp512r1.sl EZ]

theorem jLay : Lay brainpoolp512r1.MP' (own 8) (· ∈ jSl) :=
  ⟨by decide, fun x y hx hy => (by decide : ∀ x ∈ jSl, ∀ y ∈ jSl, x ≠ y → x + 8 * 8 ≤ y ∨ y + 8 * 8 ≤ x)
    x hx y hy, by decide, by decide⟩

theorem jShort : Short (· ∈ jSl) := by decide

/-- What the additions write. -/
abbrev addW (o : Pt) : List (Nat × Nat) :=
  (rcbW (Cfg.rcbSlots brainpoolp512r1) o).map (fun w => (w, 8 * 8)) ++ [(own 8, 64 * 8)]


/-- `o = p + q` by the complete addition, for points in slots of `jSl`. -/
theorem addPt_ok (hL : Law W) {base : Addr} {s : State} (hw : WsReg s base)
    (hap : wordsVal s.mem base (brainpoolp512r1.sl AP) 8 = W.a * 2 ^ 512 % W.p)
    (hbp : wordsVal s.mem base (brainpoolp512r1.sl B3P) 8 = 3 * W.b * 2 ^ 512 % W.p)
    {p q o : Pt} (hA : RcbApart (Cfg.rcbSlots brainpoolp512r1) p q o)
    (hsl : ∀ x ∈ rcbW (Cfg.rcbSlots brainpoolp512r1) o ++ rcbR (Cfg.rcbSlots brainpoolp512r1) p q, x ∈ jSl)
    {P P' : Point W} (hP : onCurve W P = true) (hP' : onCurve W P' = true)
    (hp : PtOk base s p P) (hq : PtOk base s q P') :
    WP isa (Cfg.addPt brainpoolp512r1 p q o) s fun s' =>
      Kp s s' ∧ Unch base (addW o) s.mem s'.mem ∧ PtOk base s' o (Spec.Weierstrass.add P P') := by
  have hp0 : 0 < W.p := by decide
  rw [Cfg.addPt_gen _ rfl]
  have hI : Inv 8 base W.p (· ∈ jSl) (rcbR (Cfg.rcbSlots brainpoolp512r1) p q)
      (fun x => toM W.p (2 ^ (64 * 8)) (wordsVal s.mem base x 8)) s := by
    refine ⟨hw, fun x hx => hsl x (List.mem_append_right _ hx), fun x hx => ?_, fun x _ => rfl⟩
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show wordsVal _ _ (brainpoolp512r1.sl AP) 8 < _; rw [hap]; exact Nat.mod_lt _ hp0
    · show wordsVal _ _ (brainpoolp512r1.sl B3P) 8 < _; rw [hbp]; exact Nat.mod_lt _ hp0
    exacts [hp.x, hp.y, hp.z, hq.x, hq.y, hq.z]
  refine WP.mono (rcb_ok (F := brainpoolp512r1Field) field_ok rfl jLay jShort unit hA hsl hI (fun x hx => hx))
    fun s₁ ⟨k₁, I₁, t₁⟩ => ?_
  have ea : toM W.p (2 ^ (64 * 8)) (wordsVal s.mem base (brainpoolp512r1.sl AP) 8) = Fin.ofNat W.p W.a := by
    rw [hap, toM_mont unit]
  have eb : toM W.p (2 ^ (64 * 8)) (wordsVal s.mem base (brainpoolp512r1.sl B3P) 8) = Fin.ofNat W.p (3 * W.b) := by
    rw [hbp, toM_mont unit]
  generalize hE : (fun x => toM W.p (2 ^ (64 * 8)) (wordsVal s.mem base x 8)) = E at I₁ t₁
  have hrep := Rep.add hL hP hP' hp.rep hq.rep (X3 := runOps (rcb (Cfg.rcbSlots brainpoolp512r1) p q o) E o.x)
    (Y3 := runOps (rcb (Cfg.rcbSlots brainpoolp512r1) p q o) E o.y) (Z3 := runOps (rcb (Cfg.rcbSlots brainpoolp512r1) p q o) E o.z)
    (by
      subst hE
      show rcbAdd (Fin.ofNat W.p W.a) (Fin.ofNat W.p (3 * W.b)) _ _ _ _ _ _ = _
      rw [← ea, ← eb]
      exact t₁.1.symm)
  have hm : ∀ x ∈ [o.x, o.y, o.z], x ∈ rcbW (Cfg.rcbSlots brainpoolp512r1) o ++ rcbR (Cfg.rcbSlots brainpoolp512r1) p q :=
    fun x hx => List.mem_append_left _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [rcbW])
  refine ⟨k₁.kp, k₁.mem, ⟨?_, I₁.lt _ (hm _ (by simp)), I₁.lt _ (hm _ (by simp)), I₁.lt _ (hm _ (by simp))⟩⟩
  have vx : tmv W 8 base s₁ o.x = _ := I₁.val _ (hm _ (by simp))
  have vy : tmv W 8 base s₁ o.y = _ := I₁.val _ (hm _ (by simp))
  have vz : tmv W 8 base s₁ o.z = _ := I₁.val _ (hm _ (by simp))
  rw [vx, vy, vz]
  exact hrep

theorem PtOk.of_eq {base : Addr} {s s' : State} {p : Pt} {P : Point W} (h : PtOk base s p P)
    (hx : wordsVal s'.mem base p.x 8 = wordsVal s.mem base p.x 8)
    (hy : wordsVal s'.mem base p.y 8 = wordsVal s.mem base p.y 8)
    (hz : wordsVal s'.mem base p.z 8 = wordsVal s.mem base p.z 8) : PtOk base s' p P :=
  ⟨by simp only [tmv]; rw [hx, hy, hz]; exact h.rep, by rw [hx]; exact h.x, by rw [hy]; exact h.y, by rw [hz]; exact h.z⟩

/-- A point copied to other slots. -/
theorem PtOk.move {base : Addr} {s s' : State} {p q : Pt} {P : Point W} (h : PtOk base s p P)
    (hx : wordsVal s'.mem base q.x 8 = wordsVal s.mem base p.x 8)
    (hy : wordsVal s'.mem base q.y 8 = wordsVal s.mem base p.y 8)
    (hz : wordsVal s'.mem base q.z 8 = wordsVal s.mem base p.z 8) : PtOk base s' q P :=
  ⟨by simp only [tmv]; rw [hx, hy, hz]; exact h.rep, by rw [hx]; exact h.x, by rw [hy]; exact h.y, by rw [hz]; exact h.z⟩

/-! ## The table -/

/-- Entry `e`'s coordinates. -/
abbrev entPt (e : Nat) : Pt := ⟨4096 + 192 * e, 4096 + 192 * e + 64, 4096 + 192 * e + 128⟩

/-- Entry `e` represents `[e / 4]G + [e % 4]Q`. -/
abbrev EntOk (base : Addr) (s : State) (G Q : Point W) (e : Nat) : Prop :=
  PtOk base s (entPt e) (ent G Q (e / 4) (e % 4))

/-- What the table's construction writes. -/
abbrev buildW : List (Nat × Nat) := [(1344, 576), (3008, 768), (4096, 3072), (7680, 512)]

/-- While the table is built, from `s₀`: the entries of `L`. -/
structure BS (base : Addr) (s₀ s : State) (G Q : Point W) (L : List Nat) : Prop where
  ws : WsReg s base
  kp : Kp s₀ s
  unch : Unch base buildW s₀.mem s.mem
  ap : wordsVal s.mem base (brainpoolp512r1.sl AP) 8 = W.a * 2 ^ 512 % W.p
  bp : wordsVal s.mem base (brainpoolp512r1.sl B3P) 8 = 3 * W.b * 2 ^ 512 % W.p
  ents : ∀ e ∈ L, e < 16 ∧ EntOk base s G Q e

/-- A point to entry `e`: the entries so far are kept, and so is every slot. -/
theorem store_ok' {base : Addr} {s₀ s : State} {G Q : Point W} {L : List Nat} (h : BS base s₀ s G Q L)
    {e : Nat} (he : e < 16) {p : Pt}
    (hx : p.x % 8 = 0 ∧ p.x + 64 ≤ 4095) (hy : p.y % 8 = 0 ∧ p.y + 64 ≤ 4095)
    (hz : p.z % 8 = 0 ∧ p.z + 64 ≤ 4095) (hp : PtOk base s p (ent G Q (e / 4) (e % 4))) :
    WP isa (.block (Cfg.storePt brainpoolp512r1 e p)) s fun s' => BS base s₀ s' G Q (e :: L) ∧
      ∀ d, d + 64 ≤ 4095 → wordsVal s'.mem base d 8 = wordsVal s.mem base d 8 := by
  have hn := h.ws.nowrap
  refine WP.mono (storePt_ok brainpoolp512r1 h.ws (e := e) (by decide) (by show 4096 + 192 * e + 192 ≤ 8192; omega)
    (by show 192 * e + 192 ≤ 4095; omega) ⟨hx.1, by show _ + 64 ≤ 4095; omega, by show _ + 64 ≤ 4096; omega⟩
    ⟨hy.1, by show _ + 64 ≤ 4095; omega, by show _ + 64 ≤ 4096; omega⟩
    ⟨hz.1, by show _ + 64 ≤ 4095; omega, by show _ + 64 ≤ 4096; omega⟩) fun s' ⟨ex, ey, ez, r, O⟩ => ?_
  simp only [show brainpoolp512r1.jt = 4096 from rfl, show Cfg.jb brainpoolp512r1 = 192 from rfl, show brainpoolp512r1.n = 8 from rfl,
    Nat.reduceMul] at ex ey ez O
  have hd : ∀ d, d + 64 ≤ 4095 → wordsVal s'.mem base d 8 = wordsVal s.mem base d 8 := fun d hd =>
    O.wordsVal (by omega) (by omega)
  refine ⟨⟨h.ws.of_rest r, h.kp.trans (Kp.of_rest r), ?_, ?_, ?_, ?_⟩, hd⟩
  · refine (h.unch.trans O.unch).cover fun w hw => ?_
    rcases List.mem_append.mp hw with hw | hw
    · exact ⟨w, hw, Nat.le_refl _, Nat.le_refl _⟩
    · rw [List.mem_singleton] at hw
      subst hw
      exact ⟨(4096, 3072), List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
        by show 4096 ≤ 4096 + 192 * e; omega, by show 4096 + 192 * e + 192 ≤ 4096 + 3072; omega⟩
  · rw [hd (brainpoolp512r1.sl AP) (by show 448 + 64 ≤ 4095; omega)]; exact h.ap
  · rw [hd (brainpoolp512r1.sl B3P) (by show 512 + 64 ≤ 4095; omega)]; exact h.bp
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
        · exact O.wordsVal (d := 4096 + 192 * e') (by rcases h1 with h1 | h1 <;> omega) (by omega)
        · exact O.wordsVal (d := 4096 + 192 * e' + 64) (by rcases h1 with h1 | h1 <;> omega) (by omega)
        · exact O.wordsVal (d := 4096 + 192 * e' + 128) (by rcases h1 with h1 | h1 <;> omega) (by omega)

/-- `o = p + q`, for `o` among the slots the construction writes: the
entries are kept. -/
theorem add_ok' (hL : Law W) {base : Addr} {s₀ s : State} {G Q : Point W} {L : List Nat}
    (h : BS base s₀ s G Q L) {p q o : Pt} (hA : RcbApart (Cfg.rcbSlots brainpoolp512r1) p q o)
    (hsl : ∀ x ∈ rcbW (Cfg.rcbSlots brainpoolp512r1) o ++ rcbR (Cfg.rcbSlots brainpoolp512r1) p q, x ∈ jSl)
    (hW : ∀ w ∈ addW o, ∃ w' ∈ buildW, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2)
    {P P' : Point W} (hP : onCurve W P = true) (hP' : onCurve W P' = true)
    (hp : PtOk base s p P) (hq : PtOk base s q P') :
    WP isa (Cfg.addPt brainpoolp512r1 p q o) s fun s' => BS base s₀ s' G Q L ∧
      PtOk base s' o (Spec.Weierstrass.add P P') ∧ Unch base (addW o) s.mem s'.mem := by
  have hn := h.ws.nowrap
  refine WP.mono (addPt_ok hL h.ws h.ap h.bp hA hsl hP hP' hp hq) fun s' ⟨K, U, ok⟩ => ?_
  have hd : ∀ d, (∀ w ∈ addW o, d + 64 ≤ w.1 ∨ w.1 + w.2 ≤ d) → d + 64 ≤ 8192 →
      wordsVal s'.mem base d 8 = wordsVal s.mem base d 8 := fun d h1 h2 => U.wordsVal h1 (by omega)
  have hfar : ∀ d, 4096 ≤ d → d + 64 ≤ 7168 → ∀ w ∈ addW o, d + 64 ≤ w.1 ∨ w.1 + w.2 ≤ d := by
    intro d h1 h1' w hw
    have hsl' : ∀ x ∈ rcbW (Cfg.rcbSlots brainpoolp512r1) o, x + 64 ≤ 4095 := fun x hx =>
      (by decide : ∀ x ∈ jSl, x + 64 ≤ 4095) x (hsl x (List.mem_append_left _ hx))
    simp only [addW, List.mem_append, List.mem_map, List.mem_singleton] at hw
    rcases hw with ⟨x, hx, rfl⟩ | rfl
    · have := hsl' x hx; right; simp only; omega
    · left; show d + 64 ≤ 7680; omega
  refine ⟨⟨h.ws.of_kp K, h.kp.trans K, (h.unch.trans U).cover fun w hw => ?_, ?_, ?_, ?_⟩, ok, U⟩
  · rcases List.mem_append.mp hw with hw | hw
    · exact ⟨w, hw, Nat.le_refl _, Nat.le_refl _⟩
    · exact hW w hw
  · have hlow : ∀ w ∈ addW o, 1344 ≤ w.1 := fun w hw => by
      obtain ⟨w', hw', l1, l2⟩ := hW w hw
      have : 1344 ≤ w'.1 := by
        simp only [buildW, List.mem_cons, List.not_mem_nil, or_false] at hw'
        rcases hw' with rfl | rfl | rfl | rfl <;> decide
      omega
    rw [hd (brainpoolp512r1.sl AP) (fun w hw => .inl (by have := hlow w hw; show 448 + 64 ≤ w.1; omega))
      (by show 448 + 64 ≤ 8192; omega)]
    exact h.ap
  · have hfarB : ∀ w ∈ addW o, brainpoolp512r1.sl B3P + 8 * 8 ≤ w.1 ∨ w.1 + w.2 ≤ brainpoolp512r1.sl B3P := fun w hw => by
      obtain ⟨w', hw', l1, l2⟩ := hW w hw
      have : 512 + 64 ≤ w'.1 ∨ w'.1 + w'.2 ≤ 512 := by
        simp only [buildW, List.mem_cons, List.not_mem_nil, or_false] at hw'
        rcases hw' with rfl | rfl | rfl | rfl <;> decide
      show 512 + 64 ≤ w.1 ∨ w.1 + w.2 ≤ 512
      omega
    rw [hd (brainpoolp512r1.sl B3P) hfarB (by show 512 + 64 ≤ 8192; omega)]
    exact h.bp
  · intro e he
    obtain ⟨hlt, hok⟩ := h.ents e he
    exact ⟨hlt, hok.of_eq (hd (4096 + 192 * e) (hfar _ (by omega) (by omega)) (by omega))
      (hd (4096 + 192 * e + 64) (hfar _ (by omega) (by omega)) (by omega))
      (hd (4096 + 192 * e + 128) (hfar _ (by omega) (by omega)) (by omega))⟩

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
  ap : wordsVal s.mem base (brainpoolp512r1.sl AP) 8 = W.a * 2 ^ 512 % W.p
  bp : wordsVal s.mem base (brainpoolp512r1.sl B3P) 8 = 3 * W.b * 2 ^ 512 % W.p
  zero : wordsVal s.mem base (brainpoolp512r1.sl ZERO) 8 = 0
  onep : wordsVal s.mem base (brainpoolp512r1.sl ONEP) 8 = 1 * 2 ^ 512 % W.p
  gx : wordsVal s.mem base (brainpoolp512r1.sl GX) 8 = W.gx * 2 ^ 512 % W.p
  gy : wordsVal s.mem base (brainpoolp512r1.sl GY) 8 = W.gy * 2 ^ 512 % W.p
  qx : wordsVal s.mem base (brainpoolp512r1.sl CPX) 8 < W.p
  qy : wordsVal s.mem base (brainpoolp512r1.sl CPY) 8 < W.p
  q : Point.affine (tmv W 8 base s (brainpoolp512r1.sl CPX)) (tmv W 8 base s (brainpoolp512r1.sl CPY)) = Q
  on : onCurve W Q = true

/-- The coordinates of the multiples of `G` and `Q` in slots. -/
abbrev gqSl : List Nat :=
  [brainpoolp512r1.sl GX, brainpoolp512r1.sl GY, brainpoolp512r1.sl ONEP, brainpoolp512r1.sl CPX, brainpoolp512r1.sl CPY,
    brainpoolp512r1.sl G2X, brainpoolp512r1.sl G2Y, brainpoolp512r1.sl G2Z, brainpoolp512r1.sl G3X, brainpoolp512r1.sl G3Y, brainpoolp512r1.sl G3Z,
    brainpoolp512r1.sl Q2X, brainpoolp512r1.sl Q2Y, brainpoolp512r1.sl Q2Z, brainpoolp512r1.sl Q3X, brainpoolp512r1.sl Q3Y, brainpoolp512r1.sl Q3Z]

theorem gPt_sl : ∀ a ∈ [1, 2, 3], (Cfg.gPt brainpoolp512r1 a).x ∈ gqSl ∧ (Cfg.gPt brainpoolp512r1 a).y ∈ gqSl ∧
    (Cfg.gPt brainpoolp512r1 a).z ∈ gqSl := by decide

theorem qPt_sl : ∀ b ∈ [1, 2, 3], (Cfg.qPt brainpoolp512r1 b).x ∈ gqSl ∧ (Cfg.qPt brainpoolp512r1 b).y ∈ gqSl ∧
    (Cfg.qPt brainpoolp512r1 b).z ∈ gqSl := by decide

/-- A point in slots of `gqSl`, kept where those slots are. -/
theorem PtOk.keep {base : Addr} {s s' : State} {p : Pt} {P : Point W} (h : PtOk base s p P)
    (hk : ∀ d ∈ gqSl, wordsVal s'.mem base d 8 = wordsVal s.mem base d 8)
    (hp : p.x ∈ gqSl ∧ p.y ∈ gqSl ∧ p.z ∈ gqSl) : PtOk base s' p P :=
  h.of_eq (hk _ hp.1) (hk _ hp.2.1) (hk _ hp.2.2)

theorem keep_addT {base : Addr} {m m' : Mem} (U : Unch base (addW (brainpoolp512r1.pt TX TY TZ)) m m') :
    ∀ d ∈ gqSl, wordsVal m' base d 8 = wordsVal m base d 8 := by
  have h : ∀ d ∈ gqSl, ∀ w ∈ addW (brainpoolp512r1.pt TX TY TZ), d + 8 * 8 ≤ w.1 ∨ w.1 + w.2 ≤ d := by decide
  intro d hd
  exact U.wordsVal (h d hd) (by have : d < 4095 := (by decide : ∀ d ∈ gqSl, d < 4095) d hd; omega)

theorem apart_mixed' : ∀ a ∈ [1, 2, 3], ∀ b ∈ [1, 2, 3],
    ((rcbW (Cfg.rcbSlots brainpoolp512r1) (brainpoolp512r1.pt TX TY TZ)).Nodup ∧
      ∀ x ∈ rcbR (Cfg.rcbSlots brainpoolp512r1) (Cfg.gPt brainpoolp512r1 a) (Cfg.qPt brainpoolp512r1 b), x ∉ rcbW (Cfg.rcbSlots brainpoolp512r1) (brainpoolp512r1.pt TX TY TZ)) ∧
    (∀ x ∈ rcbW (Cfg.rcbSlots brainpoolp512r1) (brainpoolp512r1.pt TX TY TZ) ++ rcbR (Cfg.rcbSlots brainpoolp512r1) (Cfg.gPt brainpoolp512r1 a) (Cfg.qPt brainpoolp512r1 b), x ∈ jSl) :=
  by decide

theorem apart_mixed {a b : Nat} (ha : a ∈ [1, 2, 3]) (hb : b ∈ [1, 2, 3]) :
    RcbApart (Cfg.rcbSlots brainpoolp512r1) (Cfg.gPt brainpoolp512r1 a) (Cfg.qPt brainpoolp512r1 b) (brainpoolp512r1.pt TX TY TZ) ∧
    (∀ x ∈ rcbW (Cfg.rcbSlots brainpoolp512r1) (brainpoolp512r1.pt TX TY TZ) ++ rcbR (Cfg.rcbSlots brainpoolp512r1) (Cfg.gPt brainpoolp512r1 a) (Cfg.qPt brainpoolp512r1 b), x ∈ jSl) :=
  have h := apart_mixed' a ha b hb
  ⟨⟨h.1.1, h.1.2⟩, h.2⟩

theorem slots_mixed : ∀ x ∈ [brainpoolp512r1.sl TX, brainpoolp512r1.sl TY, brainpoolp512r1.sl TZ], x % 8 = 0 ∧ x + 64 ≤ 4095 := by decide

/-- Entry `4 a + b`, from `[a]G` and `[b]Q` in slots. -/
theorem mixed_ok (hL : Law W) {base : Addr} {s₀ s : State} {G Q : Point W} (hG : onCurve W G = true)
    (hQ : onCurve W Q = true) {L : List Nat} (h : BS base s₀ s G Q L) {a b : Nat} (ha : a ∈ [1, 2, 3])
    (hb : b ∈ [1, 2, 3]) (hpa : PtOk base s (Cfg.gPt brainpoolp512r1 a) (mul a G))
    (hpb : PtOk base s (Cfg.qPt brainpoolp512r1 b) (mul b Q)) :
    WP isa (Cfg.mixed brainpoolp512r1 a b) s fun s' => BS base s₀ s' G Q ((4 * a + b) :: L) ∧
      ∀ d ∈ gqSl, wordsVal s'.mem base d 8 = wordsVal s.mem base d 8 := by
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
  rw [k₂ d (by have := (by decide : ∀ d ∈ gqSl, d + 64 ≤ 4095) d hd; exact this), k₁ d hd]

/-- The nine entries of both. -/
theorem mixeds_ok (hL : Law W) {base : Addr} {s₀ : State} {G Q : Point W} (hG : onCurve W G = true)
    (hQ : onCurve W Q = true) :
    ∀ (l : List (Nat × Nat)) {s : State} {L : List Nat}, l ≠ [] → (∀ ab ∈ l, ab.1 ∈ [1, 2, 3] ∧ ab.2 ∈ [1, 2, 3]) →
    BS base s₀ s G Q L → (∀ a ∈ [1, 2, 3], PtOk base s (Cfg.gPt brainpoolp512r1 a) (mul a G)) →
    (∀ b ∈ [1, 2, 3], PtOk base s (Cfg.qPt brainpoolp512r1 b) (mul b Q)) →
    WP isa (progs (l.map fun ab => Cfg.mixed brainpoolp512r1 ab.1 ab.2)) s fun s' =>
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
    rw [show progs (Cfg.mixed brainpoolp512r1 ab.1 ab.2 :: Cfg.mixed brainpoolp512r1 ab'.1 ab'.2 ::
      List.map (fun ab => Cfg.mixed brainpoolp512r1 ab.1 ab.2) l) = .seq (Cfg.mixed brainpoolp512r1 ab.1 ab.2)
        (progs (Cfg.mixed brainpoolp512r1 ab'.1 ab'.2 :: List.map (fun ab => Cfg.mixed brainpoolp512r1 ab.1 ab.2) l)) from rfl]
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
    (hD : ∀ d ∈ D, (∀ w ∈ Wl, d + 8 * 8 ≤ w.1 ∨ w.1 + w.2 ≤ d) ∧ d + 64 ≤ 4095) :
    ∀ d ∈ D, wordsVal m' base d 8 = wordsVal m base d 8 := fun d hd =>
  U.wordsVal (hD d hd).1 (by have := (hD d hd).2; omega)

/-- `O`, `G` and `Q` to entries 0, 4 and 1. -/
theorem first3_ok {base : Addr} {s₀ s : State} {G Q : Point W} (h : BS base s₀ s G Q [])
    (pO : PtOk base s (brainpoolp512r1.pt ZERO ONEP ZERO) (ent G Q (0 / 4) (0 % 4)))
    (pG : PtOk base s (Cfg.gPt brainpoolp512r1 1) (ent G Q (4 / 4) (4 % 4)))
    (pQ : PtOk base s (Cfg.qPt brainpoolp512r1 1) (ent G Q (1 / 4) (1 % 4))) {rest : Prog isa} {R : State → Prop}
    (k : ∀ s', BS base s₀ s' G Q [1, 4, 0] → (∀ d, d + 64 ≤ 4095 → wordsVal s'.mem base d 8 = wordsVal s.mem base d 8) →
      WP isa rest s' R) :
    WP isa (.seq (.block (Cfg.storePt brainpoolp512r1 0 (brainpoolp512r1.pt ZERO ONEP ZERO) ++ Cfg.storePt brainpoolp512r1 4 (Cfg.gPt brainpoolp512r1 1) ++
      Cfg.storePt brainpoolp512r1 1 (Cfg.qPt brainpoolp512r1 1))) rest) s R := by
  have sl8 : ∀ x ∈ [brainpoolp512r1.sl ZERO, brainpoolp512r1.sl ONEP, brainpoolp512r1.sl GX, brainpoolp512r1.sl GY, brainpoolp512r1.sl CPX, brainpoolp512r1.sl CPY],
      x % 8 = 0 ∧ x + 64 ≤ 4095 := by decide
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (store_ok' h (e := 0) (p := brainpoolp512r1.pt ZERO ONEP ZERO) (by decide)
    (sl8 _ (by decide)) (sl8 _ (by decide)) (sl8 _ (by decide)) pO) fun s₁ ⟨h₁, k₁⟩ => ?_))
  have pG₁ := pG.of_eq (k₁ _ (by decide)) (k₁ _ (by decide)) (k₁ _ (by decide))
  refine WP.block_append (WP.mono (store_ok' h₁ (e := 4) (p := Cfg.gPt brainpoolp512r1 1) (by decide) (sl8 _ (by decide))
    (sl8 _ (by decide)) (sl8 _ (by decide)) pG₁) fun s₂ ⟨h₂, k₂⟩ => ?_)
  have pQ₂ := pQ.of_eq ((k₂ _ (by decide)).trans (k₁ _ (by decide))) ((k₂ _ (by decide)).trans (k₁ _ (by decide)))
    ((k₂ _ (by decide)).trans (k₁ _ (by decide)))
  refine WP.mono (store_ok' h₂ (e := 1) (p := Cfg.qPt brainpoolp512r1 1) (by decide) (sl8 _ (by decide)) (sl8 _ (by decide))
    (sl8 _ (by decide)) pQ₂) fun s₃ ⟨h₃, k₃⟩ => k s₃ h₃ fun d hd => ((k₃ d hd).trans (k₂ d hd)).trans (k₁ d hd)

/-- `2P` and `3P` from `P` in the slots `p₁`, to `p₂` and `p₃` and to the
entries `e₂` and `e₃`; the slots of `D` are kept. -/
theorem mult_ok (hL : Law W) {base : Addr} {s₀ s : State} {G Q P : Point W} (hP : onCurve W P = true)
    {L : List Nat} (h : BS base s₀ s G Q L) {p₁ p₂ p₃ : Pt} {e₂ e₃ : Nat} (he₂ : e₂ < 16) (he₃ : e₃ < 16)
    (hA₂ : RcbApart (Cfg.rcbSlots brainpoolp512r1) p₁ p₁ p₂) (hA₃ : RcbApart (Cfg.rcbSlots brainpoolp512r1) p₂ p₁ p₃)
    (hsl₂ : ∀ x ∈ rcbW (Cfg.rcbSlots brainpoolp512r1) p₂ ++ rcbR (Cfg.rcbSlots brainpoolp512r1) p₁ p₁, x ∈ jSl)
    (hsl₃ : ∀ x ∈ rcbW (Cfg.rcbSlots brainpoolp512r1) p₃ ++ rcbR (Cfg.rcbSlots brainpoolp512r1) p₂ p₁, x ∈ jSl)
    (hW₂ : ∀ w ∈ addW p₂, ∃ w' ∈ buildW, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2)
    (hW₃ : ∀ w ∈ addW p₃, ∃ w' ∈ buildW, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2)
    (hs₂ : ∀ x ∈ [p₂.x, p₂.y, p₂.z], x % 8 = 0 ∧ x + 64 ≤ 4095)
    (hs₃ : ∀ x ∈ [p₃.x, p₃.y, p₃.z], x % 8 = 0 ∧ x + 64 ≤ 4095)
    (hk₁ : ∀ d ∈ [p₁.x, p₁.y, p₁.z], (∀ w ∈ addW p₂ ++ addW p₃, d + 8 * 8 ≤ w.1 ∨ w.1 + w.2 ≤ d) ∧ d + 64 ≤ 4095)
    (hk₂ : ∀ d ∈ [p₂.x, p₂.y, p₂.z], (∀ w ∈ addW p₃, d + 8 * 8 ≤ w.1 ∨ w.1 + w.2 ≤ d) ∧ d + 64 ≤ 4095)
    {D : List Nat} (hD : ∀ d ∈ D, (∀ w ∈ addW p₂ ++ addW p₃, d + 8 * 8 ≤ w.1 ∨ w.1 + w.2 ≤ d) ∧ d + 64 ≤ 4095)
    (e2 : ent G Q (e₂ / 4) (e₂ % 4) = mul 2 P) (e3 : ent G Q (e₃ / 4) (e₃ % 4) = mul 3 P)
    (hp₁ : PtOk base s p₁ (mul 1 P)) {rest : Prog isa} {R : State → Prop}
    (k : ∀ s', BS base s₀ s' G Q (e₃ :: e₂ :: L) → PtOk base s' p₁ (mul 1 P) → PtOk base s' p₂ (mul 2 P) →
      PtOk base s' p₃ (mul 3 P) → (∀ d ∈ D, wordsVal s'.mem base d 8 = wordsVal s.mem base d 8) → WP isa rest s' R) :
    WP isa (.seq (Cfg.addPt brainpoolp512r1 p₁ p₁ p₂) <| .seq (.block (Cfg.storePt brainpoolp512r1 e₂ p₂)) <|
      .seq (Cfg.addPt brainpoolp512r1 p₂ p₁ p₃) <| .seq (.block (Cfg.storePt brainpoolp512r1 e₃ p₃)) rest) s R := by
  have h1 := hL.onCurve_mul hP 1
  refine WP.seq (WP.mono (add_ok' hL h hA₂ hsl₂ hW₂ h1 h1 hp₁ hp₁) fun s₁ ⟨h₁, ok₂, U₁⟩ => ?_)
  rw [mul_one', ← mul_two'] at ok₂
  have k₁ : ∀ d ∈ [p₁.x, p₁.y, p₁.z] ++ D, wordsVal s₁.mem base d 8 = wordsVal s.mem base d 8 :=
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
      wordsVal s₃.mem base d 8 = wordsVal s₂.mem base d 8 :=
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
    WP isa (Cfg.build brainpoolp512r1) s fun s' =>
      Kp s s' ∧ Unch base buildW s.mem s'.mem ∧ JTab base s' (Spec.Weierstrass.G W) Q := by
  have hw := hp.ws
  have hp0 : 0 < W.p := by decide
  generalize hGG : Spec.Weierstrass.G W = G
  have hG : onCurve W G = true := hGG ▸ VG.Proof.BrainpoolP512r1.onCurve_G
  have hQ := hp.on
  have h1 : tmv W 8 base s (brainpoolp512r1.sl ONEP) = 1 := by
    simp only [tmv]; rw [hp.onep, Nat.one_mul]; exact toM_one unit
  have pO : PtOk base s (brainpoolp512r1.pt ZERO ONEP ZERO) (ent G Q (0 / 4) (0 % 4)) := by
    refine ⟨?_, show wordsVal _ _ (brainpoolp512r1.sl ZERO) 8 < _ by rw [hp.zero]; exact hp0,
      show wordsVal _ _ (brainpoolp512r1.sl ONEP) 8 < _ by rw [hp.onep]; exact Nat.mod_lt _ hp0,
      show wordsVal _ _ (brainpoolp512r1.sl ZERO) 8 < _ by rw [hp.zero]; exact hp0⟩
    have h0 : tmv W 8 base s (brainpoolp512r1.sl ZERO) = 0 := by simp only [tmv]; rw [hp.zero]; exact toM_zero _ _
    show Rep W (tmv W 8 base s (brainpoolp512r1.sl ZERO)) (tmv W 8 base s (brainpoolp512r1.sl ONEP)) (tmv W 8 base s (brainpoolp512r1.sl ZERO)) _
    rw [h0, h1, show (0 : Nat) / 4 = 0 from rfl, ent_a0, mul_zero']
    exact rep_infinity' hL
  have pG : PtOk base s (Cfg.gPt brainpoolp512r1 1) (mul 1 G) := by
    refine ⟨?_, show wordsVal _ _ (brainpoolp512r1.sl GX) 8 < _ by rw [hp.gx]; exact Nat.mod_lt _ hp0,
      show wordsVal _ _ (brainpoolp512r1.sl GY) 8 < _ by rw [hp.gy]; exact Nat.mod_lt _ hp0,
      show wordsVal _ _ (brainpoolp512r1.sl ONEP) 8 < _ by rw [hp.onep]; exact Nat.mod_lt _ hp0⟩
    show Rep W (tmv W 8 base s (brainpoolp512r1.sl GX)) (tmv W 8 base s (brainpoolp512r1.sl GY)) (tmv W 8 base s (brainpoolp512r1.sl ONEP)) _
    rw [h1, mul_one', ← hGG]
    have ex : tmv W 8 base s (brainpoolp512r1.sl GX) = Fin.ofNat W.p W.gx := by simp only [tmv]; rw [hp.gx, toM_mont unit]
    have ey : tmv W 8 base s (brainpoolp512r1.sl GY) = Fin.ofNat W.p W.gy := by simp only [tmv]; rw [hp.gy, toM_mont unit]
    rw [ex, ey]
    exact rep_affine' hL _ _
  have pQ : PtOk base s (Cfg.qPt brainpoolp512r1 1) (mul 1 Q) := by
    refine ⟨?_, hp.qx, hp.qy, show wordsVal _ _ (brainpoolp512r1.sl ONEP) 8 < _ by rw [hp.onep]; exact Nat.mod_lt _ hp0⟩
    show Rep W (tmv W 8 base s (brainpoolp512r1.sl CPX)) (tmv W 8 base s (brainpoolp512r1.sl CPY)) (tmv W 8 base s (brainpoolp512r1.sl ONEP)) _
    rw [h1, mul_one', ← hp.q]
    exact rep_affine' hL _ _
  have h0 : BS base s s G Q [] :=
    ⟨hw, Kp.refl s, Unch.refl _ _ _, hp.ap, hp.bp, fun _ h => absurd h (List.not_mem_nil)⟩
  rw [Cfg.build]
  refine first3_ok h0 pO ((ent_a0 G Q 1).symm ▸ pG) ((ent_0b G Q 1).symm ▸ pQ) fun s₃ h₃ k₃ => ?_
  have pG₃ := pG.of_eq (k₃ _ (by decide)) (k₃ _ (by decide)) (k₃ _ (by decide))
  have pQ₃ := pQ.of_eq (k₃ _ (by decide)) (k₃ _ (by decide)) (k₃ _ (by decide))
  refine mult_ok hL hG h₃ (p₁ := Cfg.gPt brainpoolp512r1 1) (p₂ := Cfg.gPt brainpoolp512r1 2) (p₃ := Cfg.gPt brainpoolp512r1 3) (e₂ := 8) (e₃ := 12)
    (by decide) (by decide) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (D := [brainpoolp512r1.sl CPX, brainpoolp512r1.sl CPY, brainpoolp512r1.sl ONEP])
    (by decide) (ent_a0 G Q 2) (ent_a0 G Q 3) pG₃ fun s₇ h₇ g1 g2 g3 k₇ => ?_
  have pQ₇ := pQ₃.of_eq (k₇ _ (by decide)) (k₇ _ (by decide)) (k₇ _ (by decide))
  refine mult_ok hL hQ h₇ (p₁ := Cfg.qPt brainpoolp512r1 1) (p₂ := Cfg.qPt brainpoolp512r1 2) (p₃ := Cfg.qPt brainpoolp512r1 3) (e₂ := 2) (e₃ := 3)
    (by decide) (by decide) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (D := [brainpoolp512r1.sl GX, brainpoolp512r1.sl GY, brainpoolp512r1.sl ONEP, brainpoolp512r1.sl G2X, brainpoolp512r1.sl G2Y, brainpoolp512r1.sl G2Z,
      brainpoolp512r1.sl G3X, brainpoolp512r1.sl G3Y, brainpoolp512r1.sl G3Z])
    (by decide) (ent_0b G Q 2) (ent_0b G Q 3) pQ₇ fun s₁₁ h₁₁ q1 q2 q3 k₁₁ => ?_
  have hgs : ∀ a ∈ [1, 2, 3], PtOk base s₁₁ (Cfg.gPt brainpoolp512r1 a) (mul a G) := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact g1.of_eq (k₁₁ _ (by decide)) (k₁₁ _ (by decide)) (k₁₁ _ (by decide))
    · exact g2.of_eq (k₁₁ _ (by decide)) (k₁₁ _ (by decide)) (k₁₁ _ (by decide))
    · exact g3.of_eq (k₁₁ _ (by decide)) (k₁₁ _ (by decide)) (k₁₁ _ (by decide))
  have hqs : ∀ b ∈ [1, 2, 3], PtOk base s₁₁ (Cfg.qPt brainpoolp512r1 b) (mul b Q) := by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    exacts [q1, q2, q3]
  -- The nine.
  have hl : (List.range 3).flatMap (fun a => (List.range 3).map fun b => Cfg.mixed brainpoolp512r1 (a + 1) (b + 1)) =
      ([(1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (3, 3)] : List (Nat × Nat)).map
        fun ab => Cfg.mixed brainpoolp512r1 ab.1 ab.2 := rfl
  rw [hl]
  refine WP.mono (mixeds_ok hL hG hQ _ (by decide) (by decide) h₁₁ hgs hqs) fun s' h' => ⟨h'.kp, h'.unch, ?_⟩
  intro e he
  exact (h'.ents e ((by decide : ∀ e < 16, e ∈ ((([(1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2),
    (3, 3)] : List (Nat × Nat)).map fun ab => 4 * ab.1 + ab.2).reverse ++ [3, 2, 12, 8, 1, 4, 0])) e he)).2

/-- The registers `select` writes. -/
abbrev selRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a0, .a1, .a2, .a3, .a4]

/-- The window's entry to `E`. -/
theorem select_ok {s : State} {base : Addr} (hw : WsReg s base) {j : Nat} (hj : j < 256)
    (h1 : s.gpr .s1 = BitVec.ofNat 64 j) {G Q : Point W} (hT : JTab base s G Q) :
    WP isa (.block (Cfg.select brainpoolp512r1)) s fun s' =>
      PtOk base s' (brainpoolp512r1.pt EX EY EZ) (ent G Q ((wordsVal s.mem base (brainpoolp512r1.sl UU) 8 >>> (2 * j)) % 4)
        ((wordsVal s.mem base (brainpoolp512r1.sl VV) 8 >>> (2 * j)) % 4)) ∧
      Outside base 3776 192 s.mem s'.mem ∧ Rest selRegs s s' := by
  have hn := hw.nowrap
  rw [Cfg.select]
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (window_ok brainpoolp512r1 hw hj (by decide) (by decide) h1) fun s₁ ⟨v₁, r₁, m₁⟩ => ?_)
  simp only [show brainpoolp512r1.n = 8 from rfl] at v₁
  generalize ha : (wordsVal s.mem base (brainpoolp512r1.sl UU) 8 >>> (2 * j)) % 4 = a at v₁
  generalize hb : (wordsVal s.mem base (brainpoolp512r1.sl VV) 8 >>> (2 * j)) % 4 = b at v₁
  have ha4 : a < 4 := ha ▸ Nat.mod_lt _ (by decide)
  have hb4 : b < 4 := hb ▸ Nat.mod_lt _ (by decide)
  have hw₁ := hw.of_rest r₁
  refine WP.block_append (WP.mono masks4_ok fun s₂ ⟨v₂, r₂, m₂⟩ => ?_)
  have hw₂ := hw₁.of_rest r₂
  refine wp_addAt (by decide) fun s₄ u₄ => ?_
  have r₄ : Rest [.a0] s₂ s₄ := u₄.rest (by decide)
  have hw₄ := hw₂.of_rest r₄
  have h0 : s₄.gpr .a0 = base + BitVec.ofNat 64 brainpoolp512r1.jt := by
    rw [u₄.gpr, r₂.gpr _ (by decide), r₁.gpr _ (by decide), hw.s0]
  have hm : ∀ c < 4, s₄.gpr (maskReg c) = maskOf ((4 * a + b).testBit c) := fun c hc => by
    rw [r₄.gpr _ (by
      have : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl <;> decide), v₂ c hc, v₁, BitVec.getLsbD_ofNat]
    simp [show c < 64 by omega]
  refine WP.mono (WP.rdwr (scansJ_ok brainpoolp512r1 (by decide) (by decide) (by decide) (by decide) (by decide) 24
    (Nat.le_refl _) hw₄ h0 hm)) fun s₅ ⟨⟨v₅, O₅, k₅⟩, rd₅, wr₅, sp₅⟩ => ?_
  simp only [show brainpoolp512r1.jt = 4096 from rfl, show brainpoolp512r1.sl EX = 3776 from rfl, show brainpoolp512r1.n = 8 from rfl,
    Nat.reduceMul] at v₅ O₅
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, m₂, m₁]
  rw [m₄] at v₅ O₅
  have ht : (4 * a + b) % 16 = 4 * a + b := Nat.mod_eq_of_lt (by omega)
  rw [ht] at v₅
  have he : PtOk base s (entPt (4 * a + b)) (ent G Q ((4 * a + b) / 4) ((4 * a + b) % 4)) := hT (4 * a + b) (by omega)
  have e₁ : (4 * a + b) / 4 = a := by omega
  have e₂ : (4 * a + b) % 4 = b := by omega
  rw [e₁, e₂] at he
  have wv : ∀ c < 3, wordsVal s₅.mem base (3776 + 64 * c) 8 = wordsVal s.mem base (4096 + 192 * (4 * a + b) + 64 * c) 8 :=
    fun c hc => wordsVal_of_words 8 fun q hq => by
      rw [show 3776 + 64 * c + 8 * q = 3776 + 8 * (8 * c + q) by omega, v₅ _ (by omega)]
      congr 1; omega
  refine ⟨he.move (wv 0 (by decide)) (wv 1 (by decide)) (wv 2 (by decide)), O₅.mono (Nat.le_refl _) (by omega), ?_⟩
  exact ((r₁.mono (by decide)).trans ((r₂.mono (by decide)).trans ((r₄.mono (by decide)).trans
    ⟨fun r hr => k₅.1 r (fun h => hr ((by decide : ∀ r ∈ treeRegs, r ∈ selRegs) r h)),
      rd₅, wr₅, sp₅⟩)))

/-! ## The table, kept -/

/-- The table, kept by memory unchanged there. -/
theorem JTab.of_eq {base : Addr} {s s' : State} {G Q : Point W} (h : JTab base s G Q)
    (he : ∀ d, 4096 ≤ d → d + 64 ≤ 7168 → wordsVal s'.mem base d 8 = wordsVal s.mem base d 8) : JTab base s' G Q :=
  fun e hlt => (h e hlt).of_eq (he (4096 + 192 * e) (by omega) (by omega)) (he (4096 + 192 * e + 64) (by omega) (by omega))
    (he (4096 + 192 * e + 128) (by omega) (by omega))

end VG.Proof.Ecdsa.RISCV64.BrainpoolP512r1.Joint
