module

public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.LadderP
public import VerifiedGarbage.Impl.Weierstrass.PPC64LE.Joint
import VerifiedGarbage.Proof.Weierstrass.Group
import VerifiedGarbage.Proof.Weierstrass.Comb
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Bits
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Copy
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Loop
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Mont.PPC64LE.Const
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `[u]G + [v]Q` by one chain of doublings, on PPC64LE: the proof

The accumulator after the bits `t - 1, …, j` is `[u >>> j]G + [v >>> j]Q`
(`acc`): one position doubles it and adds `G`, `Q` or `G + Q` by the bits
`j` of `u` and `v` (`acc_step`).
-/

-- separate module: the joint multiplication of any curve on the point functions, not only ECDSA's; its proofs take about 15 s

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.Joint

open VG.Proof.Weierstrass VG.Spec.Weierstrass

variable {C : Curve}

/-- The accumulator after the bits from the top down to `j`. -/
def acc (G Q : Point C) (u v j : Nat) : Point C := add (mul (u >>> j) G) (mul (v >>> j) Q)

/-- The entry of the bit pair `(a, b)`: `G + Q`, `G`, `Q` or `O`. -/
def entry (G Q : Point C) (a b : Bool) : Point C :=
  if b then (if a then add G Q else Q) else (if a then G else .infinity)

theorem acc_curve (hC : Law C) {G Q : Point C} (hG : onCurve C G = true) (hQ : onCurve C Q = true)
    (u v j : Nat) : onCurve C (acc G Q u v j) = true :=
  hC.onCurve_add (hC.onCurve_mul hG _) (hC.onCurve_mul hQ _)

theorem entry_curve (hC : Law C) {G Q : Point C} (hG : onCurve C G = true) (hQ : onCurve C Q = true)
    (a b : Bool) : onCurve C (entry G Q a b) = true := by
  unfold entry; split
  · split
    · exact hC.onCurve_add hG hQ
    · exact hQ
  · split
    · exact hG
    · rfl

/-- One position: `acc j = 2 acc (j + 1) + E`, for the entry `E` of the bits
`j` (`O` if both are clear). -/
theorem acc_step (hC : Law C) {G Q : Point C} (hG : onCurve C G = true) (hQ : onCurve C Q = true)
    (u v j : Nat) :
    acc G Q u v j =
      add (add (acc G Q u v (j + 1)) (acc G Q u v (j + 1))) (entry G Q (u.testBit j) (v.testBit j)) := by
  obtain ⟨M, _, f, hf⟩ := hC.group
  have hk : ∀ k : Nat, k >>> j = 2 * (k >>> (j + 1)) + (k.testBit j).toNat := fun k => by
    rw [Nat.testBit, Nat.shiftRight_succ, Nat.one_and_eq_mod_two]
    cases h : (k >>> j) % 2 == 1 <;> simp_all <;> omega
  have hA := acc_curve hC hG hQ u v (j + 1)
  have hD := hC.onCurve_add hA hA
  have fA : f (acc G Q u v (j + 1)) =
      ((u >>> (j + 1) : Nat) : Int) • f G + ((v >>> (j + 1) : Nat) : Int) • f Q := by
    rw [acc, hf.add (hC.onCurve_mul hG _) (hC.onCurve_mul hQ _), hf.mul hG, hf.mul hQ]
  have fJ : f (acc G Q u v j) =
      ((u >>> j : Nat) : Int) • f G + ((v >>> j : Nat) : Int) • f Q := by
    rw [acc, hf.add (hC.onCurve_mul hG _) (hC.onCurve_mul hQ _), hf.mul hG, hf.mul hQ]
  have hu := hk u
  have hv := hk v
  generalize u >>> (j + 1) = a at hu fA
  generalize v >>> (j + 1) = b at hv fA
  rcases eu : u.testBit j <;> rcases ev : v.testBit j <;> rw [eu] at hu <;> rw [ev] at hv <;>
    simp only [Bool.false_eq_true, ite_true,
      ite_false, entry, Bool.toNat_false, Bool.toNat_true, Nat.add_zero, add_infinity] at hu hv ⊢
  · apply hf.inj (acc_curve hC hG hQ u v j) hD
    rw [fJ, hf.add hA hA, fA, hu, hv]
    simp only [Int.natCast_mul, Lean.Grind.IntModule.mul_zsmul]
    grind
  · apply hf.inj (acc_curve hC hG hQ u v j) (hC.onCurve_add hD hQ)
    rw [fJ, hf.add hD hQ, hf.add hA hA, fA, hu, hv]
    simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_one,
      Lean.Grind.IntModule.add_zsmul, Lean.Grind.IntModule.mul_zsmul, Lean.Grind.IntModule.one_zsmul]
    grind
  · apply hf.inj (acc_curve hC hG hQ u v j) (hC.onCurve_add hD hG)
    rw [fJ, hf.add hD hG, hf.add hA hA, fA, hu, hv]
    simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_one,
      Lean.Grind.IntModule.add_zsmul, Lean.Grind.IntModule.mul_zsmul, Lean.Grind.IntModule.one_zsmul]
    grind
  · apply hf.inj (acc_curve hC hG hQ u v j) (hC.onCurve_add hD (hC.onCurve_add hG hQ))
    rw [fJ, hf.add hD (hC.onCurve_add hG hQ), hf.add hG hQ, hf.add hA hA, fA, hu, hv]
    simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_one,
      Lean.Grind.IntModule.add_zsmul, Lean.Grind.IntModule.mul_zsmul, Lean.Grind.IntModule.one_zsmul]
    grind


/-! ## The loop's body -/

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Weierstrass.PPC64LE.Point
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass.PPC64LE VG.Proof.Weierstrass.PPC64LE.Mont
  VG.Proof.Weierstrass.PPC64LE.Point
open VG.Impl.Weierstrass.Point (elemBytes ownAt aAt b3At oAt pAt qAt)

/-- Two slots of `n` words apart. -/
abbrev Apart (n x y : Nat) : Prop := x + 8 * n ≤ y ∨ y + 8 * n ≤ x

/-- The slots the loop only reads: `G`, `Q`, `G + Q` and `O`. -/
abbrev roL (J : JointCfg) : List Nat :=
  [J.L.G.x, J.L.G.y, J.L.G.z, J.Q.x, J.Q.y, J.Q.z, J.GQ.x, J.GQ.y, J.GQ.z, J.O.x, J.O.y, J.O.z]

/-- The slots below the point functions' it writes: `R`, `T` and `D`. -/
abbrev wL (J : JointCfg) : List Nat :=
  [J.L.R.x, J.L.R.y, J.L.R.z, J.L.T.x, J.L.T.y, J.L.T.z, J.L.D.x, J.L.D.y, J.L.D.z]

/-- `T`'s and `D`'s slots. -/
abbrev tL (J : JointCfg) : List Nat := [J.L.T.x, J.L.T.y, J.L.T.z]
abbrev dL (J : JointCfg) : List Nat := [J.L.D.x, J.L.D.y, J.L.D.z]

/-- The joint multiplication's slots: the ladder's (`LadPtLay`); those the
loop reads and the temporaries below the point functions', at multiples of 4;
those it reads apart from those it writes; `T`'s and `D`'s apart from each
other; and the table of `v`'s bits above the functions' own working space. -/
structure JLay (J : JointCfg) : Prop where
  lad : LadPtLay J.L
  low : ∀ x ∈ roL J ++ tL J ++ dL J, x + 8 * J.L.M.n ≤ oAt J.L.M.n ∧ x % 4 = 0
  ro : ∀ x ∈ roL J, ∀ y ∈ wL J, Apart J.L.M.n x y
  tne : Apart J.L.M.n J.L.T.x J.L.T.y ∧ Apart J.L.M.n J.L.T.x J.L.T.z ∧ Apart J.L.M.n J.L.T.y J.L.T.z
  dne : Apart J.L.M.n J.L.D.x J.L.D.y ∧ Apart J.L.M.n J.L.D.x J.L.D.z ∧ Apart J.L.M.n J.L.D.y J.L.D.z
  td : ∀ x ∈ tL J, ∀ y ∈ dL J, Apart J.L.M.n x y
  gq : (Apart J.L.M.n J.GQ.x J.GQ.y ∧ Apart J.L.M.n J.GQ.x J.GQ.z ∧ Apart J.L.M.n J.GQ.y J.GQ.z) ∧
    ∀ x ∈ [J.GQ.x, J.GQ.y, J.GQ.z], ∀ y ∈ [J.L.G.x, J.L.G.y, J.L.G.z, J.Q.x, J.Q.y, J.Q.z, J.O.x, J.O.y, J.O.z],
      Apart J.L.M.n x y
  bitsV : 4096 ≤ J.bitsV ∧ J.bitsV + J.L.nbits ≤ 8192

/-- What the loop writes: `R`, `T`, `D` and the point functions' slots and
own working space. -/
def jW (J : JointCfg) : List (Nat × Nat) :=
  [(J.L.R.x, 8 * J.L.M.n), (J.L.R.y, 8 * J.L.M.n), (J.L.R.z, 8 * J.L.M.n),
    (J.L.T.x, 8 * J.L.M.n), (J.L.T.y, 8 * J.L.M.n), (J.L.T.z, 8 * J.L.M.n),
    (J.L.D.x, 8 * J.L.M.n), (J.L.D.y, 8 * J.L.M.n), (J.L.D.z, 8 * J.L.M.n), (oAt J.L.M.n, 4096 - oAt J.L.M.n)]

/-- What the loop reads, fixed at its start `s₀`: `a` and `3b` in the point
functions' slots, below `p`, the entries representing `G`, `Q`, `G + Q` and
`O`, and the tables of the bits of `u` and `v`. -/
structure JFix (J : JointCfg) (C : Curve) (base : Addr) (G Q : Point C) (u v : Nat) (s₀ : State) : Prop where
  ab : tmv C J.L.M.n base s₀ (aAt J.L.M.n) = Fin.ofNat C.p C.a ∧
    tmv C J.L.M.n base s₀ (b3At J.L.M.n) = Fin.ofNat C.p (3 * C.b)
  lt : ∀ x ∈ [aAt J.L.M.n, b3At J.L.M.n, J.L.G.x, J.L.G.y, J.L.G.z, J.Q.x, J.Q.y, J.Q.z,
    J.GQ.x, J.GQ.y, J.GQ.z, J.O.x, J.O.y, J.O.z], wordsVal s₀.mem base x J.L.M.n < C.p
  g : Rep C (tmv C J.L.M.n base s₀ J.L.G.x) (tmv C J.L.M.n base s₀ J.L.G.y) (tmv C J.L.M.n base s₀ J.L.G.z) G
  q : Rep C (tmv C J.L.M.n base s₀ J.Q.x) (tmv C J.L.M.n base s₀ J.Q.y) (tmv C J.L.M.n base s₀ J.Q.z) Q
  gq : Rep C (tmv C J.L.M.n base s₀ J.GQ.x) (tmv C J.L.M.n base s₀ J.GQ.y) (tmv C J.L.M.n base s₀ J.GQ.z)
    (add G Q)
  o : Rep C (tmv C J.L.M.n base s₀ J.O.x) (tmv C J.L.M.n base s₀ J.O.y) (tmv C J.L.M.n base s₀ J.O.z) .infinity
  bu : ∀ t < J.L.nbits, s₀.mem (off base (J.L.bits + t)) = if u.testBit t then 1 else 0
  bv : ∀ t < J.L.nbits, s₀.mem (off base (J.bitsV + t)) = if v.testBit t then 1 else 0

/-- The loop's invariant at `r31 = j`: `R` represents the accumulator after
the bits down to `j`, and `a` and `3b` are where the start left them. -/
structure JInv (J : JointCfg) (C : Curve) (base : Addr) (G Q : Point C) (u v : Nat) (s₀ s : State)
    (j : Nat) : Prop where
  ws : WsReg s base
  r31 : s.gpr .r31 = BitVec.ofNat 64 j
  keep : Rk powClob s₀ s
  unch : Unch base (jW J) s₀.mem s.mem
  ab : wordsVal s.mem base (aAt J.L.M.n) J.L.M.n = wordsVal s₀.mem base (aAt J.L.M.n) J.L.M.n ∧
    wordsVal s.mem base (b3At J.L.M.n) J.L.M.n = wordsVal s₀.mem base (b3At J.L.M.n) J.L.M.n
  lt : ∀ x ∈ [J.L.R.x, J.L.R.y, J.L.R.z], wordsVal s.mem base x J.L.M.n < C.p
  rep : Rep C (tmv C J.L.M.n base s J.L.R.x) (tmv C J.L.M.n base s J.L.R.y) (tmv C J.L.M.n base s J.L.R.z)
    (acc G Q u v j)


section body
variable {J : JointCfg} {C : Curve} {base : Addr}

/-- A range the loop writes, as `jW` covers it. -/
theorem jW_cover {W : List (Nat × Nat)}
    (hW : ∀ w ∈ W, (oAt J.L.M.n ≤ w.1 ∧ w.1 + w.2 ≤ 4096) ∨ w ∈ jW J) :
    ∀ w ∈ W, ∃ w' ∈ jW J, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 := by
  intro w hw
  rcases hW w hw with h | h
  · exact ⟨(oAt J.L.M.n, 4096 - oAt J.L.M.n), by simp [jW], h.1, by simp only; omega⟩
  · exact ⟨w, h, le_refl _, le_refl _⟩

/-- A slot the loop only reads keeps its value from the start. -/
theorem ro_keep (hJ : JLay J) {m m₀ : Mem} (hU : Unch base (jW J) m₀ m)
    {x : Nat} (hx : x ∈ roL J) :
    wordsVal m base x J.L.M.n = wordsVal m₀ base x J.L.M.n := by
  have hl := (hJ.low x (List.mem_append_left _ (List.mem_append_left _ hx))).1
  have hap := hJ.ro x hx
  have hk6 := hJ.lad.k6
  obtain ⟨h1, h2, he, hb3, ha, hq, hp, hoo, ho1, h8⟩ := lay_nums hJ.lad.k3 hk6
  refine hU.wordsVal (fun w hw => ?_) (by omega_arith)
  simp only [jW, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact hap _ (by simp)
    | (simp only; omega_arith)

/-- The slots the loop writes below the point functions' are below them. -/
theorem wL_low (hJ : JLay J) : ∀ x ∈ wL J, x + 8 * J.L.M.n ≤ oAt J.L.M.n := by
  intro x hx
  simp only [wL, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hJ.lad.rx
  · exact hJ.lad.ry
  · exact hJ.lad.rz
  all_goals exact (hJ.low _ (by simp)).1

/-- What the loop writes ends below byte 4096. -/
theorem jW_le (hJ : JLay J) : ∀ w ∈ jW J, w.1 + w.2 ≤ 4096 := by
  have hl := wL_low hJ
  obtain ⟨h1, h2, he, hb3, ha, hq, hp, hoo, ho1, h8⟩ := lay_nums hJ.lad.k3 hJ.lad.k6
  have r1 := hl J.L.R.x (by simp); have r2 := hl J.L.R.y (by simp); have r3 := hl J.L.R.z (by simp)
  have t1 := hl J.L.T.x (by simp); have t2 := hl J.L.T.y (by simp); have t3 := hl J.L.T.z (by simp)
  have d1 := hl J.L.D.x (by simp); have d2 := hl J.L.D.y (by simp); have d3 := hl J.L.D.z (by simp)
  intro w hw
  simp only [jW, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (simp only; omega_arith)

/-- A byte above what the loop writes keeps its value. -/
theorem jW_byte (hJ : JLay J) {m m₀ : Mem} (U : Unch base (jW J) m₀ m) {d : Nat} (h1 : 4096 ≤ d)
    (h2 : d < 2 ^ 64) : m (off base d) = m₀ (off base d) :=
  U.byte (fun w hw => .inr (Nat.le_trans (jW_le hJ w hw) h1)) h2

theorem t_sub : ∀ d ∈ tL J, d ∈ wL J := by
  intro d hd; simp only [tL, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl <;> simp [wL]

theorem d_sub : ∀ d ∈ dL J, d ∈ wL J := by
  intro d hd; simp only [dL, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl <;> simp [wL]

/-- The slots of the entries, as `roL` has them. -/
theorem og_sub : ∀ e ∈ [J.O.x, J.O.y, J.O.z, J.L.G.x, J.L.G.y, J.L.G.z], e ∈ roL J := by
  intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [roL]

theorem qgq_sub : ∀ e ∈ [J.Q.x, J.Q.y, J.Q.z, J.GQ.x, J.GQ.y, J.GQ.z], e ∈ roL J := by
  intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [roL]

theorem low_of (hJ : JLay J) {l : List Nat} (h : ∀ x ∈ l, x ∈ roL J ++ tL J ++ dL J) :
    ∀ x ∈ l, x + 8 * J.L.M.n ≤ oAt J.L.M.n ∧ x % 4 = 0 := fun x hx => hJ.low x (h x hx)

/-- What a selection `o = a` or `b` among slots below the point functions'
needs. -/
theorem sel_conds {n : Nat} (hk3 : 3 ≤ n) (hk6 : n ≤ 6) {o a b : Pt}
    (ho : ∀ x ∈ [o.x, o.y, o.z, a.x, a.y, a.z, b.x, b.y, b.z], x + 8 * n ≤ oAt n ∧ x % 4 = 0)
    (hoo : Apart n o.x o.y ∧ Apart n o.x o.z ∧ Apart n o.y o.z)
    (hab : ∀ d ∈ [o.x, o.y, o.z], ∀ e ∈ [a.x, a.y, a.z, b.x, b.y, b.z], Apart n d e) :
    (∀ d ∈ [o.x, o.y, o.z, a.x, a.y, a.z, b.x, b.y, b.z], d % 4 = 0) ∧
    (∀ d ∈ [o.x, o.y, o.z, a.x, a.y, a.z, b.x, b.y, b.z], d + 8 * n ≤ 8192) ∧
    ((o.x + 8 * n ≤ o.y ∨ o.y + 8 * n ≤ o.x) ∧ (o.x + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.x) ∧
      (o.y + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.y)) ∧
    (∀ d ∈ [o.x, o.y, o.z], ∀ e ∈ [a.x, a.y, a.z, b.x, b.y, b.z], d + 8 * n ≤ e ∨ e + 8 * n ≤ d) := by
  obtain ⟨h1, h2, he, hb3, ha, hq, hp, hoo', ho1, h8⟩ := lay_nums hk3 hk6
  refine ⟨fun d hd => (ho d hd).2, fun d hd => ?_, hoo, hab⟩
  have := (ho d hd).1
  omega_arith

/-- What a selection into the point functions' `Q` from slots below them
needs. -/
theorem selQ_conds {n : Nat} (hk3 : 3 ≤ n) (hk6 : n ≤ 6) {a b : Pt}
    (ho : ∀ x ∈ [a.x, a.y, a.z, b.x, b.y, b.z], x + 8 * n ≤ oAt n ∧ x % 4 = 0) :
    (∀ d ∈ [(ptAt n (qAt n)).x, (ptAt n (qAt n)).y, (ptAt n (qAt n)).z, a.x, a.y, a.z, b.x, b.y, b.z],
      d % 4 = 0) ∧
    (∀ d ∈ [(ptAt n (qAt n)).x, (ptAt n (qAt n)).y, (ptAt n (qAt n)).z, a.x, a.y, a.z, b.x, b.y, b.z],
      d + 8 * n ≤ 8192) ∧
    (((ptAt n (qAt n)).x + 8 * n ≤ (ptAt n (qAt n)).y ∨ (ptAt n (qAt n)).y + 8 * n ≤ (ptAt n (qAt n)).x) ∧
      ((ptAt n (qAt n)).x + 8 * n ≤ (ptAt n (qAt n)).z ∨ (ptAt n (qAt n)).z + 8 * n ≤ (ptAt n (qAt n)).x) ∧
      ((ptAt n (qAt n)).y + 8 * n ≤ (ptAt n (qAt n)).z ∨ (ptAt n (qAt n)).z + 8 * n ≤ (ptAt n (qAt n)).y)) ∧
    (∀ d ∈ [(ptAt n (qAt n)).x, (ptAt n (qAt n)).y, (ptAt n (qAt n)).z],
      ∀ e ∈ [a.x, a.y, a.z, b.x, b.y, b.z], d + 8 * n ≤ e ∨ e + 8 * n ≤ d) := by
  obtain ⟨h1, h2, he, hb3, ha, hq, hp, hoo, ho1, h8⟩ := lay_nums hk3 hk6
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at ho
  obtain ⟨⟨a1, a1'⟩, ⟨a2, a2'⟩, ⟨a3, a3'⟩, ⟨b1, b1'⟩, ⟨b2, b2'⟩, ⟨b3, b3'⟩⟩ := ho
  simp only [ptAt, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  omega_arith

/-- `Apart` is symmetric. -/
theorem Apart.symm {n x y : Nat} (h : Apart n x y) : Apart n y x := Or.symm h

/-- After the doubling: `O` holds `2 acc j`. -/
structure Mid1 (J : JointCfg) (C : Curve) (base : Addr) (G Q : Point C) (u v : Nat) (s₀ : State) (j : Nat)
    (s : State) : Prop where
  ws : WsReg s base
  r31 : s.gpr .r31 = BitVec.ofNat 64 (j - 1)
  keep : Rk powClob s₀ s
  unch : Unch base (jW J) s₀.mem s.mem
  ab : wordsVal s.mem base (aAt J.L.M.n) J.L.M.n = wordsVal s₀.mem base (aAt J.L.M.n) J.L.M.n ∧
    wordsVal s.mem base (b3At J.L.M.n) J.L.M.n = wordsVal s₀.mem base (b3At J.L.M.n) J.L.M.n
  lt : wordsVal s.mem base (oAt J.L.M.n) J.L.M.n < C.p ∧
    wordsVal s.mem base (oAt J.L.M.n + elemBytes J.L.M.n) J.L.M.n < C.p ∧
    wordsVal s.mem base (oAt J.L.M.n + 2 * elemBytes J.L.M.n) J.L.M.n < C.p
  rep : Rep C (tmv C J.L.M.n base s (oAt J.L.M.n)) (tmv C J.L.M.n base s (oAt J.L.M.n + elemBytes J.L.M.n))
    (tmv C J.L.M.n base s (oAt J.L.M.n + 2 * elemBytes J.L.M.n))
    (add (acc G Q u v j) (acc G Q u v j))

theorem dbl_ok {G Q : Point C} {u v : Nat} {S : Impl.Weierstrass.Mont.Modulus}
    (hkS : S.k = J.L.M.n) (hmS : S.m = C.p) (hM : ModOk J.L.M.n C.p) (hodd : C.p % 2 = 1)
    (hC : Law C) (hG : onCurve C G = true) (hQ : onCurve C Q = true) (hJ : JLay J)
    {s₀ : State} (hF : JFix J C base G Q u v s₀) {j : Nat} {s : State} (hj : 1 ≤ j)
    (hI : JInv J C base G Q u v s₀ s j) {rest : Prog isa} {Q' : State → Prop}
    (k : ∀ t, Mid1 J C base G Q u v s₀ j t → WP isa rest t Q') :
    WP isa (.seq (.block (decCounter :: copyPt J.L.M.n J.fP J.L.R)) (.seq (ptCall S true) rest)) s Q' := by
  obtain ⟨c, w, m', k', d⟩ := S
  dsimp only at hkS hmS
  subst hkS hmS
  have hL := hJ.lad
  have hk3 := hL.k3
  have hk6 := hL.k6
  obtain ⟨h1, h2, he, hb3, ha, hq, hp, hoo, ho1, h8⟩ := lay_nums hk3 hk6
  have hn := hI.ws.nowrap
  obtain ⟨-, -, -, -, -, rxl, ryl, rzl⟩ := hL.al
  have rx := hL.rx; have ry := hL.ry; have rz := hL.rz
  have cR := copyPt_conds (a := J.L.R) hk3 hk6 (.inl rfl) (by omega_arith) (by omega_arith) (by omega_arith)
    ⟨rxl, ryl, rzl⟩
  have cO := copyPt_conds (a := ptAt J.L.M.n (oAt J.L.M.n)) hk3 hk6 (.inl rfl)
    (by simp only [ptAt]; omega_arith) (by simp only [ptAt]; omega_arith) (by simp only [ptAt]; omega_arith)
    (by simp only [ptAt]; omega_arith)
  have lrx : wordsVal s.mem base J.L.R.x J.L.M.n < C.p := hI.lt _ (by simp)
  have lry : wordsVal s.mem base J.L.R.y J.L.M.n < C.p := hI.lt _ (by simp)
  have lrz : wordsVal s.mem base J.L.R.z J.L.M.n < C.p := hI.lt _ (by simp)
  have la : wordsVal s.mem base (aAt J.L.M.n) J.L.M.n < C.p := by rw [hI.ab.1]; exact hF.lt _ (by simp)
  have lb : wordsVal s.mem base (b3At J.L.M.n) J.L.M.n < C.p := by rw [hI.ab.2]; exact hF.lt _ (by simp)
  -- `r31 -= 1`.
  refine WP.seq (wp_decCounter hj hI.r31 ?_)
  generalize hs₁ : s.write .r31 (BitVec.ofNat 64 (j - 1)) = s₁
  have K₁ : Kp [.r31] s s₁ := by rw [← hs₁]; exact Kp.write _ _ (by decide)
  have w₁ := hI.ws.of_rk (K₁.rk (rs' := powClob))
  have m₁ : s₁.mem = s.mem := by rw [← hs₁]; rfl
  have c₁ : s₁.gpr .r31 = BitVec.ofNat 64 (j - 1) := by rw [← hs₁]; simp only [write_gpr, ite_true]
  -- `P = R`.
  refine WP.mono (copyPt_ok w₁.ws w₁.at3 (n := J.L.M.n) (o := ptAt J.L.M.n (pAt J.L.M.n)) (a := J.L.R)
    cR.1 cR.2.1 cR.2.2.1 cR.2.2.2) fun s₂ ⟨px₂, py₂, pz₂, k₂, O₂⟩ => ?_
  simp only [ptAt] at px₂ py₂ pz₂ O₂
  rw [m₁] at px₂ py₂ pz₂ O₂
  have w₂ := w₁.of_rk (k₂.rk (rs' := powClob))
  have U₂ : Unch base [(pAt J.L.M.n, 8 * J.L.M.n), (pAt J.L.M.n + elemBytes J.L.M.n, 8 * J.L.M.n),
      (pAt J.L.M.n + 2 * elemBytes J.L.M.n, 8 * J.L.M.n)] s.mem s₂.mem := O₂
  have a₂ : wordsVal s₂.mem base (aAt J.L.M.n) J.L.M.n = wordsVal s.mem base (aAt J.L.M.n) J.L.M.n :=
    U₂.wordsVal (by ppc_apart) (by omega_arith)
  have b₂ : wordsVal s₂.mem base (b3At J.L.M.n) J.L.M.n = wordsVal s.mem base (b3At J.L.M.n) J.L.M.n :=
    U₂.wordsVal (by ppc_apart) (by omega_arith)
  -- `O = P + P`.
  refine WP.seq (WP.mono (ptCall_ok (S := ⟨c, w, C.p, J.L.M.n, d⟩) hM hodd hk3 hk6 true (a0 := false) w₂
    (rIds_lt_of true fun x hx => by
      simp only [↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [px₂]; exact lrx
      · rw [py₂]; exact lry
      · rw [pz₂]; exact lrz
      · rw [px₂]; exact lrx
      · rw [py₂]; exact lry
      · rw [pz₂]; exact lrz
      · rw [a₂]; exact la
      · rw [b₂]; exact lb)) fun s₃ ⟨k₃, O₃, L₃, E₃⟩ => ?_)
  dsimp only at k₃ O₃ L₃ E₃
  obtain ⟨d6, d7, d8⟩ := Eb_dbl (k := J.L.M.n) (m := C.p) s₂.mem base
  simp only [ptVal, Bool.false_eq_true, ↓reduceIte, d6, d7, d8] at E₃
  simp only [Eb, enc_0, enc_1, enc_2, enc_3, enc_4, enc_5, enc_9, enc_10] at E₃
  rw [a₂, b₂, px₂, py₂, pz₂] at E₃
  -- `R + R` represents `2 acc j`.
  have hA := acc_curve hC hG hQ u v j
  have hab : toM C.p (2 ^ (64 * J.L.M.n)) (wordsVal s.mem base (aAt J.L.M.n) J.L.M.n) = Fin.ofNat C.p C.a ∧
      toM C.p (2 ^ (64 * J.L.M.n)) (wordsVal s.mem base (b3At J.L.M.n) J.L.M.n) = Fin.ofNat C.p (3 * C.b) := by
    rw [hI.ab.1, hI.ab.2]; exact hF.ab
  rw [hab.1, hab.2] at E₃
  have R₃ := hC.add hA hA hI.rep hI.rep E₃.symm
  have l3x := L₃ 0 (by decide)
  have l3y := L₃ 1 (by decide)
  have l3z := L₃ 2 (by decide)
  rw [enc_0] at l3x
  rw [enc_1] at l3y
  rw [enc_2] at l3z
  have w₃ := w₂.of_rk (k₃.mono (rs' := powClob))
  refine k s₃ ⟨w₃, by rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), c₁],
    hI.keep.trans ((K₁.rk (rs' := powClob)).trans ((k₂.rk (rs' := powClob)).trans (k₃.mono (rs' := powClob)))),
    ((hI.unch.trans U₂).trans (show Unch base _ s₂.mem s₃.mem from O₃)).cover (jW_cover fun w hw => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with (h | (rfl | rfl | rfl)) | (rfl | rfl)
      · exact .inr h
      all_goals exact .inl ⟨by simp only; omega_arith, by simp only; omega_arith⟩),
    ⟨?_, ?_⟩, ⟨l3x, l3y, l3z⟩, R₃⟩
  · rw [(show Unch base _ s₂.mem s₃.mem from O₃).wordsVal (by ppc_apart) (by omega_arith), a₂, hI.ab.1]
  · rw [(show Unch base _ s₂.mem s₃.mem from O₃).wordsVal (by ppc_apart) (by omega_arith), b₂, hI.ab.2]

/-- After the selection: `P` holds `2 acc j` and `Q` the entry of the bits
`j - 1`. -/
structure Mid2 (J : JointCfg) (C : Curve) (base : Addr) (G Q : Point C) (u v : Nat) (s₀ : State) (j : Nat)
    (s : State) : Prop where
  ws : WsReg s base
  r31 : s.gpr .r31 = BitVec.ofNat 64 (j - 1)
  keep : Rk powClob s₀ s
  unch : Unch base (jW J) s₀.mem s.mem
  ab : wordsVal s.mem base (aAt J.L.M.n) J.L.M.n = wordsVal s₀.mem base (aAt J.L.M.n) J.L.M.n ∧
    wordsVal s.mem base (b3At J.L.M.n) J.L.M.n = wordsVal s₀.mem base (b3At J.L.M.n) J.L.M.n
  plt : wordsVal s.mem base (pAt J.L.M.n) J.L.M.n < C.p ∧
    wordsVal s.mem base (pAt J.L.M.n + elemBytes J.L.M.n) J.L.M.n < C.p ∧
    wordsVal s.mem base (pAt J.L.M.n + 2 * elemBytes J.L.M.n) J.L.M.n < C.p
  prep : Rep C (tmv C J.L.M.n base s (pAt J.L.M.n)) (tmv C J.L.M.n base s (pAt J.L.M.n + elemBytes J.L.M.n))
    (tmv C J.L.M.n base s (pAt J.L.M.n + 2 * elemBytes J.L.M.n))
    (add (acc G Q u v j) (acc G Q u v j))
  qlt : wordsVal s.mem base (qAt J.L.M.n) J.L.M.n < C.p ∧
    wordsVal s.mem base (qAt J.L.M.n + elemBytes J.L.M.n) J.L.M.n < C.p ∧
    wordsVal s.mem base (qAt J.L.M.n + 2 * elemBytes J.L.M.n) J.L.M.n < C.p
  qrep : Rep C (tmv C J.L.M.n base s (qAt J.L.M.n)) (tmv C J.L.M.n base s (qAt J.L.M.n + elemBytes J.L.M.n))
    (tmv C J.L.M.n base s (qAt J.L.M.n + 2 * elemBytes J.L.M.n))
    (entry G Q (u.testBit (j - 1)) (v.testBit (j - 1)))

/-- After the selections by `u`: `P` holds `2 acc j`, `T = u ? G : O` and
`D = u ? G + Q : Q`, as the start has them. -/
structure MidTD (J : JointCfg) (C : Curve) (base : Addr) (G Q : Point C) (u v : Nat) (s₀ : State) (j : Nat)
    (s : State) : Prop where
  ws : WsReg s base
  r31 : s.gpr .r31 = BitVec.ofNat 64 (j - 1)
  keep : Rk powClob s₀ s
  unch : Unch base (jW J) s₀.mem s.mem
  ab : wordsVal s.mem base (aAt J.L.M.n) J.L.M.n = wordsVal s₀.mem base (aAt J.L.M.n) J.L.M.n ∧
    wordsVal s.mem base (b3At J.L.M.n) J.L.M.n = wordsVal s₀.mem base (b3At J.L.M.n) J.L.M.n
  plt : wordsVal s.mem base (pAt J.L.M.n) J.L.M.n < C.p ∧
    wordsVal s.mem base (pAt J.L.M.n + elemBytes J.L.M.n) J.L.M.n < C.p ∧
    wordsVal s.mem base (pAt J.L.M.n + 2 * elemBytes J.L.M.n) J.L.M.n < C.p
  prep : Rep C (tmv C J.L.M.n base s (pAt J.L.M.n)) (tmv C J.L.M.n base s (pAt J.L.M.n + elemBytes J.L.M.n))
    (tmv C J.L.M.n base s (pAt J.L.M.n + 2 * elemBytes J.L.M.n))
    (add (acc G Q u v j) (acc G Q u v j))
  t : ∀ i ∈ [(J.L.T.x, J.L.G.x, J.O.x), (J.L.T.y, J.L.G.y, J.O.y), (J.L.T.z, J.L.G.z, J.O.z)],
    wordsVal s.mem base i.1 J.L.M.n = if u.testBit (j - 1) then wordsVal s₀.mem base i.2.1 J.L.M.n
      else wordsVal s₀.mem base i.2.2 J.L.M.n
  d : ∀ i ∈ [(J.L.D.x, J.GQ.x, J.Q.x), (J.L.D.y, J.GQ.y, J.Q.y), (J.L.D.z, J.GQ.z, J.Q.z)],
    wordsVal s.mem base i.1 J.L.M.n = if u.testBit (j - 1) then wordsVal s₀.mem base i.2.1 J.L.M.n
      else wordsVal s₀.mem base i.2.2 J.L.M.n

/-- `P = O`, `T = u ? G : O`, `D = u ? G + Q : Q`. -/
theorem selU_ok {G Q : Point C} {u v : Nat}
    (hJ : JLay J) {s₀ : State} (hF : JFix J C base G Q u v s₀) {j : Nat} (hj : 1 ≤ j)
    (hjn : j ≤ J.L.nbits) {s₃ : State} (h : Mid1 J C base G Q u v s₀ j s₃) :
    WP isa (.block (copyPt J.L.M.n (ptAt J.L.M.n (pAt J.L.M.n)) (ptAt J.L.M.n (oAt J.L.M.n)) ++
      (bitMask J.L.bits ++ (selPt J.L.M.n J.L.T J.O J.L.G ++ selPt J.L.M.n J.L.D J.Q J.GQ)))) s₃
      (MidTD J C base G Q u v s₀ j) := by
  have hL := hJ.lad
  have hk3 := hL.k3
  have hk6 := hL.k6
  obtain ⟨h1, h2, he, hb3, ha, hq, hp, hoo, ho1, h8⟩ := lay_nums hk3 hk6
  have hn := h.ws.nowrap
  have hbl := hL.bits
  have hbe := hL.bitsE
  have cO := copyPt_conds (a := ptAt J.L.M.n (oAt J.L.M.n)) hk3 hk6 (.inl rfl)
    (by simp only [ptAt]; omega_arith) (by simp only [ptAt]; omega_arith) (by simp only [ptAt]; omega_arith)
    (by simp only [ptAt]; omega_arith)
  rw [WP.block_append_iff]
  refine WP.mono (copyPt_ok h.ws.ws h.ws.at3 (n := J.L.M.n) (o := ptAt J.L.M.n (pAt J.L.M.n))
    (a := ptAt J.L.M.n (oAt J.L.M.n)) cO.1 cO.2.1 cO.2.2.1 cO.2.2.2) fun s₄ ⟨px₄, py₄, pz₄, k₄, O₄⟩ => ?_
  simp only [ptAt] at px₄ py₄ pz₄ O₄
  have w₄ := h.ws.of_rk (k₄.rk (rs' := powClob))
  have U₄ : Unch base (jW J) s₀.mem s₄.mem :=
    (h.unch.trans (show Unch base _ s₃.mem s₄.mem from O₄)).cover (jW_cover fun w hw => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with h | (rfl | rfl | rfl)
      · exact .inr h
      all_goals exact .inl ⟨by simp only; omega_arith, by simp only; omega_arith⟩)
  have c₄ : s₄.gpr .r31 = BitVec.ofNat 64 (j - 1) := by rw [k₄.gpr _ (by decide), h.r31]
  rw [WP.block_append_iff]
  refine WP.mono (bitMask_bool_ok w₄.ws w₄.at3 (d := J.L.bits) c₄ (by omega_arith)
    (c := u.testBit (j - 1)) (by rw [jW_byte hJ U₄ (by omega_arith) (by omega_arith), hF.bu _ (by omega)]))
    fun s₅ ⟨g₅, k₅, m₅⟩ => ?_
  have w₅ := w₄.of_rk (k₅.rk (rs' := powClob))
  rw [WP.block_append_iff]
  have sT := sel_conds hk3 hk6 (o := J.L.T) (a := J.O) (b := J.L.G) (low_of hJ (by
      intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [roL, tL, dL]))
    hJ.tne (fun d hd e he => Apart.symm (hJ.ro e (og_sub e he) d (t_sub d hd)))
  refine WP.mono (selPt_ok w₅.ws (k₅.at w₄.at3) _ g₅ (n := J.L.M.n) (o := J.L.T) (a := J.O) (b := J.L.G)
    sT.1 sT.2.1 sT.2.2.1 sT.2.2.2) fun s₆ ⟨tx₆, ty₆, tz₆, k₆, O₆⟩ => ?_
  have sD := sel_conds hk3 hk6 (o := J.L.D) (a := J.Q) (b := J.GQ) (low_of hJ (by
      intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [roL, tL, dL]))
    hJ.dne (fun d hd e he => Apart.symm (hJ.ro e (qgq_sub e he) d (d_sub d hd)))
  refine WP.mono (selPt_ok (k₆.ws w₅.ws) (k₆.at (k₅.at w₄.at3)) (u.testBit (j - 1))
    (by rw [k₆.gpr _ (by decide)]; exact g₅)
    (n := J.L.M.n) (o := J.L.D) (a := J.Q) (b := J.GQ) sD.1 sD.2.1 sD.2.2.1 sD.2.2.2)
    fun s₇ ⟨dx₇, dy₇, dz₇, k₇, O₇⟩ => ?_
  have U₆₄ : Unch base [(J.L.T.x, 8 * J.L.M.n), (J.L.T.y, 8 * J.L.M.n), (J.L.T.z, 8 * J.L.M.n)] s₄.mem s₆.mem := by
    rw [← m₅]; exact O₆
  have U₇₆ : Unch base [(J.L.D.x, 8 * J.L.M.n), (J.L.D.y, 8 * J.L.M.n), (J.L.D.z, 8 * J.L.M.n)] s₆.mem s₇.mem := O₇
  have U₆ : Unch base (jW J) s₀.mem s₆.mem :=
    (U₄.trans U₆₄).cover (jW_cover fun w hw => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with h | (rfl | rfl | rfl) <;> exact .inr (by first | exact h | simp [jW]))
  have U₇ : Unch base (jW J) s₀.mem s₇.mem :=
    (U₆.trans U₇₆).cover (jW_cover fun w hw => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with h | (rfl | rfl | rfl) <;> exact .inr (by first | exact h | simp [jW]))
  have tdL : ∀ x ∈ tL J ++ dL J, x + 8 * J.L.M.n ≤ oAt J.L.M.n := fun x hx => by
    rcases List.mem_append.mp hx with h | h
    · exact (hJ.low x (List.mem_append_left _ (List.mem_append_right _ h))).1
    · exact (hJ.low x (List.mem_append_right _ h)).1
  have tl1 := tdL J.L.T.x (by simp); have tl2 := tdL J.L.T.y (by simp); have tl3 := tdL J.L.T.z (by simp)
  have dl1 := tdL J.L.D.x (by simp); have dl2 := tdL J.L.D.y (by simp); have dl3 := tdL J.L.D.z (by simp)
  have U₇₄ := U₆₄.trans U₇₆
  have hi : ∀ {x : Nat}, oAt J.L.M.n ≤ x → x + 8 * J.L.M.n ≤ 4096 →
      wordsVal s₇.mem base x J.L.M.n = wordsVal s₄.mem base x J.L.M.n := fun h1 h2 =>
    U₇₄.wordsVal (by ppc_apart) (by omega_arith)
  have td := hJ.td
  refine ⟨w₅.of_rk ((k₆.rk (rs' := powClob)).trans (k₇.rk (rs' := powClob))),
    by rw [k₇.gpr _ (by decide), k₆.gpr _ (by decide), k₅.gpr _ (by decide), c₄],
    h.keep.trans ((k₄.rk (rs' := powClob)).trans ((k₅.rk (rs' := powClob)).trans ((k₆.rk (rs' := powClob)).trans
      (k₇.rk (rs' := powClob))))), U₇, ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hi (by omega_arith) (by omega_arith),
      (show Unch base _ s₃.mem s₄.mem from O₄).wordsVal (by ppc_apart) (by omega_arith), h.ab.1]
  · rw [hi (by omega_arith) (by omega_arith),
      (show Unch base _ s₃.mem s₄.mem from O₄).wordsVal (by ppc_apart) (by omega_arith), h.ab.2]
  · rw [hi (by omega_arith) (by omega_arith), px₄]; exact h.lt.1
  · rw [hi (by omega_arith) (by omega_arith), py₄]; exact h.lt.2.1
  · rw [hi (by omega_arith) (by omega_arith), pz₄]; exact h.lt.2.2
  · show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [hi (by omega_arith) (by omega_arith), hi (by omega_arith) (by omega_arith),
      hi (by omega_arith) (by omega_arith), px₄, py₄, pz₄]
    exact h.rep
  · intro i hi'
    have k₄₀ : ∀ {x : Nat}, x ∈ roL J → wordsVal s₅.mem base x J.L.M.n = wordsVal s₀.mem base x J.L.M.n :=
      fun hx => by rw [m₅]; exact ro_keep hJ U₄ hx
    have t76 : ∀ {x : Nat}, x ∈ tL J → wordsVal s₇.mem base x J.L.M.n = wordsVal s₆.mem base x J.L.M.n :=
      fun hx => U₇₆.wordsVal (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl <;> exact td _ hx _ (by simp))
        (by have := tdL _ (List.mem_append_left _ hx); omega_arith)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
    rcases hi' with rfl | rfl | rfl
    · rw [t76 (by simp), tx₆, k₄₀ (by simp), k₄₀ (by simp)]
    · rw [t76 (by simp), ty₆, k₄₀ (by simp), k₄₀ (by simp)]
    · rw [t76 (by simp), tz₆, k₄₀ (by simp), k₄₀ (by simp)]
  · intro i hi'
    have k₆₀ : ∀ {x : Nat}, x ∈ roL J → wordsVal s₆.mem base x J.L.M.n = wordsVal s₀.mem base x J.L.M.n :=
      fun hx => ro_keep hJ U₆ hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
    rcases hi' with rfl | rfl | rfl
    · rw [dx₇, k₆₀ (by simp), k₆₀ (by simp)]
    · rw [dy₇, k₆₀ (by simp), k₆₀ (by simp)]
    · rw [dz₇, k₆₀ (by simp), k₆₀ (by simp)]

/-- `Q = v ? D : T`: the entry. -/
theorem selV_ok {G Q : Point C} {u v : Nat}
    (hJ : JLay J) {s₀ : State} (hF : JFix J C base G Q u v s₀) {j : Nat} (hj : 1 ≤ j)
    (hjn : j ≤ J.L.nbits) {s₇ : State} (h : MidTD J C base G Q u v s₀ j s₇) :
    WP isa (.block (bitMask J.bitsV ++ selPt J.L.M.n (ptAt J.L.M.n (qAt J.L.M.n)) J.L.T J.L.D)) s₇
      (Mid2 J C base G Q u v s₀ j) := by
  have hL := hJ.lad
  have hk3 := hL.k3
  have hk6 := hL.k6
  obtain ⟨h1, h2, he, hb3, ha, hq, hp, hoo, ho1, h8⟩ := lay_nums hk3 hk6
  have hn := h.ws.nowrap
  have hbv := hJ.bitsV
  rw [WP.block_append_iff]
  refine WP.mono (bitMask_bool_ok h.ws.ws h.ws.at3 (d := J.bitsV) h.r31 (by omega_arith)
    (c := v.testBit (j - 1)) (by rw [jW_byte hJ h.unch (by omega_arith) (by omega_arith), hF.bv _ (by omega)]))
    fun s₈ ⟨g₈, k₈, m₈⟩ => ?_
  have sQ := selQ_conds hk3 hk6 (a := J.L.T) (b := J.L.D) (low_of hJ (by
      intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [roL, tL, dL]))
  refine WP.mono (selPt_ok (k₈.ws h.ws.ws) (k₈.at h.ws.at3) (v.testBit (j - 1)) g₈ (n := J.L.M.n)
    (o := ptAt J.L.M.n (qAt J.L.M.n)) (a := J.L.T) (b := J.L.D) sQ.1 sQ.2.1 sQ.2.2.1 sQ.2.2.2)
    fun s₉ ⟨qx₉, qy₉, qz₉, k₉, O₉⟩ => ?_
  simp only [ptAt] at qx₉ qy₉ qz₉ O₉
  rw [m₈] at qx₉ qy₉ qz₉ O₉
  have U₉₇ : Unch base [(qAt J.L.M.n, 8 * J.L.M.n), (qAt J.L.M.n + elemBytes J.L.M.n, 8 * J.L.M.n),
      (qAt J.L.M.n + 2 * elemBytes J.L.M.n, 8 * J.L.M.n)] s₇.mem s₉.mem := O₉
  have hi : ∀ {x : Nat}, x + 8 * J.L.M.n ≤ qAt J.L.M.n ∨ aAt J.L.M.n ≤ x → x + 8 * J.L.M.n ≤ 4096 →
      wordsVal s₉.mem base x J.L.M.n = wordsVal s₇.mem base x J.L.M.n := fun h1 h2 =>
    U₉₇.wordsVal (by ppc_apart) (by omega_arith)
  have ex : ∀ {x t d gq q g o : Nat}, x = (if v.testBit (j - 1) then d else t) →
      d = (if u.testBit (j - 1) then gq else q) → t = (if u.testBit (j - 1) then g else o) →
      x = if v.testBit (j - 1) then (if u.testBit (j - 1) then gq else q)
        else (if u.testBit (j - 1) then g else o) := fun hx hd ht => by rw [hx, hd, ht]
  have vx := ex qx₉ (h.d (J.L.D.x, J.GQ.x, J.Q.x) (by simp)) (h.t (J.L.T.x, J.L.G.x, J.O.x) (by simp))
  have vy := ex qy₉ (h.d (J.L.D.y, J.GQ.y, J.Q.y) (by simp)) (h.t (J.L.T.y, J.L.G.y, J.O.y) (by simp))
  have vz := ex qz₉ (h.d (J.L.D.z, J.GQ.z, J.Q.z) (by simp)) (h.t (J.L.T.z, J.L.G.z, J.O.z) (by simp))
  dsimp only at vx vy vz
  have lt := hF.lt
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at lt
  obtain ⟨-, -, lgx, lgy, lgz, lqx, lqy, lqz, lgqx, lgqy, lgqz, lox, loy, loz⟩ := lt
  refine ⟨h.ws.of_rk ((k₈.rk (rs' := powClob)).trans (k₉.rk (rs' := powClob))),
    by rw [k₉.gpr _ (by decide), k₈.gpr _ (by decide), h.r31],
    h.keep.trans ((k₈.rk (rs' := powClob)).trans (k₉.rk (rs' := powClob))),
    (h.unch.trans U₉₇).cover (jW_cover fun w hw => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with h | (rfl | rfl | rfl)
      · exact .inr h
      all_goals exact .inl ⟨by simp only; omega_arith, by simp only; omega_arith⟩),
    ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hi (.inr le_rfl) (by omega_arith)]; exact h.ab.1
  · rw [hi (.inr (by omega_arith)) (by omega_arith)]; exact h.ab.2
  · rw [hi (.inl (by omega_arith)) (by omega_arith)]; exact h.plt.1
  · rw [hi (.inl (by omega_arith)) (by omega_arith)]; exact h.plt.2.1
  · rw [hi (.inl (by omega_arith)) (by omega_arith)]; exact h.plt.2.2
  · show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [hi (.inl (by omega_arith)) (by omega_arith), hi (.inl (by omega_arith)) (by omega_arith),
      hi (.inl (by omega_arith)) (by omega_arith)]
    exact h.prep
  · rw [vx]; split <;> split <;> with_reducible assumption
  · rw [vy]; split <;> split <;> with_reducible assumption
  · rw [vz]; split <;> split <;> with_reducible assumption
  · show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [vx, vy, vz]
    unfold entry
    rcases v.testBit (j - 1) <;> rcases u.testBit (j - 1) <;>
      simp only [Bool.false_eq_true, ite_true, ite_false]
    · exact hF.o
    · exact hF.g
    · exact hF.q
    · exact hF.gq

/-- What a copy of the point functions' `O` into `R` needs. -/
theorem copyR_conds (hJ : JLay J) :
    (∀ d ∈ [J.L.R.x, J.L.R.y, J.L.R.z, (ptAt J.L.M.n (oAt J.L.M.n)).x, (ptAt J.L.M.n (oAt J.L.M.n)).y,
      (ptAt J.L.M.n (oAt J.L.M.n)).z], d % 4 = 0) ∧
    (∀ d ∈ [J.L.R.x, J.L.R.y, J.L.R.z, (ptAt J.L.M.n (oAt J.L.M.n)).x, (ptAt J.L.M.n (oAt J.L.M.n)).y,
      (ptAt J.L.M.n (oAt J.L.M.n)).z], d + 8 * J.L.M.n ≤ 8192) ∧
    ((J.L.R.x + 8 * J.L.M.n ≤ J.L.R.y ∨ J.L.R.y + 8 * J.L.M.n ≤ J.L.R.x) ∧
      (J.L.R.x + 8 * J.L.M.n ≤ J.L.R.z ∨ J.L.R.z + 8 * J.L.M.n ≤ J.L.R.x) ∧
      (J.L.R.y + 8 * J.L.M.n ≤ J.L.R.z ∨ J.L.R.z + 8 * J.L.M.n ≤ J.L.R.y)) ∧
    (∀ d ∈ [J.L.R.x, J.L.R.y, J.L.R.z], ∀ e ∈ [(ptAt J.L.M.n (oAt J.L.M.n)).x, (ptAt J.L.M.n (oAt J.L.M.n)).y,
      (ptAt J.L.M.n (oAt J.L.M.n)).z], d + 8 * J.L.M.n ≤ e ∨ e + 8 * J.L.M.n ≤ d) := by
  have hL := hJ.lad
  obtain ⟨h1, h2, he, hb3, ha, hq, hp, hoo, ho1, h8⟩ := lay_nums hL.k3 hL.k6
  obtain ⟨-, -, -, -, -, rxl, ryl, rzl⟩ := hL.al
  have rx := hL.rx; have ry := hL.ry; have rz := hL.rz
  refine ⟨?_, ?_, hL.rne, ?_⟩ <;>
    simp only [ptAt, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] <;> omega_arith

/-- `O = P + Q`, `R = O`. -/
theorem add_ok {G Q : Point C} {u v : Nat} {S : Impl.Weierstrass.Mont.Modulus}
    (hkS : S.k = J.L.M.n) (hmS : S.m = C.p) (hM : ModOk J.L.M.n C.p) (hodd : C.p % 2 = 1)
    (hC : Law C) (hG : onCurve C G = true) (hQ : onCurve C Q = true) (hJ : JLay J)
    {s₀ : State} (hF : JFix J C base G Q u v s₀) {j : Nat} (hj : 1 ≤ j) {s₉ : State}
    (h : Mid2 J C base G Q u v s₀ j s₉) :
    WP isa (.seq (ptCall S false) (.block (copyPt J.L.M.n J.L.R J.fO))) s₉
      (JInv J C base G Q u v s₀ · (j - 1)) := by
  obtain ⟨c, w, m', k', d⟩ := S
  dsimp only at hkS hmS
  subst hkS hmS
  have hL := hJ.lad
  have hk3 := hL.k3
  have hk6 := hL.k6
  obtain ⟨h1, h2, he, hb3, ha, hq, hp, hoo, ho1, h8⟩ := lay_nums hk3 hk6
  have hn := h.ws.nowrap
  have la : wordsVal s₉.mem base (aAt J.L.M.n) J.L.M.n < C.p := by rw [h.ab.1]; exact hF.lt _ (by simp)
  have lb : wordsVal s₉.mem base (b3At J.L.M.n) J.L.M.n < C.p := by rw [h.ab.2]; exact hF.lt _ (by simp)
  refine WP.seq (WP.mono (ptCall_ok (S := ⟨c, w, C.p, J.L.M.n, d⟩) hM hodd hk3 hk6 false (a0 := false) h.ws
    (rIds_lt_of false fun x hx => by
      simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact h.plt.1
      · exact h.plt.2.1
      · exact h.plt.2.2
      · exact h.qlt.1
      · exact h.qlt.2.1
      · exact h.qlt.2.2
      · exact la
      · exact lb)) fun s₁₀ ⟨k₁₀, O₁₀, L₁₀, E₁₀⟩ => ?_)
  dsimp only at k₁₀ O₁₀ L₁₀ E₁₀
  simp only [ptVal, Bool.false_eq_true, ↓reduceIte] at E₁₀
  simp only [Eb, enc_0, enc_1, enc_2, enc_3, enc_4, enc_5, enc_6, enc_7, enc_8, enc_9, enc_10,
    Bool.false_eq_true, ↓reduceIte] at E₁₀
  have hab : toM C.p (2 ^ (64 * J.L.M.n)) (wordsVal s₉.mem base (aAt J.L.M.n) J.L.M.n) = Fin.ofNat C.p C.a ∧
      toM C.p (2 ^ (64 * J.L.M.n)) (wordsVal s₉.mem base (b3At J.L.M.n) J.L.M.n) = Fin.ofNat C.p (3 * C.b) := by
    rw [h.ab.1, h.ab.2]; exact hF.ab
  rw [hab.1, hab.2] at E₁₀
  have hA := acc_curve hC hG hQ u v j
  have R₁₀ := hC.add (hC.onCurve_add hA hA) (entry_curve hC hG hQ _ _) h.prep h.qrep E₁₀.symm
  have l0 := L₁₀ 0 (by decide)
  have l1 := L₁₀ 1 (by decide)
  have l2 := L₁₀ 2 (by decide)
  rw [enc_0] at l0
  rw [enc_1] at l1
  rw [enc_2] at l2
  have w₁₀ := h.ws.of_rk (k₁₀.mono (rs' := powClob))
  have cR := copyR_conds hJ
  refine WP.mono (copyPt_ok w₁₀.ws w₁₀.at3 (n := J.L.M.n) (o := J.L.R) (a := ptAt J.L.M.n (oAt J.L.M.n))
    cR.1 cR.2.1 cR.2.2.1 cR.2.2.2) fun s₁₁ ⟨rx₁₁, ry₁₁, rz₁₁, k₁₁, O₁₁⟩ => ?_
  simp only [ptAt] at rx₁₁ ry₁₁ rz₁₁
  have rx := hL.rx; have ry := hL.ry; have rz := hL.rz
  have U₁₁ : Unch base [(J.L.R.x, 8 * J.L.M.n), (J.L.R.y, 8 * J.L.M.n), (J.L.R.z, 8 * J.L.M.n)]
      s₁₀.mem s₁₁.mem := O₁₁
  refine ⟨w₁₀.of_rk (k₁₁.rk (rs' := powClob)), by rw [k₁₁.gpr _ (by decide), k₁₀.gpr _ (by decide), h.r31],
    h.keep.trans ((k₁₀.mono (rs' := powClob)).trans (k₁₁.rk (rs' := powClob))),
    ((h.unch.trans (show Unch base _ s₉.mem s₁₀.mem from O₁₀)).trans U₁₁).cover (jW_cover fun w hw => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with (h | (rfl | rfl)) | (rfl | rfl | rfl)
      · exact .inr h
      · exact .inl ⟨by simp only; omega_arith, by simp only; omega_arith⟩
      · exact .inl ⟨by simp only; omega_arith, by simp only; omega_arith⟩
      all_goals exact .inr (by simp [jW])), ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [U₁₁.wordsVal (by ppc_apart) (by omega_arith),
      (show Unch base _ s₉.mem s₁₀.mem from O₁₀).wordsVal (by ppc_apart) (by omega_arith)]
    exact h.ab.1
  · rw [U₁₁.wordsVal (by ppc_apart) (by omega_arith),
      (show Unch base _ s₉.mem s₁₀.mem from O₁₀).wordsVal (by ppc_apart) (by omega_arith)]
    exact h.ab.2
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [rx₁₁]; exact l0
    · rw [ry₁₁]; exact l1
    · rw [rz₁₁]; exact l2
  · show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [rx₁₁, ry₁₁, rz₁₁, acc_step hC hG hQ u v (j - 1), Nat.sub_add_cancel hj]
    exact R₁₀

/-- An iteration. -/
theorem body_ok {G Q : Point C} {u v : Nat} {S : Impl.Weierstrass.Mont.Modulus}
    (hkS : S.k = J.L.M.n) (hmS : S.m = C.p) (hM : ModOk J.L.M.n C.p) (hodd : C.p % 2 = 1)
    (hC : Law C) (hG : onCurve C G = true) (hQ : onCurve C Q = true) (hJ : JLay J)
    {s₀ : State} (hF : JFix J C base G Q u v s₀) {j : Nat} {s : State} (hj : 1 ≤ j) (hjn : j ≤ J.L.nbits)
    (hI : JInv J C base G Q u v s₀ s j) :
    WP isa (J.body S) s fun s' => JInv J C base G Q u v s₀ s' (j - 1) := by
  rw [JointCfg.body]
  refine dbl_ok hkS hmS hM hodd hC hG hQ hJ hF hj hI fun t h => WP.seq ?_
  rw [show copyPt J.L.M.n J.fP J.fO ++ J.select =
      (copyPt J.L.M.n (ptAt J.L.M.n (pAt J.L.M.n)) (ptAt J.L.M.n (oAt J.L.M.n)) ++
        (bitMask J.L.bits ++ (selPt J.L.M.n J.L.T J.O J.L.G ++ selPt J.L.M.n J.L.D J.Q J.GQ))) ++
      (bitMask J.bitsV ++ selPt J.L.M.n (ptAt J.L.M.n (qAt J.L.M.n)) J.L.T J.L.D) by
    simp only [JointCfg.select, JointCfg.fP, JointCfg.fO, JointCfg.fQ, List.append_assoc]]
  rw [WP.block_append_iff]
  exact WP.mono (selU_ok hJ hF hj hjn h) fun t' h' => WP.mono (selV_ok hJ hF hj hjn h') fun t'' h'' =>
    add_ok hkS hmS hM hodd hC hG hQ hJ hF hj h''

/-- The loop, from a start `s₀` where `R` represents `O`: `R` represents
`[u]G + [v]Q` at the end. -/
theorem loop_ok {G Q : Point C} {u v : Nat} {S : Impl.Weierstrass.Mont.Modulus}
    (hkS : S.k = J.L.M.n) (hmS : S.m = C.p) (hM : ModOk J.L.M.n C.p) (hodd : C.p % 2 = 1)
    (hC : Law C) (hG : onCurve C G = true) (hQ : onCurve C Q = true) (hJ : JLay J)
    {s₀ : State} (hF : JFix J C base G Q u v s₀) (hw : WsReg s₀ base)
    (h31 : s₀.gpr .r31 = BitVec.ofNat 64 J.L.nbits) (hu : u < 2 ^ J.L.nbits) (hv : v < 2 ^ J.L.nbits)
    (hlt : ∀ x ∈ [J.L.R.x, J.L.R.y, J.L.R.z], wordsVal s₀.mem base x J.L.M.n < C.p)
    (hR : Rep C (tmv C J.L.M.n base s₀ J.L.R.x) (tmv C J.L.M.n base s₀ J.L.R.y) (tmv C J.L.M.n base s₀ J.L.R.z)
      .infinity) :
    WP isa (.loop (J.body S) more) s₀ fun s' => Rk powClob s₀ s' ∧ Unch base (jW J) s₀.mem s'.mem ∧
      (∀ x ∈ [J.L.R.x, J.L.R.y, J.L.R.z], wordsVal s'.mem base x J.L.M.n < C.p) ∧
      Rep C (tmv C J.L.M.n base s' J.L.R.x) (tmv C J.L.M.n base s' J.L.R.y) (tmv C J.L.M.n base s' J.L.R.z)
        (add (mul u G) (mul v Q)) := by
  have hnb := hJ.lad.nbits
  have top : acc G Q u v J.L.nbits = .infinity := by
    have h0 : ∀ X : Point C, mul 0 X = .infinity := fun X => by rw [Spec.Weierstrass.mul]; rfl
    rw [acc, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hu, Nat.div_eq_of_lt hv,
      h0, h0]
    rfl
  refine countLoop_ok (Inv := fun j s' => JInv J C base G Q u v s₀ s' j) (n := J.L.nbits)
    (fun j s' hi => hi.r31)
    (fun j s' h1 h2 hi => body_ok hkS hmS hM hodd hC hG hQ hJ hF h1 h2 hi)
    (fun s' hi => ⟨hi.keep, hi.unch, hi.lt, by
      have := hi.rep
      rwa [acc, Nat.shiftRight_zero, Nat.shiftRight_zero] at this⟩) hnb.1 (by omega_arith)
    ⟨hw, h31, Rk.refl _ _, Unch.refl _ _ _, ⟨rfl, rfl⟩, hlt, by rw [top]; exact hR⟩

/-- After the setup and the first addition: the point functions' `a` and
`3b` hold the start's, and `O` holds `G + Q`. -/
structure SetPost (J : JointCfg) (C : Curve) (base : Addr) (G Q : Point C) (s t : State) : Prop where
  ws : WsReg t base
  keep : Rk powClob s t
  unch : Unch base [(oAt J.L.M.n, 4096 - oAt J.L.M.n)] s.mem t.mem
  ab : wordsVal t.mem base (aAt J.L.M.n) J.L.M.n = wordsVal s.mem base J.L.S.a J.L.M.n ∧
    wordsVal t.mem base (b3At J.L.M.n) J.L.M.n = wordsVal s.mem base J.L.S.b3 J.L.M.n
  lt : wordsVal t.mem base (oAt J.L.M.n) J.L.M.n < C.p ∧
    wordsVal t.mem base (oAt J.L.M.n + elemBytes J.L.M.n) J.L.M.n < C.p ∧
    wordsVal t.mem base (oAt J.L.M.n + 2 * elemBytes J.L.M.n) J.L.M.n < C.p
  rep : Rep C (tmv C J.L.M.n base t (oAt J.L.M.n)) (tmv C J.L.M.n base t (oAt J.L.M.n + elemBytes J.L.M.n))
    (tmv C J.L.M.n base t (oAt J.L.M.n + 2 * elemBytes J.L.M.n)) (add G Q)

/-- `a`, `3b`, `G` and `Q` to the point functions' slots, and `O = G + Q`. -/
theorem setup_ok {G Q : Point C} {S : Impl.Weierstrass.Mont.Modulus}
    (hkS : S.k = J.L.M.n) (hmS : S.m = C.p) (hM : ModOk J.L.M.n C.p) (hodd : C.p % 2 = 1)
    (hC : Law C) (hG : onCurve C G = true) (hQ : onCurve C Q = true) (hJ : JLay J) {s : State}
    (hw : WsReg s base)
    (hlt : ∀ x ∈ [J.L.S.a, J.L.S.b3, J.L.G.x, J.L.G.y, J.L.G.z, J.Q.x, J.Q.y, J.Q.z],
      wordsVal s.mem base x J.L.M.n < C.p)
    (hab : tmv C J.L.M.n base s J.L.S.a = Fin.ofNat C.p C.a ∧
      tmv C J.L.M.n base s J.L.S.b3 = Fin.ofNat C.p (3 * C.b))
    (hg : Rep C (tmv C J.L.M.n base s J.L.G.x) (tmv C J.L.M.n base s J.L.G.y) (tmv C J.L.M.n base s J.L.G.z) G)
    (hq : Rep C (tmv C J.L.M.n base s J.Q.x) (tmv C J.L.M.n base s J.Q.y) (tmv C J.L.M.n base s J.Q.z) Q)
    {rest : Prog isa} {Q' : State → Prop} (k : ∀ t, SetPost J C base G Q s t → WP isa rest t Q') :
    WP isa (.seq (.block J.setup) (.seq (ptCall S false) rest)) s Q' := by
  obtain ⟨c, w, m', k', d⟩ := S
  dsimp only at hkS hmS
  subst hkS hmS
  have hL := hJ.lad
  have hk3 := hL.k3
  have hk6 := hL.k6
  obtain ⟨h1, h2, he, hb3, ha, hq', hp, hoo, ho1, h8⟩ := lay_nums hk3 hk6
  have hn := hw.nowrap
  obtain ⟨al, bl, gxl, gyl, gzl, -, -, -⟩ := hL.al
  have sa := hL.a; have sb := hL.b3; have sgx := hL.gx; have sgy := hL.gy; have sgz := hL.gz
  have qsub : ∀ x ∈ [J.Q.x, J.Q.y, J.Q.z], x ∈ roL J ++ tL J ++ dL J := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [roL]
  have qL := low_of hJ qsub
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at qL
  obtain ⟨⟨qx1, qx2⟩, ⟨qy1, qy2⟩, ⟨qz1, qz2⟩⟩ := qL
  have cG := copyPt_conds (a := J.L.G) hk3 hk6 (.inl rfl) (by omega_arith) (by omega_arith) (by omega_arith)
    ⟨gxl, gyl, gzl⟩
  have cQ := copyPt_conds (a := J.Q) hk3 hk6 (.inr rfl) (by omega_arith) (by omega_arith) (by omega_arith)
    ⟨qx2, qy2, qz2⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlt
  obtain ⟨la, lb, lgx, lgy, lgz, lqx, lqy, lqz⟩ := hlt
  refine WP.seq ?_
  rw [JointCfg.setup, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (copy_ok J.L.M.n hw.ws hw.at3 (o := aAt J.L.M.n) (a := J.L.S.a) (by omega_arith) al
    (by omega_arith) (by omega_arith) (by omega_arith)) fun s₁ ⟨a₁, k₁, O₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok J.L.M.n (k₁.ws hw.ws) (k₁.at hw.at3) (o := b3At J.L.M.n) (a := J.L.S.b3)
    (by omega_arith) bl (by omega_arith) (by omega_arith) (by omega_arith)) fun s₂ ⟨b₂, k₂, O₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copyPt_ok (k₂.ws (k₁.ws hw.ws)) (k₂.at (k₁.at hw.at3)) (n := J.L.M.n)
    (o := ptAt J.L.M.n (pAt J.L.M.n)) (a := J.L.G) cG.1 cG.2.1 cG.2.2.1 cG.2.2.2)
    fun s₃ ⟨gx₃, gy₃, gz₃, k₃, O₃⟩ => ?_
  refine WP.mono (copyPt_ok (k₃.ws (k₂.ws (k₁.ws hw.ws))) (k₃.at (k₂.at (k₁.at hw.at3))) (n := J.L.M.n)
    (o := ptAt J.L.M.n (qAt J.L.M.n)) (a := J.Q) cQ.1 cQ.2.1 cQ.2.2.1 cQ.2.2.2)
    fun s₄ ⟨qx₄, qy₄, qz₄, k₄, O₄⟩ => ?_
  simp only [ptAt] at gx₃ gy₃ gz₃ O₃ qx₄ qy₄ qz₄ O₄
  have U₂ : Unch base [(aAt J.L.M.n, 8 * J.L.M.n)] s.mem s₁.mem := O₁.unch
  have U₃ : Unch base [(b3At J.L.M.n, 8 * J.L.M.n)] s₁.mem s₂.mem := O₂.unch
  have U₄ : Unch base [(pAt J.L.M.n, 8 * J.L.M.n), (pAt J.L.M.n + elemBytes J.L.M.n, 8 * J.L.M.n),
      (pAt J.L.M.n + 2 * elemBytes J.L.M.n, 8 * J.L.M.n)] s₂.mem s₃.mem := O₃
  have U₅ : Unch base [(qAt J.L.M.n, 8 * J.L.M.n), (qAt J.L.M.n + elemBytes J.L.M.n, 8 * J.L.M.n),
      (qAt J.L.M.n + 2 * elemBytes J.L.M.n, 8 * J.L.M.n)] s₃.mem s₄.mem := O₄
  have lo : ∀ {x : Nat}, x + 8 * J.L.M.n ≤ oAt J.L.M.n →
      wordsVal s₂.mem base x J.L.M.n = wordsVal s.mem base x J.L.M.n := fun h =>
    (U₃.wordsVal (by ppc_apart) (by omega_arith)).trans (U₂.wordsVal (by ppc_apart) (by omega_arith))
  have lo3 : ∀ {x : Nat}, x + 8 * J.L.M.n ≤ oAt J.L.M.n →
      wordsVal s₃.mem base x J.L.M.n = wordsVal s.mem base x J.L.M.n := fun h =>
    (U₄.wordsVal (by ppc_apart) (by omega_arith)).trans (lo h)
  -- What the call reads.
  have a₄ : wordsVal s₄.mem base (aAt J.L.M.n) J.L.M.n = wordsVal s.mem base J.L.S.a J.L.M.n := by
    rw [U₅.wordsVal (by ppc_apart) (by omega_arith), U₄.wordsVal (by ppc_apart) (by omega_arith),
      U₃.wordsVal (by ppc_apart) (by omega_arith), a₁]
  have b₄ : wordsVal s₄.mem base (b3At J.L.M.n) J.L.M.n = wordsVal s.mem base J.L.S.b3 J.L.M.n := by
    rw [U₅.wordsVal (by ppc_apart) (by omega_arith), U₄.wordsVal (by ppc_apart) (by omega_arith), b₂,
      U₂.wordsVal (by ppc_apart) (by omega_arith)]
  have p₄ : ∀ i < 3, wordsVal s₄.mem base (pAt J.L.M.n + i * elemBytes J.L.M.n) J.L.M.n =
      wordsVal s₃.mem base (pAt J.L.M.n + i * elemBytes J.L.M.n) J.L.M.n := fun i hi => by
    obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    all_goals exact U₅.wordsVal (by ppc_apart) (by omega_arith)
  have gx₄ : wordsVal s₄.mem base (pAt J.L.M.n) J.L.M.n = wordsVal s.mem base J.L.G.x J.L.M.n := by
    have := p₄ 0 (by decide); simp only [Nat.zero_mul, Nat.add_zero] at this
    rw [this, gx₃, lo sgx]
  have gy₄ : wordsVal s₄.mem base (pAt J.L.M.n + elemBytes J.L.M.n) J.L.M.n =
      wordsVal s.mem base J.L.G.y J.L.M.n := by
    have := p₄ 1 (by decide); simp only [Nat.one_mul] at this
    rw [this, gy₃, lo sgy]
  have gz₄ : wordsVal s₄.mem base (pAt J.L.M.n + 2 * elemBytes J.L.M.n) J.L.M.n =
      wordsVal s.mem base J.L.G.z J.L.M.n := by
    rw [p₄ 2 (by decide), gz₃, lo sgz]
  rw [lo3 qx1] at qx₄
  rw [lo3 qy1] at qy₄
  rw [lo3 qz1] at qz₄
  have w₄ := hw.of_rk ((k₁.rk (rs' := powClob)).trans ((k₂.rk (rs' := powClob)).trans ((k₃.rk (rs' := powClob)).trans
    (k₄.rk (rs' := powClob)))))
  refine WP.seq (WP.mono (ptCall_ok (S := ⟨c, w, C.p, J.L.M.n, d⟩) hM hodd hk3 hk6 false (a0 := false) w₄
    (rIds_lt_of false fun x hx => by
      simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [gx₄]; exact lgx
      · rw [gy₄]; exact lgy
      · rw [gz₄]; exact lgz
      · rw [qx₄]; exact lqx
      · rw [qy₄]; exact lqy
      · rw [qz₄]; exact lqz
      · rw [a₄]; exact la
      · rw [b₄]; exact lb)) fun s₅ ⟨k₅, O₅, L₅, E₅⟩ => ?_)
  dsimp only at k₅ O₅ L₅ E₅
  simp only [ptVal, Bool.false_eq_true, ↓reduceIte] at E₅
  simp only [Eb, enc_0, enc_1, enc_2, enc_3, enc_4, enc_5, enc_6, enc_7, enc_8, enc_9, enc_10,
    Bool.false_eq_true, ↓reduceIte] at E₅
  have ha' : toM C.p (2 ^ (64 * J.L.M.n)) (wordsVal s.mem base J.L.S.a J.L.M.n) = Fin.ofNat C.p C.a := hab.1
  have hb' : toM C.p (2 ^ (64 * J.L.M.n)) (wordsVal s.mem base J.L.S.b3 J.L.M.n) = Fin.ofNat C.p (3 * C.b) :=
    hab.2
  rw [a₄, b₄, gx₄, gy₄, gz₄, qx₄, qy₄, qz₄, ha', hb'] at E₅
  have l0 := L₅ 0 (by decide)
  have l1 := L₅ 1 (by decide)
  have l2 := L₅ 2 (by decide)
  rw [enc_0] at l0
  rw [enc_1] at l1
  rw [enc_2] at l2
  have U₆ : Unch base [(oAt J.L.M.n, 3 * elemBytes J.L.M.n), (ownAt J.L.M.n, 4096 - ownAt J.L.M.n)]
      s₄.mem s₅.mem := O₅
  refine k s₅ ⟨w₄.of_rk (k₅.mono (rs' := powClob)),
    ((k₁.rk (rs' := powClob)).trans ((k₂.rk (rs' := powClob)).trans ((k₃.rk (rs' := powClob)).trans
      ((k₄.rk (rs' := powClob)).trans (k₅.mono (rs' := powClob)))))),
    ((((U₂.trans U₃).trans U₄).trans U₅).trans U₆).cover (pt_cover hk3 hk6 fun w hw => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with ((((rfl | rfl) | rfl | rfl | rfl) | rfl | rfl | rfl) | rfl | rfl) <;>
        (simp only; omega_arith)), ⟨?_, ?_⟩, ⟨l0, l1, l2⟩, hC.add hG hQ hg hq E₅.symm⟩
  · rw [U₆.wordsVal (by ppc_apart) (by omega_arith)]; exact a₄
  · rw [U₆.wordsVal (by ppc_apart) (by omega_arith)]; exact b₄

/-- What the start writes: `G + Q`'s slots and `R`'s. -/
abbrev startW (J : JointCfg) : List (Nat × Nat) :=
  [(J.GQ.x, 8 * J.L.M.n), (J.GQ.y, 8 * J.L.M.n), (J.GQ.z, 8 * J.L.M.n),
    (J.L.R.x, 8 * J.L.M.n), (J.L.R.y, 8 * J.L.M.n), (J.L.R.z, 8 * J.L.M.n)]

/-- What the loop needs at its start, from the start block. -/
structure StartPost (J : JointCfg) (C : Curve) (base : Addr) (G Q : Point C) (u v : Nat) (t s₀ : State) :
    Prop where
  fix : JFix J C base G Q u v s₀
  ws : WsReg s₀ base
  r31 : s₀.gpr .r31 = BitVec.ofNat 64 J.L.nbits
  lt : ∀ x ∈ [J.L.R.x, J.L.R.y, J.L.R.z], wordsVal s₀.mem base x J.L.M.n < C.p
  rep : Rep C (tmv C J.L.M.n base s₀ J.L.R.x) (tmv C J.L.M.n base s₀ J.L.R.y) (tmv C J.L.M.n base s₀ J.L.R.z)
    .infinity
  keep : Rk powClob t s₀
  unch : Unch base (startW J) t.mem s₀.mem

/-- The slots the loop only reads but `G + Q`'s lie apart from what the start
writes. -/
theorem start_apart (hJ : JLay J) :
    ∀ d ∈ [J.L.G.x, J.L.G.y, J.L.G.z, J.Q.x, J.Q.y, J.Q.z, J.O.x, J.O.y, J.O.z],
      ∀ y ∈ [J.GQ.x, J.GQ.y, J.GQ.z, J.L.R.x, J.L.R.y, J.L.R.z], Apart J.L.M.n d y := by
  intro d hd y hy
  have hd' : d ∈ roL J := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [roL]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hJ.gq.2 _ (by simp) d hd).symm
  · exact (hJ.gq.2 _ (by simp) d hd).symm
  · exact (hJ.gq.2 _ (by simp) d hd).symm
  · exact hJ.ro d hd' _ (by simp [wL])
  · exact hJ.ro d hd' _ (by simp [wL])
  · exact hJ.ro d hd' _ (by simp [wL])

/-- `G + Q`'s slots and `R`'s are below the point functions'. -/
theorem start_low (hJ : JLay J) : ∀ w ∈ startW J, w.1 + w.2 ≤ oAt J.L.M.n ∧ w.2 = 8 * J.L.M.n := by
  intro w hw
  simp only [startW, List.mem_cons, List.not_mem_nil, or_false] at hw
  have hL := hJ.lad
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨(hJ.low _ (by simp [roL])).1, rfl⟩
  · exact ⟨(hJ.low _ (by simp [roL])).1, rfl⟩
  · exact ⟨(hJ.low _ (by simp [roL])).1, rfl⟩
  · exact ⟨hL.rx, rfl⟩
  · exact ⟨hL.ry, rfl⟩
  · exact ⟨hL.rz, rfl⟩

/-- `G + Q`'s slots apart from `R`'s. -/
theorem start_gR (hJ : JLay J) :
    ∀ g ∈ [J.GQ.x, J.GQ.y, J.GQ.z], ∀ r ∈ [J.L.R.x, J.L.R.y, J.L.R.z], Apart J.L.M.n g r := by
  intro g hg r hr
  have hg' : g ∈ roL J := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> simp [roL]
  have hr' : r ∈ wL J := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [wL]
  exact hJ.ro g hg' r hr'

/-- What the start block does. -/
structure StartRun (J : JointCfg) (base : Addr) (t s₀ : State) : Prop where
  keep : Kp powClob t s₀
  unch : Unch base (startW J) t.mem s₀.mem
  r31 : s₀.gpr .r31 = BitVec.ofNat 64 J.L.nbits
  rx : wordsVal s₀.mem base J.L.R.x J.L.M.n = 0
  ry : wordsVal s₀.mem base J.L.R.y J.L.M.n = J.one
  rz : wordsVal s₀.mem base J.L.R.z J.L.M.n = 0
  gx : wordsVal s₀.mem base J.GQ.x J.L.M.n = wordsVal t.mem base (oAt J.L.M.n) J.L.M.n
  gy : wordsVal s₀.mem base J.GQ.y J.L.M.n = wordsVal t.mem base (oAt J.L.M.n + elemBytes J.L.M.n) J.L.M.n
  gz : wordsVal s₀.mem base J.GQ.z J.L.M.n = wordsVal t.mem base (oAt J.L.M.n + 2 * elemBytes J.L.M.n) J.L.M.n

theorem start_run (hJ : JLay J) {t : State} (hw : WsReg t base) (hone' : J.one < 2 ^ (64 * J.L.M.n)) :
    WP isa (.block J.start) t (StartRun J base t) := by
  have hL := hJ.lad
  have hk3 := hL.k3
  have hk6 := hL.k6
  obtain ⟨h1, h2, he, hb3, ha, hq', hp', hoo, ho1, h8⟩ := lay_nums hk3 hk6
  have hn := hw.nowrap
  have hnb := hL.nbits
  have rx := hL.rx; have ry := hL.ry; have rz := hL.rz
  have gqs : ∀ x ∈ [J.GQ.x, J.GQ.y, J.GQ.z], x ∈ roL J ++ tL J ++ dL J := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [roL]
  have gqL := low_of hJ gqs
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at gqL
  obtain ⟨⟨gx1, gx2⟩, ⟨gy1, gy2⟩, ⟨gz1, gz2⟩⟩ := gqL
  rw [JointCfg.start]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (copyPt_ok hw.ws hw.at3 (n := J.L.M.n) (o := J.GQ) (a := ptAt J.L.M.n (oAt J.L.M.n))
    (by simp only [ptAt, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_arith)
    (by simp only [ptAt, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_arith)
    hJ.gq.1
    (by simp only [ptAt, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_arith))
    fun s₁ ⟨x₁, y₁, z₁, k₁, O₁⟩ => ?_
  simp only [ptAt] at x₁ y₁ z₁
  rw [WP.block_append_iff]
  refine WP.mono (setConst_ok (k₁.ws hw.ws) (k₁.at hw.at3) (n := J.L.M.n) (o := J.L.R.x) (x := 0)
    (by omega_arith) (Nat.two_pow_pos _)) fun s₂ ⟨O₂, v₂, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (setConst_ok (k₂.ws (k₁.ws hw.ws)) (k₂.at (k₁.at hw.at3)) (n := J.L.M.n) (o := J.L.R.y)
    (x := J.one) (by omega_arith) hone') fun s₃ ⟨O₃, v₃, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (setConst_ok (k₃.ws (k₂.ws (k₁.ws hw.ws))) (k₃.at (k₂.at (k₁.at hw.at3))) (n := J.L.M.n)
    (o := J.L.R.z) (x := 0) (by omega_arith) (Nat.two_pow_pos _)) fun s₄ ⟨O₄, v₄, k₄⟩ =>
    wp_step (exec_li hnb.2) (WP.block_nil ?_)
  have U₁ : Unch base [(J.GQ.x, 8 * J.L.M.n), (J.GQ.y, 8 * J.L.M.n), (J.GQ.z, 8 * J.L.M.n)] t.mem s₁.mem := O₁
  have gR := start_gR hJ
  have hRR := hL.rne
  have gq : ∀ {g f : Nat}, g ∈ [J.GQ.x, J.GQ.y, J.GQ.z] →
      wordsVal s₁.mem base g J.L.M.n = wordsVal t.mem base f J.L.M.n →
      wordsVal s₄.mem base g J.L.M.n = wordsVal t.mem base f J.L.M.n := by
    intro g f hg e
    have l := (start_low hJ (g, 8 * J.L.M.n) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl <;> simp)).1
    simp only at l
    rw [O₄.wordsVal (gR g hg _ (by simp)) (by omega_arith),
      O₃.wordsVal (gR g hg _ (by simp)) (by omega_arith), O₂.wordsVal (gR g hg _ (by simp)) (by omega_arith), e]
  refine ⟨(k₁.mono (by decide)).trans ((k₂.mono (by decide)).trans ((k₃.mono (by decide)).trans
      ((k₄.mono (by decide)).trans (Kp.write _ _ (by decide))))), ?_, by simp only [write_gpr, ite_true],
    ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [write_mem]
  · exact ((U₁.trans O₂.unch).trans O₃.unch).trans O₄.unch |>.mono fun w hw => by
      simpa only [List.cons_append, List.nil_append] using hw
  · rw [O₄.wordsVal hRR.2.1 (by omega_arith), O₃.wordsVal hRR.1 (by omega_arith), wordsVal_eq_val32, v₂]
  · rw [O₄.wordsVal hRR.2.2 (by omega_arith), wordsVal_eq_val32, v₃]
  · rw [wordsVal_eq_val32, v₄]
  · exact gq (by simp) x₁
  · exact gq (by simp) y₁
  · exact gq (by simp) z₁

/-- `G + Q` from `O` to its slots, `R = (0 : 1 : 0)`, and the counter. -/
theorem start_ok {G Q : Point C} {u v : Nat} (hC : Law C) (hJ : JLay J) {t : State} (hw : WsReg t base)
    (hab : tmv C J.L.M.n base t (aAt J.L.M.n) = Fin.ofNat C.p C.a ∧
      tmv C J.L.M.n base t (b3At J.L.M.n) = Fin.ofNat C.p (3 * C.b))
    (hlt : ∀ x ∈ [aAt J.L.M.n, b3At J.L.M.n, J.L.G.x, J.L.G.y, J.L.G.z, J.Q.x, J.Q.y, J.Q.z,
      oAt J.L.M.n, oAt J.L.M.n + elemBytes J.L.M.n, oAt J.L.M.n + 2 * elemBytes J.L.M.n, J.O.x, J.O.y, J.O.z],
      wordsVal t.mem base x J.L.M.n < C.p)
    (hg : Rep C (tmv C J.L.M.n base t J.L.G.x) (tmv C J.L.M.n base t J.L.G.y) (tmv C J.L.M.n base t J.L.G.z) G)
    (hq : Rep C (tmv C J.L.M.n base t J.Q.x) (tmv C J.L.M.n base t J.Q.y) (tmv C J.L.M.n base t J.Q.z) Q)
    (hgq : Rep C (tmv C J.L.M.n base t (oAt J.L.M.n)) (tmv C J.L.M.n base t (oAt J.L.M.n + elemBytes J.L.M.n))
      (tmv C J.L.M.n base t (oAt J.L.M.n + 2 * elemBytes J.L.M.n)) (add G Q))
    (ho : Rep C (tmv C J.L.M.n base t J.O.x) (tmv C J.L.M.n base t J.O.y) (tmv C J.L.M.n base t J.O.z)
      .infinity)
    (hbu : ∀ i < J.L.nbits, t.mem (off base (J.L.bits + i)) = if u.testBit i then 1 else 0)
    (hbv : ∀ i < J.L.nbits, t.mem (off base (J.bitsV + i)) = if v.testBit i then 1 else 0)
    (hp : 0 < C.p) (hone : J.one < C.p ∧ toM C.p (2 ^ (64 * J.L.M.n)) J.one = 1)
    (hone' : J.one < 2 ^ (64 * J.L.M.n)) :
    WP isa (.block J.start) t (StartPost J C base G Q u v t) := by
  refine WP.mono (start_run hJ hw hone') fun s₀ R => ?_
  have hL := hJ.lad
  have hk3 := hL.k3
  have hk6 := hL.k6
  obtain ⟨h1, h2, he, hb3, ha, hq', hp', hoo, ho1, h8⟩ := lay_nums hk3 hk6
  have hn := hw.nowrap
  have low := start_low hJ
  have keep : ∀ {d : Nat}, (∀ y ∈ [J.GQ.x, J.GQ.y, J.GQ.z, J.L.R.x, J.L.R.y, J.L.R.z], Apart J.L.M.n d y) →
      d + 8 * J.L.M.n ≤ 8192 → wordsVal s₀.mem base d J.L.M.n = wordsVal t.mem base d J.L.M.n :=
    fun hd hd' => R.unch.wordsVal (fun w hw => by
      simp only [startW, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hd _ (by simp)) (by omega_arith)
  have roLow : ∀ d ∈ [J.L.G.x, J.L.G.y, J.L.G.z, J.Q.x, J.Q.y, J.Q.z, J.O.x, J.O.y, J.O.z],
      d + 8 * J.L.M.n ≤ 8192 := fun d hd => by
    have : d + 8 * J.L.M.n ≤ oAt J.L.M.n := (hJ.low d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [roL])).1
    omega_arith
  have kp : ∀ d ∈ [J.L.G.x, J.L.G.y, J.L.G.z, J.Q.x, J.Q.y, J.Q.z, J.O.x, J.O.y, J.O.z],
      wordsVal s₀.mem base d J.L.M.n = wordsVal t.mem base d J.L.M.n :=
    fun d hd => keep (start_apart hJ d hd) (roLow d hd)
  have kab : ∀ d ∈ [aAt J.L.M.n, b3At J.L.M.n],
      wordsVal s₀.mem base d J.L.M.n = wordsVal t.mem base d J.L.M.n := fun d hd =>
    R.unch.wordsVal (fun w hw => by
      obtain ⟨l1, l2⟩ := low w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      right; rcases hd with rfl | rfl <;> omega_arith) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl <;> omega_arith)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at kp kab hlt
  obtain ⟨kgx, kgy, kgz, kqx, kqy, kqz, kox, koy, koz⟩ := kp
  obtain ⟨ka, kb⟩ := kab
  obtain ⟨la, lb, lgx, lgy, lgz, lqx, lqy, lqz, lfx, lfy, lfz, lox, loy, loz⟩ := hlt
  have tc : ∀ {s s' : State} {x y : Nat}, wordsVal s.mem base x J.L.M.n = wordsVal s'.mem base y J.L.M.n →
      tmv C J.L.M.n base s x = tmv C J.L.M.n base s' y := fun e => by
    show toM _ _ _ = toM _ _ _; rw [e]
  have by4 : ∀ {d : Nat}, 4096 ≤ d → d < 8192 → s₀.mem (off base d) = t.mem (off base d) := fun h1 h2 =>
    R.unch.byte (fun w hw => by
      obtain ⟨l1, -⟩ := low w hw
      right; omega_arith) (by omega_arith)
  have hbV := hJ.bitsV
  have hbL := hL.bits
  have hbE := hL.bitsE
  refine ⟨⟨⟨by rw [tc ka]; exact hab.1, by rw [tc kb]; exact hab.2⟩, ?_, by rw [tc kgx, tc kgy, tc kgz]; exact hg,
    by rw [tc kqx, tc kqy, tc kqz]; exact hq, by rw [tc R.gx, tc R.gy, tc R.gz]; exact hgq,
    by rw [tc kox, tc koy, tc koz]; exact ho, fun i hi => by rw [by4 (by omega) (by omega)]; exact hbu i hi,
    fun i hi => by rw [by4 (by omega) (by omega)]; exact hbv i hi⟩,
    hw.of_rk (R.keep.rk (rs' := powClob)), R.r31, ?_, ?_, R.keep.rk, R.unch⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [ka]; exact la
    · rw [kb]; exact lb
    · rw [kgx]; exact lgx
    · rw [kgy]; exact lgy
    · rw [kgz]; exact lgz
    · rw [kqx]; exact lqx
    · rw [kqy]; exact lqy
    · rw [kqz]; exact lqz
    · rw [R.gx]; exact lfx
    · rw [R.gy]; exact lfy
    · rw [R.gz]; exact lfz
    · rw [kox]; exact lox
    · rw [koy]; exact loy
    · rw [koz]; exact loz
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [R.rx]; exact hp
    · rw [R.ry]; exact hone.1
    · rw [R.rz]; exact hp
  · show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [R.rx, R.ry, R.rz, toM_zero, hone.2]
    exact rep_infinity' hC

/-- What the joint multiplication writes: the loop's slots, and `G + Q`'s. -/
def jointW (J : JointCfg) : List (Nat × Nat) :=
  jW J ++ [(J.GQ.x, 8 * J.L.M.n), (J.GQ.y, 8 * J.L.M.n), (J.GQ.z, 8 * J.L.M.n)]

theorem jointW_cover : ∀ w ∈ ([(oAt J.L.M.n, 4096 - oAt J.L.M.n)] ++ startW J) ++ jW J, w ∈ jointW J := by
  intro w hw
  simp only [List.mem_append] at hw
  rcases hw with (h | h) | h
  · exact List.mem_append_left _ (by simp at h; simp [jW, h])
  · simp only [startW, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [jointW, jW]
  · exact List.mem_append_left _ h

/-- What the setup leaves for the start: the setup's facts, at its end `t`. -/
theorem setPost_start {G Q : Point C} {u v : Nat} (hJ : JLay J) {s t : State} (hw : WsReg s base)
    (ht : SetPost J C base G Q s t)
    (hlt : ∀ x ∈ [J.L.S.a, J.L.S.b3, J.L.G.x, J.L.G.y, J.L.G.z, J.Q.x, J.Q.y, J.Q.z, J.O.x, J.O.y, J.O.z],
      wordsVal s.mem base x J.L.M.n < C.p)
    (hab : tmv C J.L.M.n base s J.L.S.a = Fin.ofNat C.p C.a ∧
      tmv C J.L.M.n base s J.L.S.b3 = Fin.ofNat C.p (3 * C.b))
    (hg : Rep C (tmv C J.L.M.n base s J.L.G.x) (tmv C J.L.M.n base s J.L.G.y) (tmv C J.L.M.n base s J.L.G.z) G)
    (hq : Rep C (tmv C J.L.M.n base s J.Q.x) (tmv C J.L.M.n base s J.Q.y) (tmv C J.L.M.n base s J.Q.z) Q)
    (ho : Rep C (tmv C J.L.M.n base s J.O.x) (tmv C J.L.M.n base s J.O.y) (tmv C J.L.M.n base s J.O.z)
      .infinity)
    (hbu : ∀ i < J.L.nbits, s.mem (off base (J.L.bits + i)) = if u.testBit i then 1 else 0)
    (hbv : ∀ i < J.L.nbits, s.mem (off base (J.bitsV + i)) = if v.testBit i then 1 else 0) :
    (tmv C J.L.M.n base t (aAt J.L.M.n) = Fin.ofNat C.p C.a ∧
      tmv C J.L.M.n base t (b3At J.L.M.n) = Fin.ofNat C.p (3 * C.b)) ∧
    (∀ x ∈ [aAt J.L.M.n, b3At J.L.M.n, J.L.G.x, J.L.G.y, J.L.G.z, J.Q.x, J.Q.y, J.Q.z,
      oAt J.L.M.n, oAt J.L.M.n + elemBytes J.L.M.n, oAt J.L.M.n + 2 * elemBytes J.L.M.n, J.O.x, J.O.y, J.O.z],
      wordsVal t.mem base x J.L.M.n < C.p) ∧
    Rep C (tmv C J.L.M.n base t J.L.G.x) (tmv C J.L.M.n base t J.L.G.y) (tmv C J.L.M.n base t J.L.G.z) G ∧
    Rep C (tmv C J.L.M.n base t J.Q.x) (tmv C J.L.M.n base t J.Q.y) (tmv C J.L.M.n base t J.Q.z) Q ∧
    Rep C (tmv C J.L.M.n base t J.O.x) (tmv C J.L.M.n base t J.O.y) (tmv C J.L.M.n base t J.O.z) .infinity ∧
    (∀ i < J.L.nbits, t.mem (off base (J.L.bits + i)) = if u.testBit i then 1 else 0) ∧
    (∀ i < J.L.nbits, t.mem (off base (J.bitsV + i)) = if v.testBit i then 1 else 0) := by
  have hL := hJ.lad
  have hn := hw.nowrap
  have hk3 := hL.k3
  have hk6 := hL.k6
  obtain ⟨h1, h2, he, hb3, ha, hq', hp', hoo, ho1, h8⟩ := lay_nums hk3 hk6
  have lo : ∀ {d : Nat}, d + 8 * J.L.M.n ≤ oAt J.L.M.n →
      wordsVal t.mem base d J.L.M.n = wordsVal s.mem base d J.L.M.n := fun hd =>
    ht.unch.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; subst hw; left; exact hd) (by omega_arith)
  have rl : ∀ d ∈ [J.L.G.x, J.L.G.y, J.L.G.z, J.Q.x, J.Q.y, J.Q.z, J.O.x, J.O.y, J.O.z],
      wordsVal t.mem base d J.L.M.n = wordsVal s.mem base d J.L.M.n := fun d hd => lo (hJ.low d (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [roL])).1
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at rl hlt
  obtain ⟨kgx, kgy, kgz, kqx, kqy, kqz, kox, koy, koz⟩ := rl
  obtain ⟨la, lb, lgx, lgy, lgz, lqx, lqy, lqz, lox, loy, loz⟩ := hlt
  have tc : ∀ {s s' : State} {x y : Nat}, wordsVal s.mem base x J.L.M.n = wordsVal s'.mem base y J.L.M.n →
      tmv C J.L.M.n base s x = tmv C J.L.M.n base s' y := fun e => by
    show toM _ _ _ = toM _ _ _; rw [e]
  have by4 : ∀ {d : Nat}, 4096 ≤ d → d < 8192 → t.mem (off base d) = s.mem (off base d) := fun h1 h2 =>
    ht.unch.byte (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; subst hw; right; simp only; omega_arith)
      (by omega_arith)
  have hbV := hJ.bitsV
  have hbL := hL.bits
  have hbE := hL.bitsE
  refine ⟨⟨by rw [tc ht.ab.1]; exact hab.1, by rw [tc ht.ab.2]; exact hab.2⟩, ?_,
    by rw [tc kgx, tc kgy, tc kgz]; exact hg, by rw [tc kqx, tc kqy, tc kqz]; exact hq,
    by rw [tc kox, tc koy, tc koz]; exact ho, fun i hi => by rw [by4 (by omega) (by omega)]; exact hbu i hi,
    fun i hi => by rw [by4 (by omega) (by omega)]; exact hbv i hi⟩
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ht.ab.1]; exact la
  · rw [ht.ab.2]; exact lb
  · rw [kgx]; exact lgx
  · rw [kgy]; exact lgy
  · rw [kgz]; exact lgz
  · rw [kqx]; exact lqx
  · rw [kqy]; exact lqy
  · rw [kqz]; exact lqz
  · exact ht.lt.1
  · exact ht.lt.2.1
  · exact ht.lt.2.2
  · rw [kox]; exact lox
  · rw [koy]; exact loy
  · rw [koz]; exact loz

/-- `[u]G + [v]Q` into `R`, for `u` and `v` of at most `nbits` bits whose
tables of bits are at `bits` and `bitsV`, `G` and `Q` on the curve, and `O`
representing the point at infinity; only `powClob` and `jointW` change. -/
theorem joint_ok {G Q : Point C} {u v : Nat} {S : Impl.Weierstrass.Mont.Modulus}
    (hkS : S.k = J.L.M.n) (hmS : S.m = C.p) (hM : ModOk J.L.M.n C.p) (hodd : C.p % 2 = 1)
    (hC : Law C) (hG : onCurve C G = true) (hQ : onCurve C Q = true) (hJ : JLay J) {s : State}
    (hw : WsReg s base)
    (hlt : ∀ x ∈ [J.L.S.a, J.L.S.b3, J.L.G.x, J.L.G.y, J.L.G.z, J.Q.x, J.Q.y, J.Q.z, J.O.x, J.O.y, J.O.z],
      wordsVal s.mem base x J.L.M.n < C.p)
    (hab : tmv C J.L.M.n base s J.L.S.a = Fin.ofNat C.p C.a ∧
      tmv C J.L.M.n base s J.L.S.b3 = Fin.ofNat C.p (3 * C.b))
    (hg : Rep C (tmv C J.L.M.n base s J.L.G.x) (tmv C J.L.M.n base s J.L.G.y) (tmv C J.L.M.n base s J.L.G.z) G)
    (hq : Rep C (tmv C J.L.M.n base s J.Q.x) (tmv C J.L.M.n base s J.Q.y) (tmv C J.L.M.n base s J.Q.z) Q)
    (ho : Rep C (tmv C J.L.M.n base s J.O.x) (tmv C J.L.M.n base s J.O.y) (tmv C J.L.M.n base s J.O.z)
      .infinity)
    (hbu : ∀ i < J.L.nbits, s.mem (off base (J.L.bits + i)) = if u.testBit i then 1 else 0)
    (hbv : ∀ i < J.L.nbits, s.mem (off base (J.bitsV + i)) = if v.testBit i then 1 else 0)
    (hu : u < 2 ^ J.L.nbits) (hv : v < 2 ^ J.L.nbits)
    (hone : J.one < C.p ∧ toM C.p (2 ^ (64 * J.L.M.n)) J.one = 1) :
    WP isa (J.joint S) s fun s' => Rk powClob s s' ∧ Unch base (jointW J) s.mem s'.mem ∧
      (∀ x ∈ [J.L.R.x, J.L.R.y, J.L.R.z], wordsVal s'.mem base x J.L.M.n < C.p) ∧
      Rep C (tmv C J.L.M.n base s' J.L.R.x) (tmv C J.L.M.n base s' J.L.R.y) (tmv C J.L.M.n base s' J.L.R.z)
        (add (mul u G) (mul v Q)) := by
  rw [JointCfg.joint]
  refine setup_ok hkS hmS hM hodd hC hG hQ hJ hw (fun x hx => hlt x (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with h | h | h | h | h | h | h | h <;> simp [h])) hab hg hq fun t ht => ?_
  obtain ⟨ab, lt, g, q, o, bu, bv⟩ := setPost_start (u := u) (v := v) hJ hw ht hlt hab hg hq ho hbu hbv
  refine WP.seq (WP.mono (start_ok hC hJ ht.ws ab lt g q ht.rep o bu bv hM.m0 hone
    (Nat.lt_trans hone.1 hM.m_lt)) fun s₀ sp => ?_)
  refine WP.mono (loop_ok hkS hmS hM hodd hC hG hQ hJ sp.fix sp.ws sp.r31 hu hv sp.lt sp.rep)
    fun s' ⟨k', U', l', r'⟩ => ⟨ht.keep.trans (sp.keep.trans k'), ((ht.unch.trans sp.unch).trans U').mono
      jointW_cover, l', r'⟩

end body

end VG.Proof.Weierstrass.PPC64LE.Joint
