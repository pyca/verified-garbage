import VerifiedGarbage.Proof.Weierstrass.Arm.LadderPCall
import VerifiedGarbage.Proof.Weierstrass.Arm.Ladder

/-!
# The ladder by calls of the point functions, on 32-bit ARM

`ladderP L S` (`Impl/Weierstrass/Arm/LadderP.lean`) meets what `ladder_ok`
states of `ladder L S` (`ladderP_ok`), but that it also writes the point
functions' slots and own working space (`ptW`, empty for P-521, whose
ladder is `ladder`): for coordinates of at most 6 words, an iteration
(`ladderPBody_ok`) copies `R` to `P`, so that the doubling's call leaves
`D = R + R` in `O` (`ptCall_ok`), copies it to `P`, so that the addition's
leaves `T = D + G` in `O`, `G` having been copied to `Q` (and `a` and `3b` to
theirs) before the loop, and selects `R = T` or `D`; the ladder's slots lie
below the point functions' (`LadPt`).
-/

namespace VG.Proof.Weierstrass.Arm.Point

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass.Arm.Mont
open VG.Impl.Weierstrass VG.Impl.Weierstrass.Arm.Point
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass.Arm.Mont
open VG.Proof.X25519.Arm (Rest Upd wp_mov op2_imm)

/-- The point functions' slots and own working space, which the ladder
writes if it calls them. -/
def ptW (n : Nat) : List (Nat × Nat) :=
  if n ≤ 6 then [(Spec.Weierstrass.Point.oAt n, 4096 - Spec.Weierstrass.Point.oAt n)] else []

/-- What `ladderP` writes. -/
def ladWp (L : LadderCfg) (wk : Nat) : List (Nat × Nat) := ladWx L wk ++ ptW L.M.n

/-- The ladder's slots and modulus lie below the point functions' slots. -/
structure LadPt (L : LadderCfg) : Prop where
  sl : ∀ x ∈ ladSlots L, x + 8 * L.M.n ≤ Spec.Weierstrass.Point.oAt L.M.n
  mo : L.M.mo + 8 * L.M.n ≤ Spec.Weierstrass.Point.oAt L.M.n

theorem ModOk.odd {n m : Nat} (h : Mont.ModOk n m) : m % 2 = 1 := by
  have h2 : (m * minv m + 1) % 2 = 0 := by
    rw [← Nat.mod_mod_of_dvd _ (show 2 ∣ 2 ^ 64 by decide), h.inv]
  rcases Nat.mod_two_eq_zero_or_one m with h0 | h1
  · simp [Nat.add_mod, Nat.mul_mod, h0] at h2
  · exact h1

section enc
variable (k : Nat) (dbl : Bool)

theorem enc_0 : enc k dbl 0 = Spec.Weierstrass.Point.oAt k := by simp [enc]
theorem enc_1 : enc k dbl 1 = Spec.Weierstrass.Point.oAt k + Spec.Weierstrass.Point.elemBytes k := by simp [enc]
theorem enc_2 : enc k dbl 2 = Spec.Weierstrass.Point.oAt k + 2 * Spec.Weierstrass.Point.elemBytes k := by simp [enc]; omega_arith
theorem enc_3 : enc k dbl 3 = Spec.Weierstrass.Point.pAt k := by simp [enc]
theorem enc_4 : enc k dbl 4 = Spec.Weierstrass.Point.pAt k + Spec.Weierstrass.Point.elemBytes k := by simp [enc]
theorem enc_5 : enc k dbl 5 = Spec.Weierstrass.Point.pAt k + 2 * Spec.Weierstrass.Point.elemBytes k := by simp [enc]; omega_arith
theorem enc_6 : enc k dbl 6 = if dbl then Spec.Weierstrass.Point.pAt k else Spec.Weierstrass.Point.qAt k := by simp [enc]
theorem enc_7 : enc k dbl 7 = (if dbl then Spec.Weierstrass.Point.pAt k else Spec.Weierstrass.Point.qAt k) + Spec.Weierstrass.Point.elemBytes k := by
  simp [enc]
theorem enc_8 : enc k dbl 8 = (if dbl then Spec.Weierstrass.Point.pAt k else Spec.Weierstrass.Point.qAt k) + 2 * Spec.Weierstrass.Point.elemBytes k := by
  simp [enc]; omega_arith
theorem enc_9 : enc k dbl 9 = Spec.Weierstrass.Point.aAt k := by simp [enc]
theorem enc_10 : enc k dbl 10 = Spec.Weierstrass.Point.b3At k := by simp [enc]

end enc

/-- The bounds a call needs, by offset. -/
theorem rIds_lt_of {k m : Nat} (dbl : Bool) {mem : Mem} {base : Addr}
    (h : ∀ x ∈ [Spec.Weierstrass.Point.pAt k, Spec.Weierstrass.Point.pAt k + Spec.Weierstrass.Point.elemBytes k, Spec.Weierstrass.Point.pAt k + 2 * Spec.Weierstrass.Point.elemBytes k,
      (if dbl then Spec.Weierstrass.Point.pAt k else Spec.Weierstrass.Point.qAt k), (if dbl then Spec.Weierstrass.Point.pAt k else Spec.Weierstrass.Point.qAt k) + Spec.Weierstrass.Point.elemBytes k,
      (if dbl then Spec.Weierstrass.Point.pAt k else Spec.Weierstrass.Point.qAt k) + 2 * Spec.Weierstrass.Point.elemBytes k, Spec.Weierstrass.Point.aAt k, Spec.Weierstrass.Point.b3At k],
      wordsVal mem base x k < m) :
    ∀ x ∈ rIds, wordsVal mem base (enc k dbl x) k < m := by
  intro x hx
  simp only [rIds, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [enc_3, enc_4, enc_5, enc_6, enc_7, enc_8, enc_9, enc_10] <;> exact h _ (by simp)

/-- The point functions' `Q`, `a` and `3b` in `m` hold `G`, `a` and `3b` of
`m₀`. -/
def CpOk (L : LadderCfg) (base : Addr) (m m₀ : Mem) : Prop :=
  wordsVal m base (Spec.Weierstrass.Point.qAt L.M.n) L.M.n = wordsVal m₀ base L.G.x L.M.n ∧
  wordsVal m base (Spec.Weierstrass.Point.qAt L.M.n + Spec.Weierstrass.Point.elemBytes L.M.n) L.M.n =
    wordsVal m₀ base L.G.y L.M.n ∧
  wordsVal m base (Spec.Weierstrass.Point.qAt L.M.n + 2 * Spec.Weierstrass.Point.elemBytes L.M.n) L.M.n =
    wordsVal m₀ base L.G.z L.M.n ∧
  wordsVal m base (Spec.Weierstrass.Point.aAt L.M.n) L.M.n = wordsVal m₀ base L.S.a L.M.n ∧
  wordsVal m base (Spec.Weierstrass.Point.b3At L.M.n) L.M.n = wordsVal m₀ base L.S.b3 L.M.n

/-- The copies survive changes apart from them. -/
theorem CpOk.keep {L : LadderCfg} {base : Addr} {m m' m₀ : Mem} (h : CpOk L base m m₀)
    (hk3 : 3 ≤ L.M.n) (hk6 : L.M.n ≤ 6) {W : List (Nat × Nat)} (hU : Unch base W m m')
    (hW : ∀ w ∈ W, w.1 + w.2 ≤ Spec.Weierstrass.Point.qAt L.M.n ∨ Spec.Weierstrass.Point.ownAt L.M.n ≤ w.1) :
    CpOk L base m' m₀ := by
  have hl := lay_nums hk3 hk6
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hU.wordsVal (fun w hw => by have := hW w hw; omega_arith) (by omega_arith)]; exact h1
  · rw [hU.wordsVal (fun w hw => by have := hW w hw; omega_arith) (by omega_arith)]; exact h2
  · rw [hU.wordsVal (fun w hw => by have := hW w hw; omega_arith) (by omega_arith)]; exact h3
  · rw [hU.wordsVal (fun w hw => by have := hW w hw; omega_arith) (by omega_arith)]; exact h4
  · rw [hU.wordsVal (fun w hw => by have := hW w hw; omega_arith) (by omega_arith)]; exact h5

/-- The loop's invariant at `r11 = j`: `Q j` accepts what `R` holds, and the
point functions' `Q`, `a` and `3b` hold `G`, `a` and `3b`. -/
structure LadInvP (L : LadderCfg) (wk : Nat) (C : Spec.Weierstrass.Curve) (base : Addr) (size : Nat)
    (Q : Nat → Spec.Weierstrass.Fe C → Spec.Weierstrass.Fe C → Spec.Weierstrass.Fe C → Prop) (s₀ s : State) (j : Nat) : Prop where
  scr : Scr s base size
  r11 : s.gpr .r11 = BitVec.ofNat 32 j
  keep : Rest powClob s₀ s
  unch : Unch base (ladWx L wk ++ [(Spec.Weierstrass.Point.oAt L.M.n, 4096 - Spec.Weierstrass.Point.oAt L.M.n)]) s₀.mem s.mem
  mod : ModOkW L.M size C.p s.mem base
  lt : ∀ x ∈ [L.R.x, L.R.y, L.R.z], wordsVal s.mem base x L.M.n < C.p
  q : Q j (tmv C L.M.n base s L.R.x) (tmv C L.M.n base s L.R.y) (tmv C L.M.n base s L.R.z)
  cp : CpOk L base s.mem s₀.mem

/-- Apart from each of a few ranges, for numbers of the layout. -/
macro "apart_ranges" : tactic => `(tactic| (simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq_or_imp, forall_eq, List.mem_singleton]; omega_arith))

/-- Within the point functions' slots and own working space. -/
macro "in_pt" : tactic => `(tactic| (simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq_or_imp, forall_eq, List.mem_singleton, exists_eq_left]; omega_arith))

section body
variable {L : LadderCfg} {wk : Nat} {C : Spec.Weierstrass.Curve} {base : Addr} {size : Nat}

/-- An iteration. -/
theorem ladderPBody_ok {k : Nat} {Q : Nat → Spec.Weierstrass.Fe C → Spec.Weierstrass.Fe C → Spec.Weierstrass.Fe C → Prop}
    (hL : LadLay L size 8192) (hW : LadWk L size wk) {S : Spec.Weierstrass.Mont.Modulus}
    (hF : FnOk L.M wk S C.p) (hk6 : L.M.n ≤ 6) (hP : LadPt L) (hb8 : L.bits < 8192)
    {s₀ : State} (hf₀ : Far s₀ base 8192) (hlt₀ : ∀ x ∈ ladRo L, wordsVal s₀.mem base x L.M.n < C.p)
    (hstep : Step L C base s₀ k Q)
    (hbits : ∀ t < L.nbits, s₀.mem (off base (L.bits + t)) = if k.testBit t then 1 else 0)
    {j : Nat} {s : State} (hj : 1 ≤ j) (hjn : j ≤ L.nbits) (hI : LadInvP L wk C base size Q s₀ s j) :
    WP isa (ladderPBody L S) s fun s' =>
      LadInvP L wk C base size Q s₀ s' (j - 1) ∧ s'.z = decide (j - 1 = 0) := by
  have hM : Mont.ModOk L.M.n C.p := by have h := hF.ok; rw [hF.k, hF.m] at h; exact h
  have hodd := ModOk.odd hM
  have hk3 := hM.n3
  have hl := lay_nums hk3 hk6
  have hwk := hF.wk
  have hown := own_le L.M.n hM.n9
  have hsz : size = 4096 := by have := hW.le; have := hI.scr.small; omega_arith
  have hbl : 4096 ≤ L.bits := by have := hW.bits; omega_arith
  have hnb := hL.nbits
  have hlb := hL.bits
  have rx : L.R.x + 8 * L.M.n ≤ Spec.Weierstrass.Point.oAt L.M.n := hP.sl _ (ladPts_slots L _ (by simp))
  have ry : L.R.y + 8 * L.M.n ≤ Spec.Weierstrass.Point.oAt L.M.n := hP.sl _ (ladPts_slots L _ (by simp))
  have rz : L.R.z + 8 * L.M.n ≤ Spec.Weierstrass.Point.oAt L.M.n := hP.sl _ (ladPts_slots L _ (by simp))
  -- `r11 -= 1`.
  rw [ladderPBody]
  refine WP.seq (wp_decCounter hj hI.r11 fun s₁ u₁ => WP.block_nil ?_)
  have hm₁ : s₁.mem = s.mem := u₁.mem
  have k₁ : Rest [.r11] s s₁ := u₁.rest (by simp)
  have hs₁ := hI.scr.of_rest k₁ (by decide)
  -- `P = R`.
  refine WP.seq (WP.mono (copyPt_ok hs₁ (n := L.M.n) (o := ptAt L.M.n (Spec.Weierstrass.Point.pAt L.M.n))
    (a := L.R) (by simp only [ptAt, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_arith)
    (by simp only [ptAt]; omega_arith)
    (by simp only [ptAt, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_arith))
    fun s₂ ⟨px₂, py₂, pz₂, k₂, O₂⟩ => ?_)
  simp only [ptAt] at px₂ py₂ pz₂ O₂
  rw [hm₁] at px₂ py₂ pz₂ O₂
  have hs₂ := hs₁.of_rest k₂ (by decide)
  have hf₂ : Far s₂ base 8192 := ((hf₀.of_rest hI.keep).of_rest k₁).of_rest k₂
  have cp₂ : CpOk L base s₂.mem s₀.mem := hI.cp.keep hk3 hk6 (Outs.unch O₂) (by apart_ranges)
  obtain ⟨gx₂, gy₂, gz₂, ga₂, gb₂⟩ := cp₂
  have la : wordsVal s₀.mem base L.S.a L.M.n < C.p := hlt₀ _ (by simp [ladRo])
  have lb : wordsVal s₀.mem base L.S.b3 L.M.n < C.p := hlt₀ _ (by simp [ladRo])
  have lgx : wordsVal s₀.mem base L.G.x L.M.n < C.p := hlt₀ _ (by simp [ladRo])
  have lgy : wordsVal s₀.mem base L.G.y L.M.n < C.p := hlt₀ _ (by simp [ladRo])
  have lgz : wordsVal s₀.mem base L.G.z L.M.n < C.p := hlt₀ _ (by simp [ladRo])
  have lrx : wordsVal s.mem base L.R.x L.M.n < C.p := hI.lt _ (by simp)
  have lry : wordsVal s.mem base L.R.y L.M.n < C.p := hI.lt _ (by simp)
  have lrz : wordsVal s.mem base L.R.z L.M.n < C.p := hI.lt _ (by simp)
  -- `O = P + P`.
  refine WP.seq (WP.mono (ptCall_ok hF.m hF.k hM hodd hk6 true hs₂ hf₂ (rIds_lt_of true fun x hx => by
      simp only [↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [px₂]; exact lrx
      · rw [py₂]; exact lry
      · rw [pz₂]; exact lrz
      · rw [px₂]; exact lrx
      · rw [py₂]; exact lry
      · rw [pz₂]; exact lrz
      · rw [ga₂]; exact la
      · rw [gb₂]; exact lb)) fun s₃ ⟨k₃, O₃, L₃, E₃⟩ => ?_)
  simp only [Eb, enc_0, enc_1, enc_2, enc_3, enc_4, enc_5, enc_6, enc_7, enc_8, enc_9, enc_10, ↓reduceIte] at E₃
  rw [ga₂, gb₂, px₂, py₂, pz₂] at E₃
  have l3x := L₃ 0 (by decide)
  have l3y := L₃ 1 (by decide)
  have l3z := L₃ 2 (by decide)
  rw [enc_0] at l3x
  rw [enc_1] at l3y
  rw [enc_2] at l3z
  have hs₃ := hs₂.of_rest k₃ (by decide)
  have hf₃ : Far s₃ base 8192 := hf₂.of_rest k₃
  -- `P = O`.
  refine WP.seq (WP.mono (copyPt_ok hs₃ (n := L.M.n) (o := ptAt L.M.n (Spec.Weierstrass.Point.pAt L.M.n))
    (a := ptAt L.M.n (Spec.Weierstrass.Point.oAt L.M.n))
    (by simp only [ptAt, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_arith)
    (by simp only [ptAt]; omega_arith)
    (by simp only [ptAt, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_arith))
    fun s₄ ⟨px₄, py₄, pz₄, k₄, O₄⟩ => ?_)
  simp only [ptAt] at px₄ py₄ pz₄ O₄
  have hs₄ := hs₃.of_rest k₄ (by decide)
  have hf₄ : Far s₄ base 8192 := hf₃.of_rest k₄
  have cp₄ : CpOk L base s₄.mem s₀.mem :=
    (CpOk.keep ⟨gx₂, gy₂, gz₂, ga₂, gb₂⟩ hk3 hk6 (Outs.unch O₃) (by apart_ranges)).keep hk3 hk6 (Outs.unch O₄)
      (by apart_ranges)
  obtain ⟨gx₄, gy₄, gz₄, ga₄, gb₄⟩ := cp₄
  -- `O = P + Q`.
  refine WP.seq (WP.mono (ptCall_ok hF.m hF.k hM hodd hk6 false hs₄ hf₄ (rIds_lt_of false fun x hx => by
      simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [px₄]; exact l3x
      · rw [py₄]; exact l3y
      · rw [pz₄]; exact l3z
      · rw [gx₄]; exact lgx
      · rw [gy₄]; exact lgy
      · rw [gz₄]; exact lgz
      · rw [ga₄]; exact la
      · rw [gb₄]; exact lb)) fun s₅ ⟨k₅, O₅, L₅, E₅⟩ => ?_)
  simp only [Eb, enc_0, enc_1, enc_2, enc_3, enc_4, enc_5, enc_6, enc_7, enc_8, enc_9, enc_10,
    Bool.false_eq_true, ↓reduceIte] at E₅
  rw [ga₄, gb₄, px₄, py₄, pz₄, gx₄, gy₄, gz₄] at E₅
  have l5x := L₅ 0 (by decide)
  have l5y := L₅ 1 (by decide)
  have l5z := L₅ 2 (by decide)
  rw [enc_0] at l5x
  rw [enc_1] at l5y
  rw [enc_2] at l5z
  -- `P` still holds `D`.
  have p5x : wordsVal s₅.mem base (Spec.Weierstrass.Point.pAt L.M.n) L.M.n =
      wordsVal s₃.mem base (Spec.Weierstrass.Point.oAt L.M.n) L.M.n := by
    rw [(Outs.unch O₅).wordsVal (by apart_ranges) (by omega_arith), px₄]
  have p5y : wordsVal s₅.mem base (Spec.Weierstrass.Point.pAt L.M.n + Spec.Weierstrass.Point.elemBytes L.M.n) L.M.n =
      wordsVal s₃.mem base (Spec.Weierstrass.Point.oAt L.M.n + Spec.Weierstrass.Point.elemBytes L.M.n) L.M.n := by
    rw [(Outs.unch O₅).wordsVal (by apart_ranges) (by omega_arith), py₄]
  have p5z : wordsVal s₅.mem base (Spec.Weierstrass.Point.pAt L.M.n + 2 * Spec.Weierstrass.Point.elemBytes L.M.n) L.M.n =
      wordsVal s₃.mem base (Spec.Weierstrass.Point.oAt L.M.n + 2 * Spec.Weierstrass.Point.elemBytes L.M.n) L.M.n := by
    rw [(Outs.unch O₅).wordsVal (by apart_ranges) (by omega_arith), pz₄]
  have cp₅ : CpOk L base s₅.mem s₀.mem := CpOk.keep ⟨gx₄, gy₄, gz₄, ga₄, gb₄⟩ hk3 hk6 (Outs.unch O₅) (by apart_ranges)
  -- What changed: the point functions' slots.
  have U₁₅ : Unch base [(Spec.Weierstrass.Point.oAt L.M.n, 4096 - Spec.Weierstrass.Point.oAt L.M.n)] s.mem s₅.mem :=
    (((Outs.unch O₂).trans (Outs.unch O₃)).trans ((Outs.unch O₄).trans (Outs.unch O₅))).cover (by in_pt)
  have hU₅ : Unch base (ladWx L wk ++ [(Spec.Weierstrass.Point.oAt L.M.n, 4096 - Spec.Weierstrass.Point.oAt L.M.n)])
      s₀.mem s₅.mem :=
    (hI.unch.trans U₁₅).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hw
      · exact List.mem_append_right _ hw
  have hbyte : s₅.mem (off base (L.bits + (j - 1))) = if k.testBit (j - 1) then 1 else 0 := by
    rw [hU₅.byte (fun w hw => by
      simp only [ladWx, List.mem_append, List.mem_singleton] at hw
      rcases hw with (hw | rfl) | rfl
      · have := hL.bits_w w hw; omega_arith
      · dsimp only; omega_arith
      · dsimp only; omega_arith) (by omega_arith), hbits _ (by omega_arith)]
  have K₅ : Rest powClob s s₅ :=
    (k₁.mono (by simp [powClob])).trans <| (k₂.mono (by simp [powClob, clob])).trans <|
      (k₃.mono (by simp [powClob, clob])).trans <| (k₄.mono (by simp [powClob, clob])).trans
        (k₅.mono (by simp [powClob, clob]))
  have r11₅ : s₅.gpr .r11 = BitVec.ofNat 32 (j - 1) := by
    rw [k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), u₁.gpr]
  have hs₅ := hs₄.of_rest k₅ (by decide)
  -- `R = O` or `P`.
  rw [List.append_assoc]
  refine VG.Proof.X25519.Arm.WP.append (bitMask_bool_ok hs₅ ((hf₀.of_rest hI.keep).of_rest K₅) r11₅ (by omega_arith)
    hb8 hbyte) fun s₆ ⟨c₆, k₆, hm₆⟩ => ?_
  have hs₆ := hs₅.of_rest k₆ (by decide)
  obtain ⟨rxy, rxz, ryz⟩ := hL.rne
  have hap : ∀ x ∈ [L.R.x, L.R.y, L.R.z], ∀ y ∈ [L.R.x, L.R.y, L.R.z], x ≠ y →
      x + 8 * L.M.n ≤ y ∨ y + 8 * L.M.n ≤ x := fun x hx y hy hxy =>
    hL.lay.apart x y (ladPts_slots L x (by simp only [List.mem_cons] at hx ⊢; rcases hx with h | h | h | h <;> simp [h]))
      (ladPts_slots L y (by simp only [List.mem_cons] at hy ⊢; rcases hy with h | h | h | h <;> simp [h])) hxy
  refine VG.Proof.X25519.Arm.WP.append (selPt_ok hs₆ _ c₆ (n := L.M.n) (o := L.R)
    (a := ptAt L.M.n (Spec.Weierstrass.Point.pAt L.M.n)) (b := ptAt L.M.n (Spec.Weierstrass.Point.oAt L.M.n))
    (by simp only [ptAt, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_arith)
    ⟨hap L.R.x (by simp) L.R.y (by simp) rxy, hap L.R.x (by simp) L.R.z (by simp) rxz,
      hap L.R.y (by simp) L.R.z (by simp) ryz⟩
    (by simp only [ptAt, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_arith))
    fun s₇ ⟨ex, ey, ez, k₇, O₇⟩ => ?_
  simp only [ptAt] at ex ey ez
  rw [hm₆] at ex ey ez
  have r11₇ : s₇.gpr .r11 = BitVec.ofNat 32 (j - 1) := by rw [k₇.gpr _ (by decide), k₆.gpr _ (by decide), r11₅]
  have U₅₇ : Unch base [(L.R.x, 8 * L.M.n), (L.R.y, 8 * L.M.n), (L.R.z, 8 * L.M.n)] s₅.mem s₇.mem := by
    rw [← hm₆]; exact Outs.unch O₇
  refine wp_testCounter (by omega_arith) r11₇ fun s₈ f₈ z₈ => WP.block_nil ⟨⟨?_, by rw [f₈.gpr, r11₇], ?_, ?_, ?_, ?_, ?_, ?_⟩, z₈⟩
  · exact (hs₆.of_rest k₇ (by decide)).of_rest (f₈.rest []) (by decide)
  · exact (hI.keep.trans K₅).trans ((k₆.mono (by simp [powClob, clob])).trans
      ((k₇.mono (by simp [powClob, clob])).trans (f₈.rest _)))
  · rw [f₈.mem]
    exact (hU₅.trans U₅₇).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hw
      · exact List.mem_append_left _ (List.mem_append_left _ (mem_ladW_R w hw))
  · rw [f₈.mem]
    have hmo := hL.lay.mo
    have mx := hmo L.R.x (ladPts_slots L _ (by simp))
    have my := hmo L.R.y (ladPts_slots L _ (by simp))
    have mz := hmo L.R.z (ladPts_slots L _ (by simp))
    have hpm := hP.mo
    exact hI.mod.unch (U₁₅.trans U₅₇) (by apart_ranges) (by have := hI.scr.nowrap; omega_arith)
  · rw [f₈.mem]
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [ex]; split
      · exact l5x
      · rw [p5x]; exact l3x
    · rw [ey]; split
      · exact l5y
      · rw [p5y]; exact l3y
    · rw [ez]; split
      · exact l5z
      · rw [p5z]; exact l3z
  · have hq := hstep (j - 1) (by omega_arith) _ _ _ _ _ _ _ _ _ (by rw [Nat.sub_add_cancel hj]; exact hI.q) E₃.symm E₅.symm
    have hx : tmv C L.M.n base s₈ L.R.x = if k.testBit (j - 1) then
        toM C.p (2 ^ (64 * L.M.n)) (wordsVal s₅.mem base (Spec.Weierstrass.Point.oAt L.M.n) L.M.n) else
        toM C.p (2 ^ (64 * L.M.n)) (wordsVal s₃.mem base (Spec.Weierstrass.Point.oAt L.M.n) L.M.n) := by
      show toM _ _ _ = _
      rw [f₈.mem, ex]; split
      · rfl
      · rw [p5x]
    have hy : tmv C L.M.n base s₈ L.R.y = if k.testBit (j - 1) then
        toM C.p (2 ^ (64 * L.M.n)) (wordsVal s₅.mem base
          (Spec.Weierstrass.Point.oAt L.M.n + Spec.Weierstrass.Point.elemBytes L.M.n) L.M.n) else
        toM C.p (2 ^ (64 * L.M.n)) (wordsVal s₃.mem base
          (Spec.Weierstrass.Point.oAt L.M.n + Spec.Weierstrass.Point.elemBytes L.M.n) L.M.n) := by
      show toM _ _ _ = _
      rw [f₈.mem, ey]; split
      · rfl
      · rw [p5y]
    have hz : tmv C L.M.n base s₈ L.R.z = if k.testBit (j - 1) then
        toM C.p (2 ^ (64 * L.M.n)) (wordsVal s₅.mem base
          (Spec.Weierstrass.Point.oAt L.M.n + 2 * Spec.Weierstrass.Point.elemBytes L.M.n) L.M.n) else
        toM C.p (2 ^ (64 * L.M.n)) (wordsVal s₃.mem base
          (Spec.Weierstrass.Point.oAt L.M.n + 2 * Spec.Weierstrass.Point.elemBytes L.M.n) L.M.n) := by
      show toM _ _ _ = _
      rw [f₈.mem, ez]; split
      · rfl
      · rw [p5z]
    rw [hx, hy, hz]
    exact hq
  · rw [f₈.mem]
    exact cp₅.keep hk3 hk6 U₅₇ (by apart_ranges)

/-- `Q 0` accepts what `R` holds at the end, if `Q L.nbits` accepts what it
holds at the start and an iteration keeps `Q` (`Step`), for the scalar `k`
whose bits are the table at `L.bits`; only `powClob` and `ladWp` change. As
`ladder_ok`, for the slots below the point functions' (`LadPt`) if it calls
them. -/
theorem ladderP_ok {k : Nat} {Q : Nat → Spec.Weierstrass.Fe C → Spec.Weierstrass.Fe C → Spec.Weierstrass.Fe C → Prop}
    (hL : LadLay L size 8192) (hW : LadWk L size wk) {S : Spec.Weierstrass.Mont.Modulus}
    (hF : FnOk L.M wk S C.p) (hP : L.M.n ≤ 6 → LadPt L) (hp : UnitMod C.p (2 ^ (64 * L.M.n)))
    (hb8 : L.bits < 8192) {s : State} (hs : Scr s base size) (hf : Far s base 8192)
    (hM : ModOkW L.M size C.p s.mem base) (hlt : ∀ x ∈ ladR L, wordsVal s.mem base x L.M.n < C.p)
    (hstep : Step L C base s k Q)
    (hR : Q L.nbits (tmv C L.M.n base s L.R.x) (tmv C L.M.n base s L.R.y) (tmv C L.M.n base s L.R.z))
    (hbits : ∀ t < L.nbits, s.mem (off base (L.bits + t)) = if k.testBit t then 1 else 0)
    (henc : encodable (BitVec.ofNat 32 L.nbits) = true) :
    WP isa (ladderP L S) s fun s' => Rest powClob s s' ∧ Unch base (ladWp L wk) s.mem s'.mem ∧
      ModOkW L.M size C.p s'.mem base ∧
      (∀ x ∈ [L.R.x, L.R.y, L.R.z], wordsVal s'.mem base x L.M.n < C.p) ∧
      Q 0 (tmv C L.M.n base s' L.R.x) (tmv C L.M.n base s' L.R.y) (tmv C L.M.n base s' L.R.z) := by
  unfold ladderP ladWp ptW
  by_cases hk6 : L.M.n ≤ 6
  swap
  · simp only [hk6, ↓reduceIte, List.append_nil]
    exact ladder_ok hL hW hF hp hb8 hs hf hM hlt hstep hR hbits henc
  simp only [hk6, ↓reduceIte]
  have hPt := hP hk6
  have hM' : Mont.ModOk L.M.n C.p := by have h := hF.ok; rw [hF.k, hF.m] at h; exact h
  have hk3 := hM'.n3
  have hl := lay_nums hk3 hk6
  have hwk := hF.wk
  have hown := own_le L.M.n hM'.n9
  have hsz : size = 4096 := by have := hW.le; have := hs.small; omega_arith
  have hn := hs.nowrap
  have rx : L.R.x + 8 * L.M.n ≤ Spec.Weierstrass.Point.oAt L.M.n := hPt.sl _ (ladPts_slots L _ (by simp))
  have ry : L.R.y + 8 * L.M.n ≤ Spec.Weierstrass.Point.oAt L.M.n := hPt.sl _ (ladPts_slots L _ (by simp))
  have rz : L.R.z + 8 * L.M.n ≤ Spec.Weierstrass.Point.oAt L.M.n := hPt.sl _ (ladPts_slots L _ (by simp))
  have gx : L.G.x + 8 * L.M.n ≤ Spec.Weierstrass.Point.oAt L.M.n := hPt.sl _ (ladR_slots L _ (by simp [ladR, ladRo]))
  have gy : L.G.y + 8 * L.M.n ≤ Spec.Weierstrass.Point.oAt L.M.n := hPt.sl _ (ladR_slots L _ (by simp [ladR, ladRo]))
  have gz : L.G.z + 8 * L.M.n ≤ Spec.Weierstrass.Point.oAt L.M.n := hPt.sl _ (ladR_slots L _ (by simp [ladR, ladRo]))
  have ga : L.S.a + 8 * L.M.n ≤ Spec.Weierstrass.Point.oAt L.M.n := hPt.sl _ (ladR_slots L _ (by simp [ladR, ladRo]))
  have gb : L.S.b3 + 8 * L.M.n ≤ Spec.Weierstrass.Point.oAt L.M.n := hPt.sl _ (ladR_slots L _ (by simp [ladR, ladRo]))
  refine WP.seq ?_
  rw [ladderSetup, List.append_assoc, List.append_assoc, WP.block_append_iff]
  -- `Q = G`, `a`, `3b`.
  refine WP.mono (copyPt_ok hs (n := L.M.n) (o := ptAt L.M.n (Spec.Weierstrass.Point.qAt L.M.n)) (a := L.G)
    (by simp only [ptAt, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_arith)
    (by simp only [ptAt]; omega_arith)
    (by simp only [ptAt, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_arith))
    fun s₁ ⟨gx₁, gy₁, gz₁, k₁, O₁⟩ => ?_
  simp only [ptAt] at gx₁ gy₁ gz₁ O₁
  have hs₁ := hs.of_rest k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok (2 * L.M.n) hs₁ (o := Spec.Weierstrass.Point.aAt L.M.n) (a := L.S.a) (by omega_arith) (by omega_arith)
    (by omega_arith)) fun s₂ ⟨a₂, k₂, O₂⟩ => ?_
  rw [← wordsVal_eq_val32, ← wordsVal_eq_val32] at a₂
  have hs₂ := hs₁.of_rest k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok (2 * L.M.n) hs₂ (o := Spec.Weierstrass.Point.b3At L.M.n) (a := L.S.b3) (by omega_arith) (by omega_arith)
    (by omega_arith)) fun s₃ ⟨b₃, k₃, O₃⟩ => ?_
  rw [← wordsVal_eq_val32, ← wordsVal_eq_val32] at b₃
  have hs₃ := hs₂.of_rest k₃ (by decide)
  refine wp_mov (op2_imm henc) fun s₄ u₄ => WP.block_nil ?_
  have hm₄ : s₄.mem = s₃.mem := u₄.mem
  have U₂ : Unch base [(Spec.Weierstrass.Point.aAt L.M.n, 4 * (2 * L.M.n))] s₁.mem s₂.mem := O₂.unch
  have U₃ : Unch base [(Spec.Weierstrass.Point.b3At L.M.n, 4 * (2 * L.M.n))] s₂.mem s₃.mem := O₃.unch
  have U₁₃ : Unch base [(Spec.Weierstrass.Point.oAt L.M.n, 4096 - Spec.Weierstrass.Point.oAt L.M.n)] s.mem s₄.mem := by
    rw [hm₄]; exact ((Outs.unch O₁).trans (U₂.trans U₃)).cover (by in_pt)
  have K₄ : Rest powClob s s₄ := (k₁.mono (by simp [powClob, clob])).trans <| (k₂.mono (by simp [powClob, clob])).trans <|
    (k₃.mono (by simp [powClob, clob])).trans (u₄.rest (by simp [powClob]))
  have low : ∀ {x}, x + 8 * L.M.n ≤ Spec.Weierstrass.Point.oAt L.M.n →
      wordsVal s₄.mem base x L.M.n = wordsVal s.mem base x L.M.n := fun hx =>
    U₁₃.wordsVal (by apart_ranges) (by omega_arith)
  refine countLoop_ok (Inv := fun j s' => LadInvP L wk C base size Q s s' j) (n := L.nbits)
    (fun j s' h1 h2 hi => ladderPBody_ok hL hW hF hk6 hPt hb8 hf (fun x hx => hlt x (mem_ladRo_ladR hx))
      hstep hbits h1 h2 hi)
    (fun s' hi => ⟨hi.keep, hi.unch, hi.mod, hi.lt, hi.q⟩) hL.nbits.1
    ⟨hs.of_rest K₄ (by decide), u₄.gpr, K₄, U₁₃.mono fun w hw => List.mem_append_right _ hw,
      hM.unch U₁₃ (by have := hPt.mo; apart_ranges) (by omega_arith), fun x hx => ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [low rx]; exact hlt _ (by simp [ladR])
    · rw [low ry]; exact hlt _ (by simp [ladR])
    · rw [low rz]; exact hlt _ (by simp [ladR])
  · show Q L.nbits (toM _ _ _) (toM _ _ _) (toM _ _ _)
    rw [low rx, low ry, low rz]
    exact hR
  · have k₂₄ : Unch base [(Spec.Weierstrass.Point.aAt L.M.n, 4 * (2 * L.M.n)),
        (Spec.Weierstrass.Point.b3At L.M.n, 4 * (2 * L.M.n))] s₁.mem s₄.mem := by
      rw [hm₄]; exact U₂.trans U₃
    have k₃₄ : Unch base [(Spec.Weierstrass.Point.b3At L.M.n, 4 * (2 * L.M.n))] s₂.mem s₄.mem := by
      rw [hm₄]; exact U₃
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [k₂₄.wordsVal (by apart_ranges) (by omega_arith), gx₁]
    · rw [k₂₄.wordsVal (by apart_ranges) (by omega_arith), gy₁]
    · rw [k₂₄.wordsVal (by apart_ranges) (by omega_arith), gz₁]
    · rw [k₃₄.wordsVal (by apart_ranges) (by omega_arith), a₂, (Outs.unch O₁).wordsVal (by apart_ranges) (by omega_arith)]
    · rw [hm₄, b₃, U₂.wordsVal (by apart_ranges) (by omega_arith), (Outs.unch O₁).wordsVal (by apart_ranges) (by omega_arith)]

end body

end VG.Proof.Weierstrass.Arm.Point
