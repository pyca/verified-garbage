module

public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.LadderPCall
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Ladder
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Pow
public import VerifiedGarbage.Impl.Weierstrass.PPC64LE.LadderP
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Bits
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Copy
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Loop
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The ladder by calls of the point functions, on PPC64LE

`ladderP L S` (`Impl/Weierstrass/PPC64LE/LadderP.lean`), for coordinates of
3 to 6 words, takes the loop's invariant `Q j` on what `R` holds to `Q 0`, if
an iteration keeps it (`Step`), for the scalar `k` whose bits are the table at
`L.bits` (`ladderP_ok`), as on 32-bit ARM
(`Proof/Weierstrass/Arm/LadderP.lean`): the setup copies `G`, `a` and `3b`
to the point functions' `Q`, `a` and `3b` (`ladderSetup_ok`, `CpOk`); an
iteration (`ladderPBody_ok`) copies `R` to `P`, so that the doubling's call
leaves `D = R + R` in `O` (`ptCall_ok`), copies it to `P`, so that the
addition's leaves `T = D + G` in `O`, and selects `R = T` or `D`. The
ladder's slots lie below the point functions' (`LadPtLay`); it writes `R`
and the point functions' slots and own working space (`ladWp`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.Point

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Weierstrass.PPC64LE.Point
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont
open VG.Spec.Weierstrass (Curve Fe)
open VG.Impl.Weierstrass.Point (elemBytes ownAt aAt b3At oAt pAt qAt)

/-- Apart from each of a few ranges, for numbers of the layout. -/
tactic_template "ppc_apart" : tactic => `(tactic| (simp only [List.mem_cons, List.mem_append, List.not_mem_nil,
  or_false, or_imp, forall_and, forall_eq_or_imp, forall_eq, List.mem_singleton]; omega_arith))

/-- What the ladder by calls of the point functions writes: `R` and the
point functions' slots and own working space. -/
def ladWpt (L : LadderCfg) : List (Nat × Nat) :=
  [(L.R.x, 8 * L.M.n), (L.R.y, 8 * L.M.n), (L.R.z, 8 * L.M.n), (oAt L.M.n, 4096 - oAt L.M.n)]

/-- The point functions' slots and own working space, which the ladder
writes if it calls them. -/
def ptW (n : Nat) : List (Nat × Nat) := if n ≤ 6 then [(oAt n, 4096 - oAt n)] else []

/-- What `ladderP` writes, whether it calls the point functions or not. -/
def ladWp (L : LadderCfg) : List (Nat × Nat) := ladWx L ++ ptW L.M.n

/-- The ladder's slots: `a`, `3b`, `G` and `R` below the point functions'
slots, at multiples of 4, `R`'s apart; and its table of bits above the
functions' own working space. -/
structure LadPtLay (L : LadderCfg) : Prop where
  k3 : 3 ≤ L.M.n
  k6 : L.M.n ≤ 6
  a : L.S.a + 8 * L.M.n ≤ oAt L.M.n
  b3 : L.S.b3 + 8 * L.M.n ≤ oAt L.M.n
  gx : L.G.x + 8 * L.M.n ≤ oAt L.M.n
  gy : L.G.y + 8 * L.M.n ≤ oAt L.M.n
  gz : L.G.z + 8 * L.M.n ≤ oAt L.M.n
  rx : L.R.x + 8 * L.M.n ≤ oAt L.M.n
  ry : L.R.y + 8 * L.M.n ≤ oAt L.M.n
  rz : L.R.z + 8 * L.M.n ≤ oAt L.M.n
  al : L.S.a % 4 = 0 ∧ L.S.b3 % 4 = 0 ∧ L.G.x % 4 = 0 ∧ L.G.y % 4 = 0 ∧ L.G.z % 4 = 0 ∧
    L.R.x % 4 = 0 ∧ L.R.y % 4 = 0 ∧ L.R.z % 4 = 0
  rne : (L.R.x + 8 * L.M.n ≤ L.R.y ∨ L.R.y + 8 * L.M.n ≤ L.R.x) ∧
    (L.R.x + 8 * L.M.n ≤ L.R.z ∨ L.R.z + 8 * L.M.n ≤ L.R.x) ∧
    (L.R.y + 8 * L.M.n ≤ L.R.z ∨ L.R.z + 8 * L.M.n ≤ L.R.y)
  bits : 4096 ≤ L.bits
  bitsE : L.bits + L.nbits ≤ 8192
  nbits : 1 ≤ L.nbits ∧ L.nbits < 2 ^ 15

section enc
variable (k : Nat) (dbl : Bool)

theorem enc_0 : enc k dbl 0 = oAt k := by simp [enc]
theorem enc_1 : enc k dbl 1 = oAt k + elemBytes k := by simp [enc]
theorem enc_2 : enc k dbl 2 = oAt k + 2 * elemBytes k := by simp [enc]; omega_arith
theorem enc_3 : enc k dbl 3 = pAt k := by simp [enc]
theorem enc_4 : enc k dbl 4 = pAt k + elemBytes k := by simp [enc]
theorem enc_5 : enc k dbl 5 = pAt k + 2 * elemBytes k := by simp [enc]; omega_arith
theorem enc_6 : enc k dbl 6 = if dbl then pAt k else qAt k := by simp [enc]
theorem enc_7 : enc k dbl 7 = (if dbl then pAt k else qAt k) + elemBytes k := by simp [enc]
theorem enc_8 : enc k dbl 8 = (if dbl then pAt k else qAt k) + 2 * elemBytes k := by simp [enc]; omega_arith
theorem enc_9 : enc k dbl 9 = aAt k := by simp [enc]
theorem enc_10 : enc k dbl 10 = b3At k := by simp [enc]

end enc

/-- The bounds a call needs, by offset. -/
theorem rIds_lt_of {k m : Nat} (dbl : Bool) {mem : Mem} {base : Addr}
    (h : ∀ x ∈ [pAt k, pAt k + elemBytes k, pAt k + 2 * elemBytes k,
      (if dbl then pAt k else qAt k), (if dbl then pAt k else qAt k) + elemBytes k,
      (if dbl then pAt k else qAt k) + 2 * elemBytes k, aAt k, b3At k],
      wordsVal mem base x k < m) :
    ∀ x ∈ rIds, wordsVal mem base (enc k dbl x) k < m := by
  intro x hx
  simp only [rIds, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [enc_3, enc_4, enc_5, enc_6, enc_7, enc_8, enc_9, enc_10] <;> exact h _ (by simp)

/-- The point functions' `Q`, `a` and `3b` in `m` hold `G`, `a` and `3b` of
`m₀`. -/
def CpOk (L : LadderCfg) (base : Addr) (m m₀ : Mem) : Prop :=
  wordsVal m base (qAt L.M.n) L.M.n = wordsVal m₀ base L.G.x L.M.n ∧
  wordsVal m base (qAt L.M.n + elemBytes L.M.n) L.M.n = wordsVal m₀ base L.G.y L.M.n ∧
  wordsVal m base (qAt L.M.n + 2 * elemBytes L.M.n) L.M.n = wordsVal m₀ base L.G.z L.M.n ∧
  wordsVal m base (aAt L.M.n) L.M.n = wordsVal m₀ base L.S.a L.M.n ∧
  wordsVal m base (b3At L.M.n) L.M.n = wordsVal m₀ base L.S.b3 L.M.n

/-- The copies survive changes apart from them. -/
theorem CpOk.keep {L : LadderCfg} {base : Addr} {m m' m₀ : Mem} (h : CpOk L base m m₀)
    (hk3 : 3 ≤ L.M.n) (hk6 : L.M.n ≤ 6) {W : List (Nat × Nat)} (hU : Unch base W m m')
    (hW : ∀ w ∈ W, w.1 + w.2 ≤ qAt L.M.n ∨ ownAt L.M.n ≤ w.1) :
    CpOk L base m' m₀ := by
  obtain ⟨h1, h2, he, hb3, ha, hq, -, -, -, -⟩ := lay_nums hk3 hk6
  have ap : ∀ x, qAt L.M.n ≤ x → x + 8 * L.M.n ≤ ownAt L.M.n →
      ∀ w ∈ W, x + 8 * L.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := fun x h1 h2 w hw =>
    (hW w hw).elim (fun h => .inr (Nat.le_trans h h1)) (fun h => .inl (Nat.le_trans h2 h))
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨by rw [hU.wordsVal (ap _ (by omega_arith) (by omega_arith)) (by omega_arith)]; exact h1,
    by rw [hU.wordsVal (ap _ (by omega_arith) (by omega_arith)) (by omega_arith)]; exact h2,
    by rw [hU.wordsVal (ap _ (by omega_arith) (by omega_arith)) (by omega_arith)]; exact h3,
    by rw [hU.wordsVal (ap _ (by omega_arith) (by omega_arith)) (by omega_arith)]; exact h4,
    by rw [hU.wordsVal (ap _ (by omega_arith) (by omega_arith)) (by omega_arith)]; exact h5⟩

/-- The loop's invariant at `r31 = j`: `Q j` accepts what `R` holds, and the
point functions' `Q`, `a` and `3b` hold `G`, `a` and `3b`. -/
structure LadInvP (L : LadderCfg) (C : Curve) (base : Addr)
    (Q : Nat → Fe C → Fe C → Fe C → Prop) (s₀ s : State) (j : Nat) : Prop where
  ws : WsReg s base
  r31 : s.gpr .r31 = BitVec.ofNat 64 j
  keep : Rk powClob s₀ s
  unch : Unch base (ladWpt L) s₀.mem s.mem
  lt : ∀ x ∈ [L.R.x, L.R.y, L.R.z], wordsVal s.mem base x L.M.n < C.p
  q : Q j (tmv C L.M.n base s L.R.x) (tmv C L.M.n base s L.R.y) (tmv C L.M.n base s L.R.z)
  cp : CpOk L base s.mem s₀.mem

/-- What a copy of three slots `a` below `P` or `Q` into it needs. -/
theorem copyPt_conds {k o : Nat} {a : Pt} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) (ho : o = pAt k ∨ o = qAt k)
    (hax : a.x + 8 * k ≤ o) (hay : a.y + 8 * k ≤ o) (haz : a.z + 8 * k ≤ o)
    (h4 : a.x % 4 = 0 ∧ a.y % 4 = 0 ∧ a.z % 4 = 0) :
    (∀ d ∈ [(ptAt k o).x, (ptAt k o).y, (ptAt k o).z, a.x, a.y, a.z], d % 4 = 0) ∧
    (∀ d ∈ [(ptAt k o).x, (ptAt k o).y, (ptAt k o).z, a.x, a.y, a.z], d + 8 * k ≤ 8192) ∧
    (((ptAt k o).x + 8 * k ≤ (ptAt k o).y ∨ (ptAt k o).y + 8 * k ≤ (ptAt k o).x) ∧
      ((ptAt k o).x + 8 * k ≤ (ptAt k o).z ∨ (ptAt k o).z + 8 * k ≤ (ptAt k o).x) ∧
      ((ptAt k o).y + 8 * k ≤ (ptAt k o).z ∨ (ptAt k o).z + 8 * k ≤ (ptAt k o).y)) ∧
    (∀ d ∈ [(ptAt k o).x, (ptAt k o).y, (ptAt k o).z], ∀ e ∈ [a.x, a.y, a.z],
      d + 8 * k ≤ e ∨ e + 8 * k ≤ d) := by
  obtain ⟨h1, h2, he, hb3, ha, hq, hp, hoo, -, h8⟩ := lay_nums hk3 hk6
  obtain ⟨a1, a2, a3⟩ := h4
  simp only [ptAt, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  rcases ho with rfl | rfl <;> omega_arith

/-- What a selection of `P` or `O` into three slots below `O` needs. -/
theorem selPt_conds {k : Nat} {a : Pt} (hk3 : 3 ≤ k) (hk6 : k ≤ 6)
    (hax : a.x + 8 * k ≤ oAt k) (hay : a.y + 8 * k ≤ oAt k) (haz : a.z + 8 * k ≤ oAt k)
    (h4 : a.x % 4 = 0 ∧ a.y % 4 = 0 ∧ a.z % 4 = 0) :
    (∀ d ∈ [a.x, a.y, a.z, (ptAt k (pAt k)).x, (ptAt k (pAt k)).y, (ptAt k (pAt k)).z,
      (ptAt k (oAt k)).x, (ptAt k (oAt k)).y, (ptAt k (oAt k)).z], d % 4 = 0) ∧
    (∀ d ∈ [a.x, a.y, a.z, (ptAt k (pAt k)).x, (ptAt k (pAt k)).y, (ptAt k (pAt k)).z,
      (ptAt k (oAt k)).x, (ptAt k (oAt k)).y, (ptAt k (oAt k)).z], d + 8 * k ≤ 8192) ∧
    (∀ d ∈ [a.x, a.y, a.z], ∀ e ∈ [(ptAt k (pAt k)).x, (ptAt k (pAt k)).y, (ptAt k (pAt k)).z,
      (ptAt k (oAt k)).x, (ptAt k (oAt k)).y, (ptAt k (oAt k)).z], d + 8 * k ≤ e ∨ e + 8 * k ≤ d) := by
  obtain ⟨h1, h2, he, hb3, ha, hq, hp, hoo, -, h8⟩ := lay_nums hk3 hk6
  obtain ⟨a1, a2, a3⟩ := h4
  simp only [ptAt, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  omega_arith

/-- What a range written within the point functions' slots keeps. -/
theorem pt_cover {k : Nat} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) {W : List (Nat × Nat)}
    (hW : ∀ w ∈ W, oAt k ≤ w.1 ∧ w.1 + w.2 ≤ 4096) :
    ∀ w ∈ W, ∃ w' ∈ [(oAt k, 4096 - oAt k)], w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 := by
  obtain ⟨-, -, -, -, -, -, -, -, ho, -⟩ := lay_nums hk3 hk6
  intro w hw
  have := hW w hw
  exact ⟨_, List.mem_singleton_self _, this.1, by simp only; omega_arith⟩

/-- `G`, `a` and `3b` to the point functions' `Q`, `a` and `3b`. -/
theorem ladderSetup_ok {L : LadderCfg} {base : Addr} {s : State} (hw : WsReg s base) (hL : LadPtLay L) :
    WP isa (.block (ladderSetup L)) s fun t =>
      Kp [.r4] s t ∧ Unch base [(oAt L.M.n, 4096 - oAt L.M.n)] s.mem t.mem ∧ CpOk L base t.mem s.mem := by
  have hk3 := hL.k3
  have hk6 := hL.k6
  obtain ⟨h1, h2, he, hb3, ha, hq, hp, hoo, ho1, h8⟩ := lay_nums hk3 hk6
  have hn := hw.nowrap
  obtain ⟨al, bl, gxl, gyl, gzl, -, -, -⟩ := hL.al
  have sa := hL.a; have sb := hL.b3; have sgx := hL.gx; have sgy := hL.gy; have sgz := hL.gz
  have cG := copyPt_conds (a := L.G) hk3 hk6 (.inr rfl) (by omega_arith) (by omega_arith) (by omega_arith) ⟨gxl, gyl, gzl⟩
  rw [ladderSetup, List.append_assoc, WP.block_append_iff]
  refine WP.mono (copyPt_ok hw.ws hw.at3 (n := L.M.n) (o := ptAt L.M.n (qAt L.M.n)) (a := L.G)
    cG.1 cG.2.1 cG.2.2.1 cG.2.2.2) fun s₁ ⟨gx₁, gy₁, gz₁, k₁, O₁⟩ => ?_
  simp only [ptAt] at gx₁ gy₁ gz₁ O₁
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok L.M.n (k₁.ws hw.ws) (k₁.at hw.at3) (o := aAt L.M.n) (a := L.S.a) (by omega_arith) al
    (by omega_arith) (by omega_arith) (by omega_arith)) fun s₂ ⟨a₂, k₂, O₂⟩ => ?_
  refine WP.mono (copy_ok L.M.n (k₂.ws (k₁.ws hw.ws)) (k₂.at (k₁.at hw.at3)) (o := b3At L.M.n) (a := L.S.b3)
    (by omega_arith) bl (by omega_arith) (by omega_arith) (by omega_arith)) fun s₃ ⟨b₃, k₃, O₃⟩ => ?_
  have U₁ : Unch base [(qAt L.M.n, 8 * L.M.n), (qAt L.M.n + elemBytes L.M.n, 8 * L.M.n),
      (qAt L.M.n + 2 * elemBytes L.M.n, 8 * L.M.n)] s.mem s₁.mem := O₁
  have U₂ : Unch base [(aAt L.M.n, 8 * L.M.n)] s₁.mem s₂.mem := O₂.unch
  have U₃ : Unch base [(b3At L.M.n, 8 * L.M.n)] s₂.mem s₃.mem := O₃.unch
  refine ⟨(k₁.trans k₂).trans k₃, ((U₁.trans U₂).trans U₃).cover (pt_cover hk3 hk6 fun w hw => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with ((rfl | rfl | rfl) | rfl) | rfl <;> (simp only; omega_arith)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [(U₂.trans U₃).wordsVal (by ppc_apart) (by omega_arith), gx₁]
  · rw [(U₂.trans U₃).wordsVal (by ppc_apart) (by omega_arith), gy₁]
  · rw [(U₂.trans U₃).wordsVal (by ppc_apart) (by omega_arith), gz₁]
  · rw [U₃.wordsVal (by ppc_apart) (by omega_arith), a₂, U₁.wordsVal (by ppc_apart) (by omega_arith)]
  · rw [b₃, U₂.wordsVal (by ppc_apart) (by omega_arith), U₁.wordsVal (by ppc_apart) (by omega_arith)]

section body
variable {L : LadderCfg} {C : Curve} {base : Addr}

/-- A doubling's result as `Step` has it: for `dbl` the second operand's
slots are the first's. -/
theorem ptVal_dbl {m : Nat} [NeZero m] (a0 : Bool) {E : Nat → Fin m} (h6 : E 6 = E 3) (h7 : E 7 = E 4)
    (h8 : E 8 = E 5) : ptVal a0 true E = ladDbl a0 (E 9) (E 10) (E 3) (E 4) (E 5) := by
  cases a0
  · simp only [ptVal, ladDbl, Bool.false_eq_true, ↓reduceIte, h6, h7, h8]
  · rfl

theorem ptVal_add {m : Nat} [NeZero m] (a0 : Bool) (E : Nat → Fin m) :
    ptVal a0 false E = ladAdd a0 (E 9) (E 10) (E 3) (E 4) (E 5) (E 6) (E 7) (E 8) := by
  cases a0 <;> rfl

theorem Eb_dbl {k m : Nat} [NeZero m] (mem : Mem) (base : Addr) :
    Eb k m true mem base 6 = Eb k m true mem base 3 ∧ Eb k m true mem base 7 = Eb k m true mem base 4 ∧
      Eb k m true mem base 8 = Eb k m true mem base 5 := by
  simp only [Eb, enc_3, enc_4, enc_5, enc_6, enc_7, enc_8, ↓reduceIte, and_self]

/-- An iteration. -/
theorem ladderPBody_ok {k : Nat} {Q : Nat → Fe C → Fe C → Fe C → Prop} {S : Impl.Weierstrass.Mont.Modulus}
    (hkS : S.k = L.M.n) (hmS : S.m = C.p) (hM : ModOk L.M.n C.p) (hodd : C.p % 2 = 1) (hL : LadPtLay L)
    {s₀ : State} (hlt₀ : ∀ x ∈ [L.S.a, L.S.b3, L.G.x, L.G.y, L.G.z], wordsVal s₀.mem base x L.M.n < C.p)
    {a0 : Bool} (hstep : Step L C base s₀ k Q a0)
    (hbits : ∀ t < L.nbits, s₀.mem (off base (L.bits + t)) = if k.testBit t then 1 else 0)
    {j : Nat} {s : State} (hj : 1 ≤ j) (hjn : j ≤ L.nbits) (hI : LadInvP L C base Q s₀ s j) :
    WP isa (ladderPBody L S a0) s fun s' => LadInvP L C base Q s₀ s' (j - 1) := by
  obtain ⟨c, w, m', k', d⟩ := S
  dsimp only at hkS hmS
  subst hkS hmS
  have hk3 := hL.k3
  have hk6 := hL.k6
  obtain ⟨h1, h2, he, hb3, ha, hq, hp, hoo, ho1, h8⟩ := lay_nums hk3 hk6
  have hn := hI.ws.nowrap
  have hbl := hL.bits
  have hbe := hL.bitsE
  have hnb := hL.nbits
  obtain ⟨-, -, -, -, -, rxl, ryl, rzl⟩ := hL.al
  have rx := hL.rx; have ry := hL.ry; have rz := hL.rz
  have cR := copyPt_conds (a := L.R) hk3 hk6 (.inl rfl) (by omega_arith) (by omega_arith) (by omega_arith) ⟨rxl, ryl, rzl⟩
  have cO := copyPt_conds (a := ptAt L.M.n (oAt L.M.n)) hk3 hk6 (.inl rfl)
    (by simp only [ptAt]; omega_arith) (by simp only [ptAt]; omega_arith) (by simp only [ptAt]; omega_arith)
    (by simp only [ptAt]; omega_arith)
  -- `r31 -= 1`.
  rw [ladderPBody]
  refine WP.seq (wp_decCounter hj hI.r31 ?_)
  generalize hs₁ : s.write .r31 (BitVec.ofNat 64 (j - 1)) = s₁
  have K₁ : Kp [.r31] s s₁ := by rw [← hs₁]; exact Kp.write _ _ (by decide)
  have w₁ := hI.ws.of_rk (K₁.rk (rs' := powClob))
  have m₁ : s₁.mem = s.mem := by rw [← hs₁]; rfl
  have c₁ : s₁.gpr .r31 = BitVec.ofNat 64 (j - 1) := by rw [← hs₁]; simp only [write_gpr, ite_true]
  -- `P = R`.
  refine WP.mono (copyPt_ok w₁.ws w₁.at3 (n := L.M.n) (o := ptAt L.M.n (pAt L.M.n)) (a := L.R)
    cR.1 cR.2.1 cR.2.2.1 cR.2.2.2) fun s₂ ⟨px₂, py₂, pz₂, k₂, O₂⟩ => ?_
  simp only [ptAt] at px₂ py₂ pz₂ O₂
  rw [m₁] at px₂ py₂ pz₂ O₂
  have w₂ := w₁.of_rk (k₂.rk (rs' := powClob))
  have cp₂ : CpOk L base s₂.mem s₀.mem := hI.cp.keep hk3 hk6 (W := [(pAt L.M.n, 8 * L.M.n),
    (pAt L.M.n + elemBytes L.M.n, 8 * L.M.n), (pAt L.M.n + 2 * elemBytes L.M.n, 8 * L.M.n)]) O₂ (by ppc_apart)
  obtain ⟨gx₂, gy₂, gz₂, ga₂, gb₂⟩ := cp₂
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlt₀
  obtain ⟨la, lb, lgx, lgy, lgz⟩ := hlt₀
  have lrx : wordsVal s.mem base L.R.x L.M.n < C.p := hI.lt _ (by simp)
  have lry : wordsVal s.mem base L.R.y L.M.n < C.p := hI.lt _ (by simp)
  have lrz : wordsVal s.mem base L.R.z L.M.n < C.p := hI.lt _ (by simp)
  -- `O = P + P`.
  refine WP.seq (WP.mono (ptCall_ok (S := ⟨c, w, C.p, L.M.n, d⟩) hM hodd hk3 hk6 true w₂
    (rIds_lt_of true fun x hx => by
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
  dsimp only at k₃ O₃ L₃ E₃
  obtain ⟨d6, d7, d8⟩ := Eb_dbl (k := L.M.n) (m := C.p) s₂.mem base
  rw [ptVal_dbl a0 d6 d7 d8] at E₃
  simp only [Eb, enc_0, enc_1, enc_2, enc_3, enc_4, enc_5, enc_9, enc_10] at E₃
  rw [ga₂, gb₂, px₂, py₂, pz₂] at E₃
  have l3x := L₃ 0 (by decide)
  have l3y := L₃ 1 (by decide)
  have l3z := L₃ 2 (by decide)
  rw [enc_0] at l3x
  rw [enc_1] at l3y
  rw [enc_2] at l3z
  have w₃ := w₂.of_rk (k₃.mono (rs' := powClob))
  -- `P = O`.
  refine WP.seq (WP.mono (copyPt_ok w₃.ws w₃.at3 (n := L.M.n) (o := ptAt L.M.n (pAt L.M.n))
    (a := ptAt L.M.n (oAt L.M.n)) cO.1 cO.2.1 cO.2.2.1 cO.2.2.2)
    fun s₄ ⟨px₄, py₄, pz₄, k₄, O₄⟩ => ?_)
  simp only [ptAt] at px₄ py₄ pz₄ O₄
  have w₄ := w₃.of_rk (k₄.rk (rs' := powClob))
  have cp₄ : CpOk L base s₄.mem s₀.mem :=
    (CpOk.keep ⟨gx₂, gy₂, gz₂, ga₂, gb₂⟩ hk3 hk6 O₃ (by ppc_apart)).keep
      hk3 hk6 (W := [(pAt L.M.n, 8 * L.M.n), (pAt L.M.n + elemBytes L.M.n, 8 * L.M.n),
        (pAt L.M.n + 2 * elemBytes L.M.n, 8 * L.M.n)]) O₄ (by ppc_apart)
  obtain ⟨gx₄, gy₄, gz₄, ga₄, gb₄⟩ := cp₄
  -- `O = P + Q`.
  refine WP.seq (WP.mono (ptCall_ok (S := ⟨c, w, C.p, L.M.n, d⟩) hM hodd hk3 hk6 false w₄
    (rIds_lt_of false fun x hx => by
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
  dsimp only at k₅ O₅ L₅ E₅
  rw [ptVal_add] at E₅
  simp only [Eb, enc_0, enc_1, enc_2, enc_3, enc_4, enc_5, enc_6, enc_7, enc_8, enc_9, enc_10,
    Bool.false_eq_true, ↓reduceIte] at E₅
  rw [ga₄, gb₄, px₄, py₄, pz₄, gx₄, gy₄, gz₄] at E₅
  have l5x := L₅ 0 (by decide)
  have l5y := L₅ 1 (by decide)
  have l5z := L₅ 2 (by decide)
  rw [enc_0] at l5x
  rw [enc_1] at l5y
  rw [enc_2] at l5z
  have U₅ : Unch base [(oAt L.M.n, 3 * elemBytes L.M.n), (ownAt L.M.n, 4096 - ownAt L.M.n)] s₄.mem s₅.mem := O₅
  -- `P` still holds `D`.
  have p5x : wordsVal s₅.mem base (pAt L.M.n) L.M.n = wordsVal s₃.mem base (oAt L.M.n) L.M.n := by
    rw [U₅.wordsVal (by ppc_apart)
      (by omega_arith), px₄]
  have p5y : wordsVal s₅.mem base (pAt L.M.n + elemBytes L.M.n) L.M.n =
      wordsVal s₃.mem base (oAt L.M.n + elemBytes L.M.n) L.M.n := by
    rw [U₅.wordsVal (by ppc_apart)
      (by omega_arith), py₄]
  have p5z : wordsVal s₅.mem base (pAt L.M.n + 2 * elemBytes L.M.n) L.M.n =
      wordsVal s₃.mem base (oAt L.M.n + 2 * elemBytes L.M.n) L.M.n := by
    rw [U₅.wordsVal (by ppc_apart)
      (by omega_arith), pz₄]
  have cp₅ : CpOk L base s₅.mem s₀.mem := CpOk.keep ⟨gx₄, gy₄, gz₄, ga₄, gb₄⟩ hk3 hk6 U₅ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_arith)
  -- What changed: the point functions' slots.
  have U₁₅ : Unch base [(oAt L.M.n, 4096 - oAt L.M.n)] s.mem s₅.mem :=
    ((((show Unch base _ s.mem s₂.mem from O₂).trans (show Unch base _ s₂.mem s₃.mem from O₃)).trans
      (show Unch base _ s₃.mem s₄.mem from O₄)).trans U₅).cover (pt_cover hk3 hk6 fun w hw => by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with (((rfl | rfl | rfl) | rfl | rfl) | rfl | rfl | rfl) | rfl | rfl <;> (simp only; omega_arith))
  have hU₅ : Unch base (ladWpt L) s₀.mem s₅.mem :=
    (hI.unch.trans U₁₅).mono fun w hw => by
      simp only [ladWpt, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
      rcases hw with (h | h | h | h) | h <;> simp [h]
  have hbyte : s₅.mem (off base (L.bits + (j - 1))) = if k.testBit (j - 1) then 1 else 0 := by
    rw [hU₅.byte (fun w hw => by
      simp only [ladWpt, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl <;> (simp only; omega_arith)) (by omega_arith), hbits _ (by omega_arith)]
  have K₅ : Rk powClob s s₅ :=
    (K₁.rk (rs' := powClob)).trans <| (k₂.rk (rs' := powClob)).trans <| (k₃.mono (rs' := powClob)).trans <|
      (k₄.rk (rs' := powClob)).trans (k₅.mono (rs' := powClob))
  have c₅ : s₅.gpr .r31 = BitVec.ofNat 64 (j - 1) := by
    rw [k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), c₁]
  have w₅ := w₄.of_rk (k₅.mono (rs' := powClob))
  -- `R = O` or `P`.
  refine wp_append (WP.mono (bitMask_bool_ok w₅.ws w₅.at3 c₅ (by omega_arith) hbyte) fun s₆ ⟨g₆, k₆, m₆⟩ => ?_)
  have sR := selPt_conds (a := L.R) hk3 hk6 rx ry rz ⟨rxl, ryl, rzl⟩
  refine WP.mono (selPt_ok (k₆.ws w₅.ws) (k₆.at w₅.at3) _ g₆ (n := L.M.n) (o := L.R)
    (a := ptAt L.M.n (pAt L.M.n)) (b := ptAt L.M.n (oAt L.M.n)) sR.1 sR.2.1 hL.rne sR.2.2)
    fun s₇ ⟨ex, ey, ez, k₇, O₇⟩ => ?_
  simp only [ptAt] at ex ey ez
  rw [m₆] at ex ey ez
  have U₅₇ : Unch base [(L.R.x, 8 * L.M.n), (L.R.y, 8 * L.M.n), (L.R.z, 8 * L.M.n)] s₅.mem s₇.mem := by
    rw [← m₆]; exact O₇
  have K₇ : Rk powClob s₅ s₇ := (k₆.rk (rs' := powClob)).trans (k₇.rk (rs' := powClob))
  refine ⟨w₅.of_rk K₇, by rw [k₇.g, k₆.g, c₅], (hI.keep.trans K₅).trans K₇, ?_, ?_, ?_, ?_⟩
  · exact (hU₅.trans U₅₇).mono fun w hw => by
      simp only [ladWpt, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
      rcases hw with (h | h | h | h) | (h | h | h) <;> simp [h]
  · intro x hx
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
  · have hq := hstep (j - 1) (by omega_arith) _ _ _ _ _ _ _ _ _ (by rw [Nat.sub_add_cancel hj]; exact hI.q)
      E₃.symm E₅.symm
    have hx : tmv C L.M.n base s₇ L.R.x = if k.testBit (j - 1) then
        toM C.p (2 ^ (64 * L.M.n)) (wordsVal s₅.mem base (oAt L.M.n) L.M.n) else
        toM C.p (2 ^ (64 * L.M.n)) (wordsVal s₃.mem base (oAt L.M.n) L.M.n) := by
      show toM _ _ _ = _
      rw [ex]; split
      · rfl
      · rw [p5x]
    have hy : tmv C L.M.n base s₇ L.R.y = if k.testBit (j - 1) then
        toM C.p (2 ^ (64 * L.M.n)) (wordsVal s₅.mem base (oAt L.M.n + elemBytes L.M.n) L.M.n) else
        toM C.p (2 ^ (64 * L.M.n)) (wordsVal s₃.mem base (oAt L.M.n + elemBytes L.M.n) L.M.n) := by
      show toM _ _ _ = _
      rw [ey]; split
      · rfl
      · rw [p5y]
    have hz : tmv C L.M.n base s₇ L.R.z = if k.testBit (j - 1) then
        toM C.p (2 ^ (64 * L.M.n)) (wordsVal s₅.mem base (oAt L.M.n + 2 * elemBytes L.M.n) L.M.n) else
        toM C.p (2 ^ (64 * L.M.n)) (wordsVal s₃.mem base (oAt L.M.n + 2 * elemBytes L.M.n) L.M.n) := by
      show toM _ _ _ = _
      rw [ez]; split
      · rfl
      · rw [p5z]
    rw [hx, hy, hz]
    exact hq
  · exact cp₅.keep hk3 hk6 U₅₇ (by ppc_apart)

/-- `Q 0` accepts what `R` holds at the end, if `Q L.nbits` accepts what it
holds at the start and an iteration keeps `Q` (`Step`), for the scalar `k`
whose bits are the table at `L.bits`, by calls of the point functions; only
`powClob` and `ladWpt` change. -/
theorem ladderPt_ok {k : Nat} {Q : Nat → Fe C → Fe C → Fe C → Prop} {S : Impl.Weierstrass.Mont.Modulus}
    (hkS : S.k = L.M.n) (hmS : S.m = C.p) (hM : ModOk L.M.n C.p) (hodd : C.p % 2 = 1) (hL : LadPtLay L)
    {s : State} (hs : WsReg s base)
    (hlt : ∀ x ∈ [L.S.a, L.S.b3, L.G.x, L.G.y, L.G.z, L.R.x, L.R.y, L.R.z],
      wordsVal s.mem base x L.M.n < C.p)
    {a0 : Bool} (hstep : Step L C base s k Q a0)
    (hR : Q L.nbits (tmv C L.M.n base s L.R.x) (tmv C L.M.n base s L.R.y) (tmv C L.M.n base s L.R.z))
    (hbits : ∀ t < L.nbits, s.mem (off base (L.bits + t)) = if k.testBit t then 1 else 0) :
    WP isa (ladderP L S a0) s fun s' => Rk powClob s s' ∧ Unch base (ladWpt L) s.mem s'.mem ∧
      (∀ x ∈ [L.R.x, L.R.y, L.R.z], wordsVal s'.mem base x L.M.n < C.p) ∧
      Q 0 (tmv C L.M.n base s' L.R.x) (tmv C L.M.n base s' L.R.y) (tmv C L.M.n base s' L.R.z) := by
  have hk3 := hL.k3
  have hk6 := hL.k6
  obtain ⟨h1, h2, he, hb3, ha, hq, hp, hoo, ho1, h8⟩ := lay_nums hk3 hk6
  have hn := hs.nowrap
  have hnb := hL.nbits
  have rx := hL.rx; have ry := hL.ry; have rz := hL.rz
  unfold ladderP
  simp only [hk6, ↓reduceIte]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (ladderSetup_ok hs hL) fun s₃ ⟨k₃, U₃, cp₃⟩ =>
    wp_step (exec_li hnb.2) (WP.block_nil ?_)
  have K₄ : Kp powClob s (s₃.write .r31 (BitVec.ofNat 64 L.nbits)) :=
    (k₃.mono (by decide)).trans (Kp.write _ _ (by decide))
  have low : ∀ {x}, x + 8 * L.M.n ≤ oAt L.M.n →
      wordsVal (s₃.write .r31 (BitVec.ofNat 64 L.nbits)).mem base x L.M.n = wordsVal s.mem base x L.M.n :=
    fun hx => by rw [write_mem]; exact U₃.wordsVal (by ppc_apart) (by omega_arith)
  refine countLoop_ok (Inv := fun j s' => LadInvP L C base Q s s' j) (n := L.nbits)
    (fun j s' hi => hi.r31)
    (fun j s' h1 h2 hi => ladderPBody_ok hkS hmS hM hodd hL (fun x hx => hlt x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with h | h | h | h | h <;> simp [h])) hstep hbits h1 h2 hi)
    (fun s' hi => ⟨hi.keep, hi.unch, hi.lt, hi.q⟩) hnb.1 (by omega_arith)
    ⟨hs.of_rk (K₄.rk (rs' := powClob)), by simp only [write_gpr, ite_true], K₄.rk,
      U₃.mono fun w hw => by simp at hw; simp [hw, ladWpt], fun x hx => ?_, ?_, cp₃⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [low rx]; exact hlt _ (by simp)
    · rw [low ry]; exact hlt _ (by simp)
    · rw [low rz]; exact hlt _ (by simp)
  · show Q L.nbits (toM _ _ _) (toM _ _ _) (toM _ _ _)
    rw [low rx, low ry, low rz]
    exact hR

/-- `Q 0` accepts what `R` holds at the end, if `Q L.nbits` accepts what it
holds at the start and an iteration keeps `Q` (`Step`), for the scalar `k`
whose bits are the table at `L.bits`: by calls of the point functions for
coordinates of at most 6 words (`ladderPt_ok`, whose slots `LadPtLay` gives),
else by the complete addition inlined (`ladder_ok`, `LadLayI`); only
`powClob` and `ladWp` change. -/
theorem ladderP_ok {k : Nat} {Q : Nat → Fe C → Fe C → Fe C → Prop} {S : Impl.Weierstrass.Mont.Modulus}
    (hkS : S.k = L.M.n) (hmS : S.m = C.p) (hM : ModOk L.M.n C.p) (hodd : C.p % 2 = 1)
    (hp : UnitMod C.p (2 ^ (64 * L.M.n))) (hP : L.M.n ≤ 6 → LadPtLay L) (hX : 6 < L.M.n → LadLayI L)
    {s : State} (hs : WsReg s base)
    (hlt : ∀ x ∈ [L.S.a, L.S.b3, L.G.x, L.G.y, L.G.z, L.R.x, L.R.y, L.R.z],
      wordsVal s.mem base x L.M.n < C.p)
    {a0 : Bool} (ha0 : a0 = true → L.M.n ≤ 6) (hstep : Step L C base s k Q a0)
    (hR : Q L.nbits (tmv C L.M.n base s L.R.x) (tmv C L.M.n base s L.R.y) (tmv C L.M.n base s L.R.z))
    (hbits : ∀ t < L.nbits, s.mem (off base (L.bits + t)) = if k.testBit t then 1 else 0) :
    WP isa (ladderP L S a0) s fun s' => Rk powClob s s' ∧ Unch base (ladWp L) s.mem s'.mem ∧
      (∀ x ∈ [L.R.x, L.R.y, L.R.z], wordsVal s'.mem base x L.M.n < C.p) ∧
      Q 0 (tmv C L.M.n base s' L.R.x) (tmv C L.M.n base s' L.R.y) (tmv C L.M.n base s' L.R.z) := by
  by_cases hk6 : L.M.n ≤ 6
  · refine WP.mono (ladderPt_ok hkS hmS hM hodd (hP hk6) hs hlt hstep hR hbits)
      fun s' ⟨K, U, l, q⟩ => ⟨K, U.mono fun w hw => ?_, l, q⟩
    simp only [ladWpt, List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [ladWp, ptW, hk6, ↓reduceIte, List.mem_append, List.mem_singleton]
    rcases hw with rfl | rfl | rfl | rfl
    · exact .inl (List.mem_append_left _ (mem_ladW_R _ (by simp)))
    · exact .inl (List.mem_append_left _ (mem_ladW_R _ (by simp)))
    · exact .inl (List.mem_append_left _ (mem_ladW_R _ (by simp)))
    · exact .inr rfl
  · unfold ladderP
    simp only [hk6, ↓reduceIte]
    have hM' : ModOk S.k S.m := by rw [hkS, hmS]; exact hM
    cases a0
    swap; · exact absurd (ha0 rfl) hk6
    exact WP.mono (ladder_ok hM' hkS hmS hp (hX (by omega_arith)) hs hlt hstep hR hbits)
      fun s' ⟨K, U, l, q⟩ => ⟨K, U.mono fun w hw => List.mem_append_left _ hw, l, q⟩

end body

end VG.Proof.Weierstrass.PPC64LE.Point
