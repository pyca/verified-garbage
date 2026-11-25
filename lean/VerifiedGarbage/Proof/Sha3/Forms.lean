module

public import VerifiedGarbage.Proof.Sha3.Lanes
import VerifiedGarbage.Proof.Framework.Omega
import all Init.Data.Nat.Bitwise.Basic

/-!
# Keccak-f[1600]: a round's lanes as forms in its input lanes

What straight-line code of a round computes from 25 words (`env i`, the
input lanes) is a *form*: the XOR of rotations of them, and of ANDs of two
such XORs. A XOR of rotations is one number, 64 bits for each lane: bit
`64 i + r` is set where lane `i` rotated left by `r` takes part. XOR of two
is then XOR of the numbers, and a rotation rotates every 64-bit field
(`rotl`), two shifts. So an evaluator that tracks every register's form is
cheap for the kernel, whatever the code's order, registers and pending
rotations, and code is right when the forms it ends with are the round's
(`chiForm`).
-/

@[expose] public section

namespace VG.Proof.Sha3.Forms

/-! ## XOR of finitely many bits -/

/-- `f 0 ⊕ … ⊕ f (n - 1)`. -/
def xsum (f : Nat → Bool) : Nat → Bool
  | 0 => false
  | n + 1 => xsum f n ^^ f n

theorem xsum_xor (f g : Nat → Bool) (n : Nat) :
    xsum (fun i => f i ^^ g i) n = (xsum f n ^^ xsum g n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [xsum, ih]; cases xsum f n <;> cases xsum g n <;> cases f n <;> cases g n <;> rfl

theorem xsum_congr {f g : Nat → Bool} {n : Nat} (h : ∀ i < n, f i = g i) : xsum f n = xsum g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [xsum, ih fun i hi => h i (Nat.lt_succ_of_lt hi), h n (Nat.lt_succ_self n)]

theorem xsum_false {f : Nat → Bool} {n : Nat} (h : ∀ i < n, f i = false) : xsum f n = false := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [xsum, ih fun i hi => h i (Nat.lt_succ_of_lt hi), h n (Nat.lt_succ_self n)]; rfl

theorem xsum_single {f : Nat → Bool} {n k : Nat} (hk : k < n) (h : ∀ i < n, i ≠ k → f i = false) :
    xsum f n = f k := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [xsum]
    by_cases hkn : k = n
    · subst hkn
      rw [xsum_false fun i hi => h i (Nat.lt_succ_of_lt hi) (by omega)]; simp
    · rw [ih (by omega) fun i hi => h i (by omega), h n (by omega) (by omega)]; simp

/-! ## Linear forms -/

/-- Bit `j` of the linear form `m` in the lanes `env`. -/
def linBit (env : Nat → BitVec 64) (m j : Nat) : Bool :=
  xsum (fun i => xsum (fun s => m.testBit (64 * i + (j + 64 - s) % 64) && (env i).getLsbD s) 64) 25

/-- The numbers of 25 fields of 64 bits, each with its low `w` bits set. -/
def fields (w : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => 2 ^ 64 * fields w n + (2 ^ w - 1)

/-- The linear form rotated left by `k`. -/
def rotl (k m : Nat) : Nat :=
  if k = 0 then m else
    ((m &&& fields (64 - k) 25) <<< k) ||| ((m >>> (64 - k)) &&& fields k 25)

theorem fields_testBit {w : Nat} (hw : w ≤ 64) (n i r : Nat) (hr : r < 64) :
    (fields w n).testBit (64 * i + r) = (decide (i < n) && decide (r < w)) := by
  induction n generalizing i with
  | zero => simp [fields]
  | succ n ih =>
    have h1 : 2 ^ w - 1 < 2 ^ 64 := by
      have := Nat.pow_le_pow_right (n := 2) (by decide) hw
      have := Nat.two_pow_pos w
      omega
    simp only [fields]
    rw [Nat.testBit_two_pow_mul_add _ h1]
    cases i with
    | zero => simp [hr, Nat.testBit_two_pow_sub_one]
    | succ i =>
      rw [ite_eq_right (by omega), show 64 * (i + 1) + r - 64 = 64 * i + r by omega, ih]
      simp

theorem rotl_testBit {k : Nat} (hk : k < 64) (m : Nat) {i r : Nat} (hi : i < 25) (hr : r < 64) :
    (rotl k m).testBit (64 * i + r) = m.testBit (64 * i + (r + 64 - k) % 64) := by
  unfold rotl
  split
  · subst_vars; rw [show (r + 64 - 0) % 64 = r by omega]
  rename_i h0
  rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_shiftRight,
    fields_testBit (by omega) _ _ _ hr]
  by_cases hrk : r < k
  · rw [show (r + 64 - k) % 64 = r + 64 - k by omega]
    have hz : ((decide (64 * i + r ≥ k)) && (m.testBit (64 * i + r - k) && (fields (64 - k) 25).testBit (64 * i + r - k))) = false := by
      cases i with
      | zero => simp; omega
      | succ i =>
        rw [show 64 * (i + 1) + r - k = 64 * i + (64 + r - k) by omega,
          fields_testBit (by omega) _ _ _ (by omega)]
        simp; omega
    rw [hz]
    simp only [Bool.false_or, hi, hrk, decide_true, Bool.and_true]
    congr 1; omega
  · rw [show (r + 64 - k) % 64 = r - k by omega, show 64 * i + r - k = 64 * i + (r - k) by omega,
      fields_testBit (by omega) _ _ _ (by omega)]
    simp only [hi, hrk, decide_false, decide_true, Bool.and_false, Bool.or_false, Bool.true_and,
      show r - k < 64 - k by omega, Bool.and_true, show 64 * i + r ≥ k by omega]

theorem linBit_xor (env : Nat → BitVec 64) (a b j : Nat) :
    linBit env (a ^^^ b) j = (linBit env a j ^^ linBit env b j) := by
  simp only [linBit, ← xsum_xor]
  refine xsum_congr fun i _ => ?_
  refine xsum_congr fun s _ => ?_
  rw [Nat.testBit_xor]
  cases a.testBit _ <;> cases b.testBit _ <;> cases (env i).getLsbD s <;> rfl

theorem linBit_rotl (env : Nat → BitVec 64) {k : Nat} (hk : k < 64) (m : Nat) {j : Nat} (hj : j < 64) :
    linBit env (rotl k m) j = linBit env m ((j + 64 - k) % 64) := by
  refine xsum_congr fun i hi => ?_
  refine xsum_congr fun s hs => ?_
  rw [rotl_testBit hk m hi (Nat.mod_lt _ (by decide))]
  congr 3
  omega

/-- The form that is lane `i`. -/
def atom (i : Nat) : Nat := 2 ^ (64 * i)

theorem linBit_atom (env : Nat → BitVec 64) {i j : Nat} (hi : i < 25) (hj : j < 64) :
    linBit env (atom i) j = (env i).getLsbD j := by
  unfold linBit atom
  rw [xsum_single hi fun i' _ hne => xsum_false fun s hs => ?_, xsum_single hj fun s hs hne => ?_]
  · rw [show (j + 64 - j) % 64 = 0 by omega]; simp
  · rw [Nat.testBit_two_pow]
    simp only [Bool.and_eq_false_imp, decide_eq_true_eq]
    intro h; omega
  · rw [Nat.testBit_two_pow]
    simp only [Bool.and_eq_false_imp, decide_eq_true_eq]
    intro h; omega

/-! ## Forms -/

/-- The XOR of a linear form and of products of two. -/
structure Form where
  lin : Nat
  prods : List (Nat × Nat)
  deriving DecidableEq

/-- Bit `j` of the products. -/
def prodBit (env : Nat → BitVec 64) : List (Nat × Nat) → Nat → Bool
  | [], _ => false
  | (a, b) :: ps, j => (linBit env a j && linBit env b j) ^^ prodBit env ps j

/-- The form `f` in the lanes `env` is the word `x`. -/
def Is (env : Nat → BitVec 64) (f : Form) (x : BitVec 64) : Prop :=
  ∀ j < 64, x.getLsbD j = (linBit env f.lin j ^^ prodBit env f.prods j)

theorem Is.unique {env : Nat → BitVec 64} {f : Form} {x y : BitVec 64} (hx : Is env f x) (hy : Is env f y) :
    x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [hx j hj, hy j hj]

theorem prodBit_append (env : Nat → BitVec 64) (a b : List (Nat × Nat)) (j : Nat) :
    prodBit env (a ++ b) j = (prodBit env a j ^^ prodBit env b j) := by
  induction a with
  | nil => simp [prodBit]
  | cons p a ih => simp only [List.cons_append, prodBit, ih, Bool.xor_assoc]

namespace Form

def xor (f g : Form) : Form := ⟨f.lin ^^^ g.lin, f.prods ++ g.prods⟩

def rot (k : Nat) (f : Form) : Form :=
  ⟨rotl k f.lin, f.prods.map fun p => (rotl k p.1, rotl k p.2)⟩

/-- A product, its factors in order. -/
def prod (a b : Nat) : Nat × Nat := if a ≤ b then (a, b) else (b, a)

/-- `f ∧ ¬g`, of linear forms. -/
def bic (f g : Form) : Option Form :=
  match f.prods, g.prods with
  | [], [] => some ⟨f.lin, [prod f.lin g.lin]⟩
  | _, _ => none

def ofLane (i : Nat) : Form := ⟨atom i, []⟩

end Form

theorem Is.xor {env : Nat → BitVec 64} {f g : Form} {x y : BitVec 64} (hx : Is env f x) (hy : Is env g y) :
    Is env (f.xor g) (x ^^^ y) := by
  intro j hj
  rw [BitVec.getLsbD_xor, hx j hj, hy j hj]
  simp only [Form.xor, linBit_xor, prodBit_append]
  cases linBit env f.lin j <;> cases linBit env g.lin j <;> cases prodBit env f.prods j <;>
    cases prodBit env g.prods j <;> rfl

theorem prodBit_rot (env : Nat → BitVec 64) {k : Nat} (hk : k < 64) (ps : List (Nat × Nat)) {j : Nat} (hj : j < 64) :
    prodBit env (ps.map fun p => (rotl k p.1, rotl k p.2)) j = prodBit env ps ((j + 64 - k) % 64) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [List.map_cons, prodBit, ih, linBit_rotl env hk _ hj]

theorem Is.rot {env : Nat → BitVec 64} {f : Form} {x : BitVec 64} (hx : Is env f x) {k : Nat} (hk : k < 64) :
    Is env (f.rot k) (x.rotateLeft k) := by
  intro j hj
  simp only [Form.rot, linBit_rotl env hk _ hj, prodBit_rot env hk _ hj]
  rw [← hx _ (Nat.mod_lt _ (by decide))]
  rw [BitVec.getLsbD_rotateLeft]
  rw [Nat.mod_eq_of_lt hk]
  split
  · congr 1; omega
  · rw [show (j + 64 - k) % 64 = j - k by omega]; simp [hj]

/-- A rotation right by `k`, as the instructions have it. -/
theorem Is.ror {env : Nat → BitVec 64} {f : Form} {x : BitVec 64} (hx : Is env f x) {k : Nat} (hk : k < 64) :
    Is env (f.rot ((64 - k) % 64)) (x.rotateRight k) := by
  by_cases h0 : k = 0
  · subst h0
    have : x.rotateRight 0 = x.rotateLeft 0 := by
      rw [rotateLeft_zero]
      ext i hi
      simp only [BitVec.getElem_rotateRight]
      split <;> first | (exfalso; omega) | exact getElem_congr rfl (by omega) _
    rw [this]; exact hx.rot (by decide)
  · rw [Nat.mod_eq_of_lt (by omega), show x.rotateRight k = x.rotateLeft (64 - k) by
      rw [rotateLeft_eq _ (by omega) (by omega)]; congr 1; omega]
    exact hx.rot (by omega)

theorem prodBit_prod (env : Nat → BitVec 64) (a b j : Nat) :
    prodBit env [Form.prod a b] j = (linBit env a j && linBit env b j) := by
  unfold Form.prod
  split <;> simp [prodBit, Bool.and_comm]

theorem Is.bic {env : Nat → BitVec 64} {f g h : Form} {x y : BitVec 64} (hx : Is env f x) (hy : Is env g y)
    (e : f.bic g = some h) : Is env h (x &&& ~~~y) := by
  unfold Form.bic at e
  split at e
  · rename_i h1 h2
    cases e
    intro j hj
    rw [BitVec.getLsbD_and, BitVec.getLsbD_not, hx j hj, hy j hj, h1, h2]
    simp only [prodBit_prod, hj, decide_true, Bool.true_and]
    simp only [prodBit, Bool.xor_false]
    cases linBit env f.lin j <;> cases linBit env g.lin j <;> rfl
  · cases e

theorem Is.lane {env : Nat → BitVec 64} {i : Nat} (hi : i < 25) : Is env (Form.ofLane i) (env i) := by
  intro j hj
  simp only [Form.ofLane, linBit_atom env hi hj, prodBit, Bool.xor_false]

/-! ## The round -/

open VG.Impl.Sha3 (rhoOff piSrc)

/-- The parity of column `x`. -/
def colForm (x : Nat) : Form :=
  (((Form.ofLane x).xor (.ofLane (x + 5))).xor (.ofLane (x + 10))).xor (.ofLane (x + 15)) |>.xor (.ofLane (x + 20))

/-- Lane `x` of plane `y` after θ, ρ and π. -/
def bForm (x y : Nat) : Form :=
  ((Form.ofLane (piSrc x y)).xor
    (((colForm (((x + 3 * y) % 5 + 1) % 5)).rot 1).xor (colForm (((x + 3 * y) % 5 + 4) % 5)))).rot (rhoOff (piSrc x y))

/-- Lane `x` of plane `y` after θ, ρ, π and χ. -/
def chiForm (x y : Nat) : Form :=
  let b := (bForm ((x + 2) % 5) y).lin
  ⟨(bForm x y).lin ^^^ b, [Form.prod b (bForm ((x + 1) % 5) y).lin]⟩

/-- The state after θ, ρ, π and χ. -/
abbrev core (A : Spec.Sha3.State) : Spec.Sha3.State := Spec.Sha3.chi (Spec.Sha3.pi (Spec.Sha3.rho (Spec.Sha3.theta A)))

theorem C_is (A : Spec.Sha3.State) {x : Nat} (hx : x < 5) : Is (fun i => A[i]!) (colForm x) (C A x) :=
  ((((Is.lane (by omega)).xor (Is.lane (by omega))).xor (Is.lane (by omega))).xor (Is.lane (by omega))).xor
    (Is.lane (by omega))

theorem B_is (A : Spec.Sha3.State) {x : Nat} (hx : x < 5) (y : Nat) : Is (fun i => A[i]!) (bForm x y) (B A x y) := by
  have hj : piSrc x y < 25 := by simp only [piSrc]; omega
  rw [B, rotl_eq _ (rhoOff_lt _ hj)]
  refine Is.rot (Is.xor (Is.lane hj) ?_) (rhoOff_lt _ hj)
  exact Is.xor ((C_is A (Nat.mod_lt _ (by decide))).ror (k := 63) (by decide)) (C_is A (Nat.mod_lt _ (by decide)))

theorem chi_is (A : Spec.Sha3.State) {i : Nat} (hi : i < 25) :
    Is (fun i => A[i]!) (chiForm (i % 5) (i / 5)) (core A)[i]! := by
  have hx : i % 5 < 5 := Nat.mod_lt _ (by decide)
  have hy : i / 5 < 5 := by omega
  have hchi := chi_get (Spec.Sha3.pi (Spec.Sha3.rho (Spec.Sha3.theta A))) hx hy
  rw [pi_get _ hx hy, pi_get _ (Nat.mod_lt (i % 5 + 1) (by decide)) hy, pi_get _ (Nat.mod_lt (i % 5 + 2) (by decide)) hy,
    ← B_eq _ hx hy, ← B_eq _ (Nat.mod_lt _ (by decide)) hy, ← B_eq _ (Nat.mod_lt _ (by decide)) hy] at hchi
  rw [getElem!_eq _ hi]
  simp only [show i % 5 + 5 * (i / 5) = i by omega] at hchi
  rw [hchi, BitVec.and_comm]
  intro j hj
  have hb := (B_is A hx (i / 5)) j hj
  have h2 := (B_is A (Nat.mod_lt (i % 5 + 2) (by decide)) (i / 5)) j hj
  have h1 := (B_is A (Nat.mod_lt (i % 5 + 1) (by decide)) (i / 5)) j hj
  have e : ∀ x y, (bForm x y).prods = [] := fun _ _ => rfl
  simp only [e, prodBit, Bool.xor_false] at hb h1 h2
  rw [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not, hb, h1, h2]
  simp only [chiForm, linBit_xor, prodBit_prod, hj, decide_true, Bool.true_and]
  cases linBit _ (bForm (i % 5) (i / 5)).lin j <;> cases linBit _ (bForm ((i % 5 + 2) % 5) (i / 5)).lin j <;>
    cases linBit _ (bForm ((i % 5 + 1) % 5) (i / 5)).lin j <;> rfl

/-- The round constant. -/
theorem rnd_core (A : Spec.Sha3.State) (r : Nat) {i : Nat} (hi : i < 25) :
    (Spec.Sha3.rnd A r)[i]! = if i = 0 then (core A)[0]! ^^^ Spec.Sha3.RC r else (core A)[i]! := by
  rw [getElem!_eq _ hi]
  simp only [Spec.Sha3.rnd, Spec.Sha3.iota]
  split
  · subst_vars; rw [Vector.getElem_set_self]; rfl
  · rw [Vector.getElem_set_ne _ _ (by omega), getElem!_eq _ hi]

end VG.Proof.Sha3.Forms
