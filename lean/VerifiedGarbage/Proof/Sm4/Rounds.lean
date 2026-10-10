import VerifiedGarbage.Proof.Sm4.Bitsliced

/-!
# SM4's rounds as the implementations run them

The implementations keep the four words of the state in place: round `r`
replaces word `r mod 4` with its new value, so that after every four rounds
the words are in the specification's order again. `sround l rk a x` is such
a round (with `T` for `l = .enc`, `T'` for `l = .key`) on the words `x 0 …
x 3`, `quad` four of them with the round keys `K (4 m) … K (4 m + 3)`, and
`quads` the first `n` groups.

`crypt_eq`: the specification's 32 rounds and final reversal are eight
`quad`s, the output words in reverse order. `expandKey_eq`: the round key
`rk_i` of the key schedule is word `i mod 4` after `⌊i / 4⌋ + 1` `quad`s of
the key schedule's rounds from `MK ⊕ FK`.
-/

namespace VG.Proof.Sm4

open VG VG.Spec.Sm4
open VG.Impl.Sm4 (Lin)

/-- A round in place: word `a` becomes `x_a ⊕ T(x_{a+1} ⊕ x_{a+2} ⊕ x_{a+3} ⊕ rk)`. -/
def sround (l : Lin) (rk : Word) (a : Nat) (x : Nat → Word) : Nat → Word := fun w =>
  if w = a then x a ^^^ l.t (x ((a + 1) % 4) ^^^ x ((a + 2) % 4) ^^^ x ((a + 3) % 4) ^^^ rk) else x w

/-- Rounds `4 m … 4 m + 3`. -/
def quad (l : Lin) (K : Nat → Word) (m : Nat) (x : Nat → Word) : Nat → Word :=
  sround l (K (4 * m + 3)) 3 (sround l (K (4 * m + 2)) 2 (sround l (K (4 * m + 1)) 1 (sround l (K (4 * m)) 0 x)))

/-- The first `n` groups of four rounds. -/
def quads (l : Lin) (K : Nat → Word) : Nat → (Nat → Word) → Nat → Word
  | 0, x => x
  | n + 1, x => quad l K n (quads l K n x)

/-- The words of a state. -/
def tup (x : Nat → Word) : State := (x 0, x 1, x 2, x 3)

/-- Four rounds of the specification are a `quad`. -/
theorem round4_eq (K : Nat → Word) (m : Nat) (x : Nat → Word) :
    round (K (4 * m + 3)) (round (K (4 * m + 2)) (round (K (4 * m + 1)) (round (K (4 * m)) (tup x)))) =
      tup (quad .enc K m x) := by
  simp only [round, tup, quad, sround, Lin.t_enc]
  simp

theorem range_four (n : Nat) : List.range (4 * (n + 1)) = List.range (4 * n) ++ [4 * n, 4 * n + 1, 4 * n + 2, 4 * n + 3] := by
  rw [show 4 * (n + 1) = 4 * n + 3 + 1 by omega, List.range_succ, show 4 * n + 3 = 4 * n + 2 + 1 by omega,
    List.range_succ, show 4 * n + 2 = 4 * n + 1 + 1 by omega, List.range_succ, List.range_succ]
  simp

theorem foldl_rounds (K : Nat → Word) (x : Nat → Word) (n : Nat) :
    (List.range (4 * n)).foldl (fun s i => round (K i) s) (tup x) = tup (quads .enc K n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [range_four, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, quads]
    exact round4_eq K n _

/-- The words of a block. -/
def ofBlock (b : Block) : Nat → Word := fun w => wordAt b (4 * w)

/-- The output block of the final words `z`: `R(z) = (z 3, z 2, z 1, z 0)`. -/
def outBlock (z : Nat → Word) : Block :=
  Vector.ofFn fun i => ((#v[z 3, z 2, z 1, z 0] : Vector Word 4).getD (i.val / 4) 0 >>> (8 * (3 - i.val % 4))).setWidth 8

theorem crypt_eq (K : Nat → Word) (b : Block) : crypt K b = outBlock (quads .enc K 8 (ofBlock b)) := by
  have h : (List.range 32).foldl (fun s i => round (K i) s) (tup (ofBlock b)) = tup (quads .enc K 8 (ofBlock b)) :=
    foldl_rounds K (ofBlock b) 8
  have hi : initial b = tup (ofBlock b) := rfl
  unfold crypt
  rw [hi, h]
  rfl

/-! ## The key schedule -/

/-- A round of the key schedule on the state, as `expandKey` runs it. -/
def kround (rk : Word) (s : State) : State :=
  let (a, b, c, d) := s
  (b, c, d, a ^^^ keyT (b ^^^ c ^^^ d ^^^ rk))

theorem kround4_eq (K : Nat → Word) (m : Nat) (x : Nat → Word) :
    kround (K (4 * m + 3)) (kround (K (4 * m + 2)) (kround (K (4 * m + 1)) (kround (K (4 * m)) (tup x)))) =
      tup (quad .key K m x) := by
  simp only [kround, tup, quad, sround, Lin.t_key]
  simp

/-- `MK ⊕ FK`. -/
def keyInit (key : Block) : Nat → Word := fun w => wordAt key (4 * w) ^^^ fk.getD w 0

/-- Round key `i`: word `i mod 4` after `⌊i / 4⌋ + 1` groups. -/
def rkOf (key : Block) (i : Nat) : Word := quads .key ck (i / 4 + 1) (keyInit key) (i % 4)

/-- The loop of `expandKey`, as a fold. -/
def ekStep (b : State × Vector Word 32) (a : Nat) : State × Vector Word 32 :=
  ((b.1.2.1, b.1.2.2.1, b.1.2.2.2, b.1.1 ^^^ keyT (b.1.2.1 ^^^ b.1.2.2.1 ^^^ b.1.2.2.2 ^^^ ck a)),
    b.2.set! a (b.1.1 ^^^ keyT (b.1.2.1 ^^^ b.1.2.2.1 ^^^ b.1.2.2.2 ^^^ ck a)))

theorem ekStep_fst (b : State × Vector Word 32) (a : Nat) : (ekStep b a).1 = kround (ck a) b.1 := rfl

theorem foldl_ek (key : Block) (n : Nat) (hn : n ≤ 8) :
    ((List.range (4 * n)).foldl ekStep (tup (keyInit key), Vector.replicate 32 0)).1 =
      tup (quads .key ck n (keyInit key)) ∧
    ∀ i (h : i < 32), ((List.range (4 * n)).foldl ekStep (tup (keyInit key), Vector.replicate 32 0)).2[i] =
      if i < 4 * n then rkOf key i else 0 := by
  induction n with
  | zero => exact ⟨rfl, fun i h => by simp⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    rw [range_four, List.foldl_append]
    generalize hB : (List.range (4 * n)).foldl ekStep (tup (keyInit key), Vector.replicate 32 0) = B at h1 h2
    simp only [List.foldl_cons, List.foldl_nil]
    refine ⟨?_, fun i h => ?_⟩
    · simp only [ekStep_fst, h1, quads]
      exact kround4_eq ck n _
    · have hq : quads .key ck (n + 1) (keyInit key) = quad .key ck n (quads .key ck n (keyInit key)) := rfl
      have hk := kround4_eq ck n (quads .key ck n (keyInit key))
      rw [← hq, ← h1] at hk
      simp only [ekStep, Vector.getElem_set! h, h2 i h]
      simp only [kround, tup] at hk
      simp only [Prod.mk.injEq] at hk
      obtain ⟨k0, k1, k2, k3⟩ := hk
      have hr : ∀ r < 4, rkOf key (4 * n + r) = quads .key ck (n + 1) (keyInit key) r := fun r hr => by
        simp only [rkOf, show (4 * n + r) / 4 + 1 = n + 1 by omega, show (4 * n + r) % 4 = r by omega]
      have l3 : 4 * n + 3 < 4 * (n + 1) := by omega
      have l2 : 4 * n + 2 < 4 * (n + 1) := by omega
      have l1 : 4 * n + 1 < 4 * (n + 1) := by omega
      have l0 : 4 * n < 4 * (n + 1) := by omega
      have r0 := hr 0 (by omega)
      simp only [Nat.add_zero] at r0
      by_cases h3 : 4 * n + 3 = i
      · subst h3; simp only [↓reduceIte, l3, hr 3 (by omega), ← k3]
      by_cases h2' : 4 * n + 2 = i
      · subst h2'; simp only [h3, ↓reduceIte, l2, hr 2 (by omega), ← k2]
      by_cases h1' : 4 * n + 1 = i
      · subst h1'; simp only [h3, h2', ↓reduceIte, l1, hr 1 (by omega), ← k1]
      by_cases h0 : 4 * n = i
      · subst h0; simp only [h3, h2', h1', ↓reduceIte, l0, r0, ← k0]
      · simp only [h3, h2', h1', h0, ↓reduceIte]
        by_cases hi : i < 4 * n
        · simp only [hi, ↓reduceIte, show i < 4 * (n + 1) by omega]
        · simp only [hi, ↓reduceIte, show ¬ i < 4 * (n + 1) by omega]

theorem expandKey_eq (key : Block) : expandKey key = Vector.ofFn fun i => rkOf key i.val := by
  have h := (foldl_ek key 8 (by decide)).2
  unfold expandKey
  simp only [Id.run, List.forIn_pure_yield_eq_foldl, pure_bind]
  apply Vector.ext
  intro i hi
  have := h i hi
  simp only [show 4 * 8 = 32 from rfl, hi, ↓reduceIte] at this
  rw [Vector.getElem_ofFn, ← this]
  rfl

end VG.Proof.Sm4
