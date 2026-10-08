import VerifiedGarbage.Proof.Seed.Rounds

/-!
# The key schedule, as `G` of 32 inputs

`expandKey_eq`: RFC 4269 §2.3's key schedule (`Spec.Seed.expandKey`) is `G`
of 32 inputs (`gInput`), the key words of each round (`keyWords`) added and
subtracted with its constant: none depends on an output of `G`.
-/

namespace VG.Proof.Seed
open VG.Spec.Seed

/-- The rotation after round `j + 1`. -/
def keyStep (j : Nat) (k : Quad) : Quad :=
  if j % 2 = 0 then
    ((k.1 ++ k.2.1).rotateRight 8 |>.extractLsb' 32 32, (k.1 ++ k.2.1).rotateRight 8 |>.setWidth 32,
      k.2.2.1, k.2.2.2)
  else
    (k.1, k.2.1, (k.2.2.1 ++ k.2.2.2).rotateLeft 8 |>.extractLsb' 32 32,
      (k.2.2.1 ++ k.2.2.2).rotateLeft 8 |>.setWidth 32)

/-- The key words in round `j + 1`. -/
def keyWords (key : Block) : Nat → Quad
  | 0 => (wordAt key 0, wordAt key 4, wordAt key 8, wordAt key 12)
  | j + 1 => keyStep j (keyWords key j)

/-- Input `i` of `G` in the key schedule. -/
def gInput (key : Block) (i : Nat) : Word :=
  let k := keyWords key (i / 2)
  if i % 2 = 0 then k.1 + k.2.2.1 - kc.getD (i / 2) 0 else k.2.1 - k.2.2.2 + kc.getD (i / 2) 0

theorem forIn_ite_yield {α β : Type} (l : List α) (init : β) (c : α → Prop) [DecidablePred c]
    (f g : α → β → β) :
    forIn (m := Id) l init (fun a b => if c a then pure (.yield (f a b)) else pure (.yield (g a b))) =
      pure (l.foldl (fun b a => if c a then f a b else g a b) init) := by
  rw [show (fun a b => if c a then (pure (.yield (f a b)) : Id (ForInStep β)) else pure (.yield (g a b))) =
    fun a b => pure (.yield (if c a then f a b else g a b)) from by
      funext a b; split <;> rfl]
  exact List.forIn_pure_yield_eq_foldl ..

/-- One iteration of `expandKey`'s loop. -/
def keyBody (b : Word × Word × Word × Word × Schedule) (a : Nat) : Word × Word × Word × Word × Schedule :=
  if a % 2 = 0 then
    (BitVec.extractLsb' 32 32 ((b.1 ++ b.2.1).rotateRight 8), BitVec.setWidth 32 ((b.1 ++ b.2.1).rotateRight 8),
      b.2.2.1, b.2.2.2.1,
      (Vector.set! b.2.2.2.2 (2 * a) (g (b.1 + b.2.2.1 - kc.getD a 0))).set! (2 * a + 1)
        (g (b.2.1 - b.2.2.2.1 + kc.getD a 0)))
  else
    (b.1, b.2.1, BitVec.extractLsb' 32 32 ((b.2.2.1 ++ b.2.2.2.1).rotateLeft 8),
      BitVec.setWidth 32 ((b.2.2.1 ++ b.2.2.2.1).rotateLeft 8),
      (Vector.set! b.2.2.2.2 (2 * a) (g (b.1 + b.2.2.1 - kc.getD a 0))).set! (2 * a + 1)
        (g (b.2.1 - b.2.2.2.1 + kc.getD a 0)))

/-- The schedule after `n` rounds. -/
def partialKeys (key : Block) (n : Nat) : Schedule :=
  Vector.ofFn fun i => if i.val < 2 * n then g (gInput key i.val) else 0

theorem keyBody_fold (key : Block) : ∀ n, n ≤ 16 →
    (List.range n).foldl keyBody (wordAt key 0, wordAt key 4, wordAt key 8, wordAt key 12, Vector.replicate 32 0) =
      ((keyWords key n).1, (keyWords key n).2.1, (keyWords key n).2.2.1, (keyWords key n).2.2.2,
        partialKeys key n)
  | 0, _ => by
    simp only [List.range_zero, List.foldl_nil, keyWords, partialKeys, Nat.mul_zero, Nat.not_lt_zero,
      ite_false]
    rfl
  | n + 1, hn => by
    rw [List.range_succ, List.foldl_append, keyBody_fold key n (by omega), List.foldl_cons, List.foldl_nil]
    have hk : ∀ i (hi : i < 32), (((partialKeys key n).set! (2 * n) (g (gInput key (2 * n)))).set! (2 * n + 1)
        (g (gInput key (2 * n + 1))) : Vector Word 32)[i] = (partialKeys key (n + 1))[i] := by
      intro i hi
      rw [Vector.getElem_set! hi, Vector.getElem_set! hi]
      simp only [partialKeys, Vector.getElem_ofFn]
      split
      · subst i; simp only [show 2 * n + 1 < 2 * (n + 1) by omega, ite_true]
      · split
        · subst i; simp only [show 2 * n < 2 * (n + 1) by omega, ite_true]
        · rename_i h1 h2
          by_cases hlt : i < 2 * n
          · rw [ite_eq_left_iff.mpr (fun h => absurd hlt h), ite_eq_left_iff.mpr (fun h => by omega)]
          · rw [ite_eq_right_iff.mpr (fun h => absurd h hlt), ite_eq_right_iff.mpr (fun h => by omega)]
    have g0 : gInput key (2 * n) = (keyWords key n).1 + (keyWords key n).2.2.1 - kc.getD n 0 := by
      simp only [gInput, show 2 * n / 2 = n by omega, show 2 * n % 2 = 0 by omega, ite_true]
    have g1 : gInput key (2 * n + 1) = (keyWords key n).2.1 - (keyWords key n).2.2.2 + kc.getD n 0 := by
      simp only [gInput, show (2 * n + 1) / 2 = n by omega, show (2 * n + 1) % 2 = 1 by omega]
      rfl
    have hpk : ((partialKeys key n).set! (2 * n) (g ((keyWords key n).1 + (keyWords key n).2.2.1 - kc.getD n 0))).set!
        (2 * n + 1) (g ((keyWords key n).2.1 - (keyWords key n).2.2.2 + kc.getD n 0)) = partialKeys key (n + 1) := by
      rw [← g0, ← g1]; exact Vector.ext hk
    unfold keyBody
    simp only [keyWords, keyStep]
    split <;> simp only [hpk]

theorem expandKey_eq (key : Block) : expandKey key = Vector.ofFn fun i => g (gInput key i.val) := by
  have h : expandKey key = ((List.range 16).foldl keyBody
      (wordAt key 0, wordAt key 4, wordAt key 8, wordAt key 12, Vector.replicate 32 0)).2.2.2.2 := by
    simp only [expandKey, Id.run]
    rw [forIn_ite_yield]
    simp only [pure_bind]
    have hf : (fun (b : Word × Word × Word × Word × Schedule) (a : Nat) =>
        if a % 2 = 0 then
          (BitVec.extractLsb' 32 32 ((b.1 ++ b.2.1).rotateRight 8), BitVec.setWidth 32 ((b.1 ++ b.2.1).rotateRight 8),
            b.2.2.1, b.2.2.2.1,
            (Vector.set! b.2.2.2.2 (2 * a) (g (b.1 + b.2.2.1 - kc.getD a 0))).set! (2 * a + 1)
              (g (b.2.1 - b.2.2.2.1 + kc.getD a 0)))
        else
          (b.1, b.2.1, BitVec.extractLsb' 32 32 ((b.2.2.1 ++ b.2.2.2.1).rotateLeft 8),
            BitVec.setWidth 32 ((b.2.2.1 ++ b.2.2.2.1).rotateLeft 8),
            (Vector.set! b.2.2.2.2 (2 * a) (g (b.1 + b.2.2.1 - kc.getD a 0))).set! (2 * a + 1)
              (g (b.2.1 - b.2.2.2.1 + kc.getD a 0)))) = keyBody := rfl
    rw [hf]
    rfl
  rw [h, keyBody_fold key 16 (by decide)]
  apply Vector.ext
  intro i hi
  simp only [partialKeys, Vector.getElem_ofFn, show i < 2 * 16 by omega, ite_true]

end VG.Proof.Seed
