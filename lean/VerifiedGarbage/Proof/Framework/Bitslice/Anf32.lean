module

public import VerifiedGarbage.Proof.Framework.Bitslice.Anf
import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The ANF domain, for 32-bit words

The ANF domain (`Bitslice.Anf`) is of 64-bit words. A 32-bit word written
twice (`dbl x = x ++ x`) is a 64-bit word whose bitwise operations and
rotations are those of the 32-bit word, written twice (`dbl_xor`,
`dbl_ror`): so the same polynomials evaluate code on 32-bit words, an
abstract word standing for the 32-bit word `x` when it evaluates to `dbl x`
on the atoms written twice (`Anf32Rel`). A word written twice is the same
rotated by 32, so the rotations keep their counts below 32, and sort again
what they rotated (`pror32`): two programs that compute the same polynomial
in the same linear forms then get the same `Poly`, whenever they rotate.
-/

@[expose] public section

namespace VG.Bitslice.Anf

/-- A 32-bit word, twice. -/
def dbl (x : BitVec 32) : W := x ++ x

theorem getLsbD_dbl (x : BitVec 32) {i : Nat} (hi : i < 64) : (dbl x).getLsbD i = x.getLsbD (i % 32) := by
  have e : (x ++ x : BitVec (32 + 32)).getLsbD i = if i < 32 then x.getLsbD i else x.getLsbD (i - 32) :=
    BitVec.getLsbD_append
  rw [dbl, e]
  split
  · rename_i h; rw [Nat.mod_eq_of_lt h]
  · rename_i h; rw [show i % 32 = i - 32 by omega_using [h, hi]]

theorem dbl_xor (x y : BitVec 32) : dbl (x ^^^ y) = dbl x ^^^ dbl y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_xor, getLsbD_dbl _ hi]

theorem dbl_and (x y : BitVec 32) : dbl (x &&& y) = dbl x &&& dbl y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, getLsbD_dbl _ hi]

theorem dbl_or (x y : BitVec 32) : dbl (x ||| y) = dbl x ||| dbl y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_or, getLsbD_dbl _ hi]

theorem dbl_zero : dbl 0 = 0 := by decide

theorem dbl_ones : dbl (BitVec.allOnes 32) = BitVec.allOnes 64 := by decide

theorem dbl_ror (x : BitVec 32) (n : Nat) : dbl (x.rotateRight n) = (dbl x).rotateRight n := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have h64 : (i + n) % 64 < 64 := Nat.mod_lt _ (by decide)
  rw [getLsbD_dbl _ hi, getLsbD_rotateRight_lt _ _ _ hi, getLsbD_dbl _ h64,
    getLsbD_rotateRight_lt _ _ _ (Nat.mod_lt _ (by decide))]
  congr 1
  omega_using []

theorem dbl_inj {x y : BitVec 32} (h : dbl x = dbl y) : x = y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have := congrArg (·.getLsbD i) h
  simp only [getLsbD_dbl _ (show i < 64 by omega_using [hi]), Nat.mod_eq_of_lt hi] at this
  exact this

/-- A word written twice is rotated as by the count modulo 32. -/
theorem dbl_ror_mod (x : BitVec 32) (n : Nat) : (dbl x).rotateRight (n % 32) = (dbl x).rotateRight n := by
  rw [← dbl_ror, ← dbl_ror]
  refine congrArg dbl ?_
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_rotateRight_lt _ _ _ hi, getLsbD_rotateRight_lt _ _ _ hi, Nat.add_mod_mod]

/-! ## Rotations with counts below 32 -/

/-- Rotate each key right by `n`, modulo 32, and sort the keys again: a
linear form with two keys of the same atom may not stay sorted. -/
def linRor32 (n : Nat) (l : List Nat) : List Nat :=
  (l.map fun k => k / 64 * 64 + (k % 64 + n) % 32).foldr keyIns []

/-- Rotate each linear form of a monomial, and sort them again. -/
def monoRor32 (n : Nat) (m : List (List Nat)) : List (List Nat) := (m.map (linRor32 n)).foldr atomIns []

def pror32 (n : Nat) (p : Poly) : Poly :=
  ⟨linRor32 n p.lin, p.c, (p.nl.map (monoRor32 n)).foldr monoIns []⟩

/-- The ANF domain, for 32-bit words. -/
def anf32 : Dom Poly 32 where
  xor a b := some (pxor a b)
  and a b := some (pand a b)
  or a b := some (por a b)
  ror n a := some (pror32 n a)
  shr _ _ := none
  const v := if v = 0 then some zero else if v = BitVec.allOnes 32 then some one else none

section
variable (V : Nat → BitVec 32)

/-- The atoms, each written twice. -/
def dblV : Nat → W := fun a => dbl (V a)

theorem key_ror32 (k n : Nat) :
    key (dblV V) (k / 64 * 64 + (k % 64 + n) % 32) = (key (dblV V) k).rotateRight n := by
  have h1 : (k / 64 * 64 + (k % 64 + n) % 32) / 64 = k / 64 := by omega_using []
  have h2 : (k / 64 * 64 + (k % 64 + n) % 32) % 64 = (k % 64 + n) % 32 := by omega_using []
  simp only [key, h1, h2, rotateRight_rotateRight, dblV]
  rw [dbl_ror_mod, ← dbl_ror_mod _ ((k % 64 + n) % 64), Nat.mod_mod_of_dvd _ (by decide : 32 ∣ 64),
    dbl_ror_mod]

theorem lin_linRor32 (n : Nat) (l : List Nat) :
    lin (dblV V) (linRor32 n l) = (lin (dblV V) l).rotateRight n := by
  induction l with
  | nil => simp only [linRor32, lin, List.map_nil, List.foldr_nil]; exact (rotateRight_zero' n).symm
  | cons k l ih =>
    simp only [linRor32, List.map_cons, List.foldr_cons] at ih ⊢
    rw [lin_keyIns, ih, key_ror32]
    simp only [lin, List.foldr_cons, rotateRight_xor]

theorem mono_ror32 (n : Nat) (m : List (List Nat)) :
    mono (dblV V) (monoRor32 n m) = (mono (dblV V) m).rotateRight n := by
  induction m with
  | nil => simp only [monoRor32, mono, List.map_nil, List.foldr_nil, ones_ror]
  | cons a m ih =>
    simp only [monoRor32, List.map_cons, List.foldr_cons] at ih ⊢
    rw [mono_atomIns, ih, lin_linRor32]
    simp only [mono, List.foldr_cons, rotateRight_and]

theorem monos_ror32 (n : Nat) (ns : List (List (List Nat))) :
    monos (dblV V) ((ns.map (monoRor32 n)).foldr monoIns []) = (monos (dblV V) ns).rotateRight n := by
  induction ns with
  | nil => simp [monos, rotateRight_zero']
  | cons m ns ih =>
    simp only [List.map_cons, List.foldr_cons] at ih ⊢
    rw [monos_monoIns, ih, mono_ror32]
    simp only [monos, List.foldr_cons, rotateRight_xor]

theorem eval_pror32 (n : Nat) (p : Poly) : eval (dblV V) (pror32 n p) = (eval (dblV V) p).rotateRight n := by
  simp only [eval, pror32, lin_linRor32, monos_ror32, rotateRight_xor, cst_ror]

/-- `Poly` stands for the 32-bit word that, written twice, it evaluates to
on the atoms written twice. -/
def Anf32Rel (p : Poly) (x : BitVec 32) : Prop := eval (dblV V) p = dbl x

theorem Anf32Rel.unique {p : Poly} {x y : BitVec 32} (h₁ : Anf32Rel V p x) (h₂ : Anf32Rel V p y) :
    x = y := dbl_inj (h₁.symm.trans h₂)

theorem anf32Rel_atom (a : Nat) : Anf32Rel V (atom a) (V a) := eval_atom _ a

theorem anf32_sound : anf32.Sound (Anf32Rel V) where
  xor ha hb h := by
    simp only [anf32, Option.some.injEq] at h; subst h
    simp only [Anf32Rel] at *; rw [eval_pxor, ha, hb, dbl_xor]
  and ha hb h := by
    simp only [anf32, Option.some.injEq] at h; subst h
    simp only [Anf32Rel] at *; rw [eval_pand, ha, hb, dbl_and]
  or ha hb h := by
    simp only [anf32, Option.some.injEq] at h; subst h
    simp only [Anf32Rel] at *; rw [eval_por, ha, hb, dbl_or]
  ror ha h := by
    simp only [anf32, Option.some.injEq] at h; subst h
    simp only [Anf32Rel] at *; rw [eval_pror32, ha, dbl_ror]
  shr _ h := by cases h
  const {v c} h := by
    simp only [anf32] at h
    split at h
    · rename_i hv; cases h; subst hv
      simp only [Anf32Rel]; rw [eval_zero, dbl_zero]
    · split at h
      · rename_i hv; cases h; subst hv
        simp only [Anf32Rel]; rw [eval_one, dbl_ones]
      · cases h

end

end VG.Bitslice.Anf
