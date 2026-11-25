module

public import VerifiedGarbage.Impl.Aes.Arm.Linear
public import VerifiedGarbage.Proof.Aes.Arm.Sbox
public import VerifiedGarbage.Proof.Aes.InvRounds
public import VerifiedGarbage.Proof.Framework.Arm.Linear
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The layers of bitsliced AES on ARMv7

Two states in eight slices (`BsRel`): in form `f`, the byte of row `r` and
column `c` of state `b` is at position `8 r + 2 ((c + f r) mod 4) + b`. Nothing
is done for ShiftRows: of a state in form `f`, the same slices are the state
after ShiftRows in form `f + 1` (`bs_shiftRows`), and, of one in form `f + 1`,
the state after InvShiftRows in form `f`.

The linear layers' code is checked by evaluation over the lane domain, on the
input words' bits as atoms: every output bit is the XOR of input bits that
FIPS 197's formulas give (`mcWords`, `invMcWords`, as the slices and rows of
the bits XORed).

`{63}` added to every byte of a state goes through MixColumns and
InvMixColumns unchanged (`mix_add63`, `invMix_add63`).
-/

@[expose] public section

namespace VG.Proof.Aes.Arm

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.Aes.Arm
open VG.Proof.Aes (mulBits bitsXor mul0e_bit mul0b_bit mul0d_bit mul09_bit invMcWords getLsbD_xtimes)
open VG.Spec.Aes (sbox invSbox mul xtimes shiftRows invShiftRows addRoundKey roundKey)

theorem vget {α : Type} {n : Nat} (xs : Vector α n) {i : Nat} (h : i < n) (d : α) :
    xs.getD i d = xs[i] := by
  simp [Vector.getD, Array.getD, h]

theorem byteExt {x y : Byte} (h : ∀ j < 8, x.getLsbD j = y.getLsbD j) : x = y :=
  BitVec.eq_of_getLsbD_eq fun j hj => h j hj

/-! ## Forms -/

/-- The position of byte `i` (`r + 4 c`) of state `b` in form `f`. -/
def at_ (f b i : Nat) : Nat := 8 * (i % 4) + 2 * ((i / 4 + f * (i % 4)) % 4) + b

/-- The byte at position `x`. -/
def byteAt (f x : Nat) : Nat := x / 8 + 4 * ((x / 2 % 4 + 3 * f * (x / 8)) % 4)

/-- The byte `k` rows below byte `i`, in its column. -/
def down (i k : Nat) : Nat := (i % 4 + k) % 4 + 4 * (i / 4)

theorem down_lt {i k : Nat} (hi : i < 16) : down i k < 16 := by unfold down; omega_using [hi]

theorem at_lt {f b i : Nat} (hb : b < 2) : at_ f b i < 32 := by
  unfold at_
  have := Nat.mod_lt (i / 4 + f * (i % 4)) (show 0 < 4 by decide)
  omega_using [hb, this]

theorem at_mod (f b i : Nat) : at_ (f % 4) b i = at_ f b i := by
  simp only [at_]
  rw [Nat.add_mod, Nat.mod_mul_mod, ← Nat.add_mod]

theorem at_byteAt : ∀ f < 4, ∀ x < 32, at_ f (x % 2) (byteAt f x) = x ∧ byteAt f x < 16 := by decide

theorem byteAt_at : ∀ f < 4, ∀ b < 2, ∀ i < 16, byteAt f (at_ f b i) = i ∧ at_ f b i % 2 = b := by decide

/-- The states `S b` in the slices `Q`, in form `f`. -/
def BsRel (f : Nat) (Q : Nat → BitVec 32) (S : Nat → Spec.Aes.State) : Prop :=
  ∀ b < 2, ∀ i < 16, bsByte Q (at_ f b i) = (S b).getD i 0

theorem BsRel.mod {f : Nat} {Q : Nat → BitVec 32} {S : Nat → Spec.Aes.State} :
    BsRel (f % 4) Q S ↔ BsRel f Q S := by
  simp only [BsRel, at_mod]

theorem BsRel.congr {f : Nat} {Q Q' : Nat → BitVec 32} {S : Nat → Spec.Aes.State} (h : BsRel f Q S)
    (hq : ∀ j < 8, Q' j = Q j) : BsRel f Q' S := fun b hb i hi => by
  rw [← h b hb i hi]
  exact byteExt fun j hj => by rw [getLsbD_bsByte _ _ hj, getLsbD_bsByte _ _ hj, hq j hj]

theorem BsRel.of_eq {f : Nat} {Q : Nat → BitVec 32} {S T : Nat → Spec.Aes.State} (h : BsRel f Q S)
    (hs : ∀ b, S b = T b) : BsRel f Q T := by
  rw [← funext hs]; exact h

/-- `{63}` added to every byte. -/
def add63 (x : Spec.Aes.State) : Spec.Aes.State := x.map (· ^^^ 0x63)

theorem add63_getD (x : Spec.Aes.State) {i : Nat} (hi : i < 16) : (add63 x).getD i 0 = x.getD i 0 ^^^ 0x63 := by
  rw [vget _ hi, vget _ hi, add63, Vector.getElem_map]

/-! ## SubBytes and ShiftRows -/

theorem bs_subBytes {f : Nat} {P Q : Nat → BitVec 32} {S : Nat → Spec.Aes.State}
    (h : ∀ x < 32, bsByte P x = sbox (bsByte Q x) ^^^ 0x63) (hq : BsRel f Q S) :
    BsRel f P fun b => add63 (Spec.Aes.subBytes (S b)) := fun b hb i hi => by
  rw [h _ (at_lt hb), hq b hb i hi, add63_getD _ hi, vget _ hi, vget _ hi, Spec.Aes.subBytes, Vector.getElem_map]

theorem bs_invSubBytes {f : Nat} {P Q : Nat → BitVec 32} {S : Nat → Spec.Aes.State}
    (h : ∀ x < 32, bsByte P x = invSbox (bsByte Q x ^^^ 0x63)) (hq : BsRel f Q fun b => add63 (S b)) :
    BsRel f P fun b => Spec.Aes.invSubBytes (S b) := fun b hb i hi => by
  show _ = (Spec.Aes.invSubBytes (S b)).getD i 0
  rw [h _ (at_lt hb), hq b hb i hi, add63_getD _ hi, vget _ hi, vget _ hi, Spec.Aes.invSubBytes, Vector.getElem_map,
    BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem shiftRows_getD (x : Spec.Aes.State) {i : Nat} (hi : i < 16) :
    (shiftRows x).getD i 0 = x.getD (i % 4 + 4 * ((i / 4 + i % 4) % 4)) 0 := by
  rw [vget _ hi, shiftRows, Vector.getElem_ofFn]

theorem invShiftRows_getD (x : Spec.Aes.State) {i : Nat} (hi : i < 16) :
    (invShiftRows x).getD i 0 = x.getD (i % 4 + 4 * ((i / 4 + 4 - i % 4) % 4)) 0 := by
  rw [vget _ hi, invShiftRows, Vector.getElem_ofFn]

theorem bs_shiftRows {f : Nat} {Q : Nat → BitVec 32} {S : Nat → Spec.Aes.State} (h : BsRel f Q S) :
    BsRel (f + 1) Q fun b => shiftRows (S b) := fun b hb i hi => by
  rw [shiftRows_getD _ hi, ← h b hb _ (by omega_using [hi])]
  congr 1
  have e := Nat.succ_mul f (i % 4)
  simp only [at_]
  rw [Nat.succ_eq_add_one] at e
  rw [e]
  rw [show (i % 4 + 4 * ((i / 4 + i % 4) % 4)) % 4 = i % 4 by omega_using [],
    show (i % 4 + 4 * ((i / 4 + i % 4) % 4)) / 4 = (i / 4 + i % 4) % 4 by omega_using []]
  omega_using []

theorem bs_invShiftRows {f : Nat} {Q : Nat → BitVec 32} {S : Nat → Spec.Aes.State} (h : BsRel (f + 1) Q S) :
    BsRel f Q fun b => invShiftRows (S b) := fun b hb i hi => by
  rw [invShiftRows_getD _ hi, ← h b hb _ (by omega_using [hi])]
  congr 1
  have e := Nat.succ_mul f (i % 4)
  simp only [at_]
  rw [Nat.succ_eq_add_one] at e
  rw [show (i % 4 + 4 * ((i / 4 + 4 - i % 4) % 4)) % 4 = i % 4 by omega_using [],
    show (i % 4 + 4 * ((i / 4 + 4 - i % 4) % 4)) / 4 = (i / 4 + 4 - i % 4) % 4 by omega_using [], e]
  omega_using []

theorem add63_shiftRows (x : Spec.Aes.State) : shiftRows (add63 x) = add63 (shiftRows x) := by
  apply Vector.ext
  intro i hi
  rw [← vget _ hi 0, ← vget _ hi 0, shiftRows_getD _ hi, add63_getD _ (by omega_using [hi]), add63_getD _ hi,
    shiftRows_getD _ hi]

theorem add63_invShiftRows (x : Spec.Aes.State) : invShiftRows (add63 x) = add63 (invShiftRows x) := by
  apply Vector.ext
  intro i hi
  rw [← vget _ hi 0, ← vget _ hi 0, invShiftRows_getD _ hi, add63_getD _ (by omega_using [hi]), add63_getD _ hi,
    invShiftRows_getD _ hi]

/-! ## MixColumns and InvMixColumns, as sums of bits -/

/-- The sum of the bits that `g` gives for the slices and rows `ws`. -/
def wsum (g : Nat → Nat → Bool) (ws : List (Nat × Nat)) : Bool :=
  ws.foldr (fun t b => g t.1 t.2 ^^ b) false

theorem wsum_congr {g h : Nat → Nat → Bool} : ∀ {ws : List (Nat × Nat)},
    (∀ t ∈ ws, g t.1 t.2 = h t.1 t.2) → wsum g ws = wsum h ws
  | [], _ => rfl
  | t :: ws, hgh => by
    simp only [wsum, List.foldr_cons]
    rw [hgh t List.mem_cons_self]
    exact congrArg _ (wsum_congr fun u hu => hgh u (List.mem_cons_of_mem _ hu))

theorem wsum_xor (g h : Nat → Nat → Bool) : ∀ ws : List (Nat × Nat),
    wsum (fun j k => g j k ^^ h j k) ws = (wsum g ws ^^ wsum h ws)
  | [] => rfl
  | t :: ws => by
    have ih := wsum_xor g h ws
    simp only [wsum, List.foldr_cons] at ih ⊢
    rw [ih]
    cases g t.1 t.2 <;> cases h t.1 t.2 <;> simp

/-- Bit `j` of byte `i` of `F x` is the sum of the bits of `x` that `ws j`
gives as slices and rows below. -/
structure LinOn (ws : Nat → List (Nat × Nat)) (F : Spec.Aes.State → Spec.Aes.State) : Prop where
  bit : ∀ x, ∀ i < 16, ∀ j < 8, ((F x).getD i 0).getLsbD j =
    wsum (fun t k => (x.getD (down i k) 0).getLsbD t) (ws j)
  lt : ∀ j < 8, ∀ t ∈ ws j, t.1 < 8
  c63 : ∀ j < 8, wsum (fun t _ => (0x63 : Byte).getLsbD t) (ws j) = (0x63 : Byte).getLsbD j

theorem LinOn.add63 {ws : Nat → List (Nat × Nat)} {F : Spec.Aes.State → Spec.Aes.State} (hF : LinOn ws F)
    (x : Spec.Aes.State) : F (add63 x) = Arm.add63 (F x) := by
  apply Vector.ext
  intro i hi
  rw [← vget _ hi 0, ← vget _ hi 0, add63_getD _ hi]
  refine byteExt fun j hj => ?_
  rw [BitVec.getLsbD_xor, hF.bit _ i hi j hj, hF.bit _ i hi j hj, ← hF.c63 j hj, ← wsum_xor]
  exact wsum_congr fun t _ => by rw [add63_getD _ (down_lt hi), BitVec.getLsbD_xor]

/-- The bits of `{02} • a` that bit `j` sums. -/
def twoBits (j : Nat) : List Nat :=
  (if j = 0 then [] else [j - 1]) ++ (if j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 4 then [7] else [])

/-- MixColumns' slice `j`. -/
def mcWords (j : Nat) : List (Nat × Nat) :=
  (twoBits j).map (·, 0) ++ (twoBits j ++ [j]).map (·, 1) ++ [(j, 2), (j, 3)]

theorem mul02 (a : Byte) : mul 0x02 a = xtimes a := by
  simp [mul, List.range, List.range.loop, Nat.repeat]

theorem mul03 (a : Byte) : mul 0x03 a = a ^^^ xtimes a := by
  simp [mul, List.range, List.range.loop, Nat.repeat]

theorem wsum_append (g : Nat → Nat → Bool) (a b : List (Nat × Nat)) :
    wsum g (a ++ b) = (wsum g a ^^ wsum g b) := by
  induction a with
  | nil => simp [wsum]
  | cons t a ih =>
    simp only [wsum, List.cons_append, List.foldr_cons] at ih ⊢
    rw [ih, Bool.xor_assoc]

theorem wsum_row (g : Nat → Nat → Bool) (k : Nat) (ts : List Nat) :
    wsum g (ts.map (·, k)) = ts.foldr (fun t b => g t k ^^ b) false := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [wsum, List.map_cons, List.foldr_cons] at ih ⊢
    rw [ih]

theorem xtimes_bit (a : Byte) : ∀ j < 8, (xtimes a).getLsbD j = bitsXor a (twoBits j) := by
  intro j hj
  rw [getLsbD_xtimes _ hj]
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;>
    first | omega_using [hj] | simp [bitsXor, twoBits] | skip

theorem mc_lin : LinOn mcWords Spec.Aes.mixColumns where
  bit x i hi j hj := by
    have e : ∀ k, x.getD ((i % 4 + k) % 4 + 4 * (i / 4)) 0 = x.getD (down i k) 0 := fun _ => rfl
    rw [vget _ hi, Spec.Aes.mixColumns, Vector.getElem_ofFn]
    simp only [e, mul02, mul03, BitVec.getLsbD_xor, xtimes_bit _ j hj]
    rw [mcWords, wsum_append, wsum_append, wsum_row, wsum_row, List.foldr_append]
    simp only [wsum, List.foldr_cons, List.foldr_nil, Bool.xor_false, bitsXor]
    have ac : ∀ (a : Byte) (ts : List Nat) (c : Bool), ts.foldr (fun t b => a.getLsbD t ^^ b) c =
        (c ^^ ts.foldr (fun t b => a.getLsbD t ^^ b) false) := by
      intro a ts c
      induction ts with
      | nil => simp
      | cons t ts ih => simp only [List.foldr_cons, ih]; cases a.getLsbD t <;> cases c <;> simp
    rw [ac _ _ ((x.getD (down i 1) 0).getLsbD j)]
    simp only [Bool.xor_assoc]
  lt := by decide
  c63 := by decide

theorem invMc_lin : LinOn invMcWords Spec.Aes.invMixColumns where
  bit x i hi j hj := by
    have e : ∀ k, x.getD ((i % 4 + k) % 4 + 4 * (i / 4)) 0 = x.getD (down i k) 0 := fun _ => rfl
    rw [vget _ hi, Spec.Aes.invMixColumns, Vector.getElem_ofFn]
    simp only [e, BitVec.getLsbD_xor, mul0e_bit _ hj, mul0b_bit _ hj, mul0d_bit _ hj, mul09_bit _ hj]
    simp only [invMcWords, List.flatMap_cons, List.flatMap_nil, List.append_nil, wsum_append, wsum_row, bitsXor,
      Bool.xor_assoc]
  lt := by decide
  c63 := by decide

/-- The output bits of a linear layer of form `f` with the sums `ws`, as bits
of the input words. -/
def linG (f : Nat) (ws : Nat → List (Nat × Nat)) (j x : Nat) : List Nat :=
  (ws j).map fun t => 32 * t.1 + at_ f (x % 2) (down (byteAt f x) t.2)

theorem xorBits_linG (W : Nat → BitVec 32) (f : Nat) (ws : List (Nat × Nat)) (x : Nat) :
    Straight.xorBits W (ws.map fun t => 32 * t.1 + at_ f (x % 2) (down (byteAt f x) t.2)) =
      wsum (fun t k => (W t).getLsbD (at_ f (x % 2) (down (byteAt f x) k))) ws := by
  induction ws with
  | nil => rfl
  | cons t ws ih =>
    simp only [List.map_cons, Straight.xorBits_cons, wsum, List.foldr_cons] at ih ⊢
    rw [ih, Straight.bitOf_word _ _ _ (at_lt (Nat.mod_lt _ (by decide)))]

theorem bs_linear {f : Nat} (hf : f < 4) {ws : Nat → List (Nat × Nat)} {F : Spec.Aes.State → Spec.Aes.State}
    (hF : LinOn ws F) {P Q : Nat → BitVec 32} {S : Nat → Spec.Aes.State}
    (h : ∀ j < 8, ∀ x < 32, (Q j).getLsbD x = Straight.xorBits P (linG f ws j x)) (hp : BsRel f P S) :
    BsRel f Q fun b => F (S b) := fun b hb i hi => by
  refine byteExt fun j hj => ?_
  obtain ⟨e1, e2⟩ := byteAt_at f hf b hb i hi
  rw [getLsbD_bsByte _ _ hj, h j hj _ (at_lt hb), linG, xorBits_linG, e1, e2, hF.bit _ i hi j hj]
  refine wsum_congr fun t ht => ?_
  rw [← hp b hb _ (down_lt hi), getLsbD_bsByte _ _ (hF.lt j hj t ht)]

theorem mix_add63 (x : Spec.Aes.State) : Spec.Aes.mixColumns (add63 x) = add63 (Spec.Aes.mixColumns x) := mc_lin.add63 x
theorem invMix_add63 (x : Spec.Aes.State) : Spec.Aes.invMixColumns (add63 x) = add63 (Spec.Aes.invMixColumns x) := invMc_lin.add63 x

/-! ## AddRoundKey -/

/-- A round key's slices, in both blocks' places: the bytes `v i`. -/
def KeyRel (f : Nat) (K : Nat → BitVec 32) (v : Nat → Byte) : Prop :=
  ∀ b < 2, ∀ i < 16, bsByte K (at_ f b i) = v i

theorem keyRel_congr {f : Nat} {K K' : Nat → BitVec 32} {v : Nat → Byte} (h : KeyRel f K v)
    (he : ∀ k < 8, K' k = K k) : KeyRel f K' v := fun b hb i hi => by
  rw [← h b hb i hi]
  exact byteExt fun j hj => by rw [getLsbD_bsByte _ _ hj, getLsbD_bsByte _ _ hj, he j hj]

/-- The bytes of round key `j` as it is stored, `{63}` added but for the first. -/
def rkByte (w : List Byte) (j i : Nat) : Byte := (roundKey w j).getD i 0 ^^^ (if j = 0 then 0 else 0x63)

theorem addRoundKey_getD (x : Spec.Aes.State) (rk : List Byte) {i : Nat} (hi : i < 16) :
    (addRoundKey x rk).getD i 0 = x.getD i 0 ^^^ rk.getD i 0 := by
  rw [vget _ hi, addRoundKey, Vector.getElem_ofFn]

theorem bs_ark {f : Nat} {P Q K : Nat → BitVec 32} {S : Nat → Spec.Aes.State} {v : Nat → Byte}
    (h : ∀ j < 8, ∀ x < 32, (Q j).getLsbD x = ((P j).getLsbD x ^^ (K j).getLsbD x)) (hp : BsRel f P S)
    (hk : KeyRel f K v) {T : Nat → Spec.Aes.State}
    (hT : ∀ b < 2, ∀ i < 16, (T b).getD i 0 = (S b).getD i 0 ^^^ v i) : BsRel f Q T := fun b hb i hi => by
  rw [hT b hb i hi, ← hp b hb i hi, ← hk b hb i hi]
  refine byteExt fun j hj => ?_
  rw [BitVec.getLsbD_xor, getLsbD_bsByte _ _ hj, getLsbD_bsByte _ _ hj, getLsbD_bsByte _ _ hj, h j hj _ (at_lt hb)]

/-- The first round key, with no `{63}`. -/
theorem ark_first {x : Spec.Aes.State} {w : List Byte} {i : Nat} (hi : i < 16) :
    (addRoundKey x (roundKey w 0)).getD i 0 = x.getD i 0 ^^^ rkByte w 0 i := by
  rw [addRoundKey_getD _ _ hi, rkByte]; simp

/-- The others, of a state with `{63}` added. -/
theorem ark_next {x : Spec.Aes.State} {w : List Byte} {j i : Nat} (hj : j ≠ 0) (hi : i < 16) :
    (addRoundKey x (roundKey w j)).getD i 0 = (add63 x).getD i 0 ^^^ rkByte w j i := by
  rw [addRoundKey_getD _ _ hi, rkByte, add63_getD _ hi, ite_eq_right hj]
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  simp only [BitVec.getLsbD_xor]
  cases (x.getD i 0).getLsbD t <;> cases ((roundKey w j).getD i 0).getLsbD t <;>
    cases (0x63 : Byte).getLsbD t <;> rfl

/-- The others, adding `{63}`. -/
theorem ark_add63 {x : Spec.Aes.State} {w : List Byte} {j i : Nat} (hj : j ≠ 0) (hi : i < 16) :
    (add63 (addRoundKey x (roundKey w j))).getD i 0 = x.getD i 0 ^^^ rkByte w j i := by
  rw [add63_getD _ hi, addRoundKey_getD _ _ hi, rkByte, ite_eq_right hj, BitVec.xor_assoc]

/-! ## Blocks' words -/

/-- The states `S b` in the words `W (2 c + b)` as in form `f` of the slices:
byte `i` is byte `r` of word `c + f r`. -/
def WRel (f : Nat) (W : Nat → BitVec 32) (S : Nat → Spec.Aes.State) : Prop :=
  ∀ b < 2, ∀ i < 16, ∀ j < 8,
    (W (2 * ((i / 4 + f * (i % 4)) % 4) + b)).getLsbD (8 * (i % 4) + j) = ((S b).getD i 0).getLsbD j

/-- The states `S b` in the words `W (2 c + b)`. -/
def InRel (W : Nat → BitVec 32) (S : Nat → Spec.Aes.State) : Prop :=
  ∀ b < 2, ∀ i < 16, ∀ j < 8, (W (2 * (i / 4) + b)).getLsbD (8 * (i % 4) + j) = ((S b).getD i 0).getLsbD j

theorem inRel_iff {W : Nat → BitVec 32} {S : Nat → Spec.Aes.State} : WRel 0 W S ↔ InRel W S := by
  have e : ∀ i < 16, (i / 4 + 0 * (i % 4)) % 4 = i / 4 := by decide
  constructor
  · intro h b hb i hi j hj
    have := h b hb i hi j hj
    rwa [e i hi] at this
  · intro h b hb i hi j hj
    rw [e i hi]; exact h b hb i hi j hj

/-- The transpose's bits. -/
def orthoG (j x : Nat) : List Nat := [32 * (x % 8) + (8 * (x / 8) + j)]

theorem bs_of_words {f : Nat} {Q W : Nat → BitVec 32} {S : Nat → Spec.Aes.State}
    (h : ∀ j < 8, ∀ x < 32, (Q j).getLsbD x = (W (x % 8)).getLsbD (8 * (x / 8) + j)) (hw : WRel f W S) :
    BsRel f Q S := fun b hb i hi => by
  refine byteExt fun j hj => ?_
  rw [getLsbD_bsByte _ _ hj, h j hj _ (at_lt hb), ← hw b hb i hi j hj]
  simp only [at_]
  generalize i / 4 + f * (i % 4) = m
  rw [show (8 * (i % 4) + 2 * (m % 4) + b) % 8 = 2 * (m % 4) + b by omega_using [hb],
    show (8 * (i % 4) + 2 * (m % 4) + b) / 8 = i % 4 by omega_using [hb]]

theorem words_of_bs {f : Nat} {Q W : Nat → BitVec 32} {S : Nat → Spec.Aes.State}
    (h : ∀ j < 8, ∀ x < 32, (W j).getLsbD x = (Q (x % 8)).getLsbD (8 * (x / 8) + j)) (hq : BsRel f Q S) :
    WRel f W S := fun b hb i hi j hj => by
  rw [← hq b hb i hi, getLsbD_bsByte _ _ hj, h _ (by omega_using [hb]) _ (by omega_using [hj])]
  simp only [at_]
  generalize i / 4 + f * (i % 4) = m
  rw [show (8 * (i % 4) + j) % 8 = j by omega_using [hj], show (8 * (i % 4) + j) / 8 = i % 4 by omega_using [hj],
    show 8 * (i % 4) + (2 * (m % 4) + b) = 8 * (i % 4) + 2 * (m % 4) + b by omega_using []]

/-- The exchange's bits: byte `r` of column `c` from column `c + 2 r`. -/
def sr2WordsG (k x : Nat) : List Nat := [32 * (2 * ((k / 2 + 2 * (x / 8)) % 4) + k % 2) + x]

theorem words_sr2 {f : Nat} {W W' : Nat → BitVec 32} {S : Nat → Spec.Aes.State}
    (h : ∀ k < 8, ∀ x < 32, (W' k).getLsbD x = (W (2 * ((k / 2 + 2 * (x / 8)) % 4) + k % 2)).getLsbD x)
    (hw : WRel f W S) : WRel (f + 2) W' S := fun b hb i hi j hj => by
  rw [← hw b hb i hi j hj, h _ (by omega_using [hb]) _ (by omega_using [hj]), Nat.add_mul]
  generalize f * (i % 4) = m
  rw [show (8 * (i % 4) + j) / 8 = i % 4 by omega_using [hj],
    show (2 * ((i / 4 + (m + 2 * (i % 4))) % 4) + b) / 2 = (i / 4 + (m + 2 * (i % 4))) % 4 by omega_using [hb],
    show (2 * ((i / 4 + (m + 2 * (i % 4))) % 4) + b) % 2 = b by omega_using [hb],
    show ((i / 4 + (m + 2 * (i % 4))) % 4 + 2 * (i % 4)) % 4 = (i / 4 + m) % 4 by omega_using []]

theorem WRel.mod {f : Nat} {W : Nat → BitVec 32} {S : Nat → Spec.Aes.State} :
    WRel (f % 4) W S ↔ WRel f W S := by
  have e : ∀ i, (i / 4 + f % 4 * (i % 4)) % 4 = (i / 4 + f * (i % 4)) % 4 := fun i => by
    rw [Nat.add_mod, Nat.mod_mul_mod, ← Nat.add_mod]
  simp only [WRel, e]

/-! ## The checks -/

/-- No memory. -/
def noMem : Cfg := { base := sb, slots := 0, ext := sb, exts := 0 }

theorem noMem_ok (s : State) : Ok noMem s where
  slotIn k hk := by simp [noMem] at hk
  extIn k hk := by simp [noMem] at hk
  slots := by simp only [noMem]; have := (s.gpr sb).isLt; omega_using [this]
  sep k hk := by simp [noMem] at hk

/-- The slices `r j` hold input words `j`. -/
def rIns (r : Nat → Reg) : List (Reg × Nat) := (List.range 8).map fun k => (r k, k)

/-- The outputs `r j`, bit `x` the XOR of the input bits `g j x`. -/
def rOuts (r : Nat → Reg) (g : Nat → Nat → List Nat) : List (Reg × (Nat → List Nat)) :=
  (List.range 8).map fun j => (r j, g j)

/-- The check of a linear layer from `a j` to `d j`. -/
def linCheck (is : List Instr) (a d : Nat → Reg) (g : Nat → Nat → List Nat) : Bool :=
  check (lanes 32 8) noMem (linExt 0) is (linEnv (rIns a)) (linPost 8 (rOuts d g))

theorem ortho_check : linCheck ortho q q orthoG = true := by decide +kernel
theorem sr2Words_check : linCheck sr2Words q q sr2WordsG = true := by decide +kernel
theorem mix0_check : linCheck (Impl.Aes.Arm.mixColumns 0) p q (linG 0 mcWords) = true := by decide +kernel
theorem mix1_check : linCheck (Impl.Aes.Arm.mixColumns 1) p q (linG 1 mcWords) = true := by decide +kernel
theorem mix2_check : linCheck (Impl.Aes.Arm.mixColumns 2) p q (linG 2 mcWords) = true := by decide +kernel
theorem mix3_check : linCheck (Impl.Aes.Arm.mixColumns 3) p q (linG 3 mcWords) = true := by decide +kernel
theorem inv0_check : linCheck (Impl.Aes.Arm.invMixColumns 0) p q (linG 0 invMcWords) = true := by decide +kernel
theorem inv1_check : linCheck (Impl.Aes.Arm.invMixColumns 1) p q (linG 1 invMcWords) = true := by decide +kernel
theorem inv2_check : linCheck (Impl.Aes.Arm.invMixColumns 2) p q (linG 2 invMcWords) = true := by decide +kernel
theorem inv3_check : linCheck (Impl.Aes.Arm.invMixColumns 3) p q (linG 3 invMcWords) = true := by decide +kernel

theorem mix_check {f : Nat} (hf : f < 4) :
    linCheck (Impl.Aes.Arm.mixColumns f) p q (linG f mcWords) = true := by
  rcases f with _ | _ | _ | _ | f
  · exact mix0_check
  · exact mix1_check
  · exact mix2_check
  · exact mix3_check
  · omega_using [hf]

theorem inv_check {f : Nat} (hf : f < 4) :
    linCheck (Impl.Aes.Arm.invMixColumns f) p q (linG f invMcWords) = true := by
  rcases f with _ | _ | _ | _ | f
  · exact inv0_check
  · exact inv1_check
  · exact inv2_check
  · exact inv3_check
  · omega_using [hf]

/-! ## On the machine -/

theorem frame_nil {m m' : Mem} {a : Addr} (h : Frame [⟨a, 4 * 0⟩] m m') : m' = m := by
  funext x
  exact h x fun r hr hc => by
    simp only [List.mem_singleton] at hr; subst hr
    simp [Region.Contains] at hc

/-- A linear layer that the check accepts. -/
theorem lin_ok {is : List Instr} {a d : Nat → Reg} {g : Nat → Nat → List Nat}
    (hchk : linCheck is a d g = true) (s : State) :
    ∃ s', runBlock isa is s = some s' ∧
      (∀ j < 8, ∀ x < 32, (s'.gpr (d j)).getLsbD x = Straight.xorBits (fun k => s.gpr (a k)) (g j x)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, (is.all fun i => !clobbers i r) = true → s'.gpr r = s.gpr r) := by
  obtain ⟨s', hs', hout, hrd, hwr, hsp, hoth, hfr⟩ := linear_ok hchk (noMem_ok s) (fun k => s.gpr (a k))
    (fun r i hri => by
      simp only [rIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hri
      obtain ⟨i, hi, rfl, rfl⟩ := hri
      exact ⟨by omega_using [hi], rfl⟩) (fun j hj => by simp [noMem] at hj)
  have hmem : ∀ j < 8, (d j, g j) ∈ rOuts d g := fun j hj => by
    simp only [rOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩
  exact ⟨s', hs', fun j hj x hx => hout _ _ (hmem j hj) x hx, hrd, hwr, hsp, frame_nil hfr, hoth⟩

/-- The words of the state's registers. -/
abbrev Q (s : State) (i : Nat) : BitVec 32 := s.gpr (q i)

/-- The registers `ortho` (and the key setup's layers) may write. -/
def orthoWrites : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r10, .r11]

theorem ortho_writes : ∀ r, r ∉ orthoWrites → (ortho.all fun i => !clobbers i r) = true := by
  intro r; cases r <;> decide +kernel

theorem ortho_ok' (s : State) :
    ∃ s', runBlock isa ortho s = some s' ∧
      (∀ j < 8, ∀ x < 32, (Q s' j).getLsbD x = (Q s (x % 8)).getLsbD (8 * (x / 8) + j)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ orthoWrites → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem := by
  obtain ⟨s', hs', hout, hrd, hwr, hsp, hm, hoth⟩ := lin_ok ortho_check s
  refine ⟨s', hs', fun j hj x hx => ?_, hrd, hwr, hsp, fun r hr => hoth r (ortho_writes r hr), hm⟩
  rw [hout j hj x hx, orthoG, Straight.xorBits_cons, Straight.xorBits_nil, Bool.xor_false,
    Straight.bitOf_word _ _ _ (by omega_using [hj, hx])]

theorem sr2Words_ok (s : State) :
    ∃ s', runBlock isa sr2Words s = some s' ∧
      (∀ k < 8, ∀ x < 32, (Q s' k).getLsbD x = (Q s (2 * ((k / 2 + 2 * (x / 8)) % 4) + k % 2)).getLsbD x) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ orthoWrites → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem := by
  obtain ⟨s', hs', hout, hrd, hwr, hsp, hm, hoth⟩ := lin_ok sr2Words_check s
  refine ⟨s', hs', fun j hj x hx => ?_, hrd, hwr, hsp, fun r hr => hoth r ?_, hm⟩
  · rw [hout j hj x hx, sr2WordsG, Straight.xorBits_cons, Straight.xorBits_nil, Bool.xor_false,
      Straight.bitOf_word _ _ _ hx]
  · revert hr; cases r <;> decide +kernel

theorem mix_keeps : ∀ f < 4, ((Impl.Aes.Arm.mixColumns f).all fun i => !clobbers i sb) = true ∧
    (f % 2 = 0 → ((Impl.Aes.Arm.mixColumns f).all fun i => !clobbers i kp) = true) := by decide +kernel

theorem invMix_keeps : ∀ f < 4, ((Impl.Aes.Arm.invMixColumns f).all fun i => !clobbers i sb) = true := by
  decide +kernel

theorem mix_ok {f : Nat} (hf : f < 4) (s : State) :
    ∃ s', runBlock isa (Impl.Aes.Arm.mixColumns f) s = some s' ∧
      (∀ S, BsRel f (fun j => s.gpr (p j)) S → BsRel f (Q s') fun b => Spec.Aes.mixColumns (S b)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.gpr sb = s.gpr sb ∧
      (f % 2 = 0 → s'.gpr kp = s.gpr kp) := by
  obtain ⟨s', hs', hout, hrd, hwr, hsp, hm, hoth⟩ := lin_ok (mix_check hf) s
  exact ⟨s', hs', fun S hS => bs_linear hf mc_lin hout hS, hrd, hwr, hsp, hm, hoth sb (mix_keeps f hf).1,
    fun h => hoth kp ((mix_keeps f hf).2 h)⟩

theorem invMix_ok {f : Nat} (hf : f < 4) (s : State) :
    ∃ s', runBlock isa (Impl.Aes.Arm.invMixColumns f) s = some s' ∧
      (∀ S, BsRel f (fun j => s.gpr (p j)) S → BsRel f (Q s') fun b => Spec.Aes.invMixColumns (S b)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.gpr sb = s.gpr sb := by
  obtain ⟨s', hs', hout, hrd, hwr, hsp, hm, hoth⟩ := lin_ok (inv_check hf) s
  exact ⟨s', hs', fun S hS => bs_linear hf invMc_lin hout hS, hrd, hwr, hsp, hm, hoth sb (invMix_keeps f hf)⟩

end VG.Proof.Aes.Arm
