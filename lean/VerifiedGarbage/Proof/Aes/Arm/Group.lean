module

public import VerifiedGarbage.Proof.Aes.Blocks
public import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.Bytes
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
public import VerifiedGarbage.Impl.Aes.Arm.Ctr32
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Impl.Aes.Arm.Linear
public import VerifiedGarbage.Proof.Aes.Arm.Sbox
public import VerifiedGarbage.Proof.Aes.InvRounds
public import VerifiedGarbage.Proof.Framework.Arm.Linear
import VerifiedGarbage.Proof.Framework.Omega

/-! ### The layers -/

section

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
open VG.Proof.Aes (bsByte getLsbD_bsByte getD_eq byte_ext mulBits bitsXor mul0e_bit mul0b_bit mul0d_bit mul09_bit
  invMcWords getLsbD_xtimes)
open VG.Spec.Aes (sbox invSbox mul xtimes shiftRows invShiftRows addRoundKey roundKey)

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
  exact byte_ext fun j hj => by rw [getLsbD_bsByte _ _ hj, getLsbD_bsByte _ _ hj, hq j hj]

theorem BsRel.of_eq {f : Nat} {Q : Nat → BitVec 32} {S T : Nat → Spec.Aes.State} (h : BsRel f Q S)
    (hs : ∀ b, S b = T b) : BsRel f Q T := by
  rw [← funext hs]; exact h

/-- `{63}` added to every byte. -/
def add63 (x : Spec.Aes.State) : Spec.Aes.State := x.map (· ^^^ 0x63)

theorem add63_getD (x : Spec.Aes.State) {i : Nat} (hi : i < 16) : (add63 x).getD i 0 = x.getD i 0 ^^^ 0x63 := by
  rw [getD_eq _ hi, getD_eq _ hi, add63, Vector.getElem_map]

/-! ## SubBytes and ShiftRows -/

theorem bs_subBytes {f : Nat} {P Q : Nat → BitVec 32} {S : Nat → Spec.Aes.State}
    (h : ∀ x < 32, bsByte P x = sbox (bsByte Q x) ^^^ 0x63) (hq : BsRel f Q S) :
    BsRel f P fun b => add63 (Spec.Aes.subBytes (S b)) := fun b hb i hi => by
  rw [h _ (at_lt hb), hq b hb i hi, add63_getD _ hi, getD_eq _ hi, getD_eq _ hi, Spec.Aes.subBytes, Vector.getElem_map]

theorem bs_invSubBytes {f : Nat} {P Q : Nat → BitVec 32} {S : Nat → Spec.Aes.State}
    (h : ∀ x < 32, bsByte P x = invSbox (bsByte Q x ^^^ 0x63)) (hq : BsRel f Q fun b => add63 (S b)) :
    BsRel f P fun b => Spec.Aes.invSubBytes (S b) := fun b hb i hi => by
  show _ = (Spec.Aes.invSubBytes (S b)).getD i 0
  rw [h _ (at_lt hb), hq b hb i hi, add63_getD _ hi, getD_eq _ hi, getD_eq _ hi, Spec.Aes.invSubBytes, Vector.getElem_map,
    BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem shiftRows_getD (x : Spec.Aes.State) {i : Nat} (hi : i < 16) :
    (shiftRows x).getD i 0 = x.getD (i % 4 + 4 * ((i / 4 + i % 4) % 4)) 0 := by
  rw [getD_eq _ hi, shiftRows, Vector.getElem_ofFn]

theorem invShiftRows_getD (x : Spec.Aes.State) {i : Nat} (hi : i < 16) :
    (invShiftRows x).getD i 0 = x.getD (i % 4 + 4 * ((i / 4 + 4 - i % 4) % 4)) 0 := by
  rw [getD_eq _ hi, invShiftRows, Vector.getElem_ofFn]

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
  rw [← getD_eq (d := 0) _ hi, ← getD_eq (d := 0) _ hi, shiftRows_getD _ hi, add63_getD _ (by omega_using [hi]), add63_getD _ hi,
    shiftRows_getD _ hi]

theorem add63_invShiftRows (x : Spec.Aes.State) : invShiftRows (add63 x) = add63 (invShiftRows x) := by
  apply Vector.ext
  intro i hi
  rw [← getD_eq (d := 0) _ hi, ← getD_eq (d := 0) _ hi, invShiftRows_getD _ hi, add63_getD _ (by omega_using [hi]), add63_getD _ hi,
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
  rw [← getD_eq (d := 0) _ hi, ← getD_eq (d := 0) _ hi, add63_getD _ hi]
  refine byte_ext fun j hj => ?_
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
    rw [getD_eq _ hi, Spec.Aes.mixColumns, Vector.getElem_ofFn]
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
    rw [getD_eq _ hi, Spec.Aes.invMixColumns, Vector.getElem_ofFn]
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
  refine byte_ext fun j hj => ?_
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
  exact byte_ext fun j hj => by rw [getLsbD_bsByte _ _ hj, getLsbD_bsByte _ _ hj, he j hj]

/-- The bytes of round key `j` as it is stored, `{63}` added but for the first. -/
def rkByte (w : List Byte) (j i : Nat) : Byte := (roundKey w j).getD i 0 ^^^ (if j = 0 then 0 else 0x63)

theorem addRoundKey_getD (x : Spec.Aes.State) (rk : List Byte) {i : Nat} (hi : i < 16) :
    (addRoundKey x rk).getD i 0 = x.getD i 0 ^^^ rk.getD i 0 := by
  rw [getD_eq _ hi, addRoundKey, Vector.getElem_ofFn]

theorem bs_ark {f : Nat} {P Q K : Nat → BitVec 32} {S : Nat → Spec.Aes.State} {v : Nat → Byte}
    (h : ∀ j < 8, ∀ x < 32, (Q j).getLsbD x = ((P j).getLsbD x ^^ (K j).getLsbD x)) (hp : BsRel f P S)
    (hk : KeyRel f K v) {T : Nat → Spec.Aes.State}
    (hT : ∀ b < 2, ∀ i < 16, (T b).getD i 0 = (S b).getD i 0 ^^^ v i) : BsRel f Q T := fun b hb i hi => by
  rw [hT b hb i hi, ← hp b hb i hi, ← hk b hb i hi]
  refine byte_ext fun j hj => ?_
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
  refine byte_ext fun j hj => ?_
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

end

/-! ### Two blocks -/

section

/-!
# Encrypting two blocks, bitsliced, on ARMv7

`encrypt2_ok`: from two blocks in the registers (`InRel`), with the
bitsliced round keys in the scratch buffer (`KeysAt`) and `kp` at the
first, `encrypt2` leaves the two ciphertexts, having written only the first
128 bytes of the scratch buffer. The layers are composed from their proofs
(above); the round loop's invariant is the specification's `foldl`
over the rounds done, a multiple of four of them.
-/

@[expose] public section

namespace VG.Proof.Aes.Arm

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.Aes.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg op2_lsr wp_mov wp_add wp_sub wp_cmp wp_rev
  wp_ldr wp_str)
open VG.Spec.Aes (roundKey shiftRows addRoundKey cipher)

/-! ## Slots of the scratch buffer -/

/-- Slot `k` of the scratch buffer at `B`. -/
abbrev slotA (B : Addr) (k : Nat) : Addr := B + BitVec.ofNat 64 (4 * k)

theorem slot_addr {b : BitVec 32} (hfit : b.toNat + 2048 ≤ 2 ^ 32) {k : Nat} (hk : k < 512) :
    State.addr (b + BitVec.ofNat 32 (4 * k)) = slotA (State.addr b) k := addr_add (by omega_arith)

theorem slot_addr' {b : BitVec 32} {L : Nat} (hfit : b.toNat + L ≤ 2 ^ 32) {k : Nat} (hk : 4 * k + 4 ≤ L) :
    State.addr (b + BitVec.ofNat 32 (4 * k)) = slotA (State.addr b) k := addr_add (by omega_arith)

theorem slot_in {rs : List Region} {b : BitVec 32} (hr : (⟨State.addr b, 2048⟩ : Region) ∈ rs)
    (hfit : b.toNat + 2048 ≤ 2 ^ 32) {k : Nat} (hk : k < 512) : InRegions rs (slotA (State.addr b) k) 4 := by
  rw [← slot_addr hfit hk]; exact in_off hr hfit (by omega_arith) (by omega_arith)

theorem slotA_sep (B : Addr) {j k : Nat} (hj : j < 512) (hk : k < 512) (h : j ≠ k) :
    Mem.Sep (slotA B j) (32 / 8) (slotA B k) (32 / 8) :=
  VG.Offset.sep B (by omega_arith) (by omega_arith) (by omega_arith)

theorem readW_writeW_slot (m : Mem) (B : Addr) {j k : Nat} (hj : j < 512) (hk : k < 512) (h : j ≠ k)
    (v : BitVec 32) : (m.writeW (slotA B k) v).readW (slotA B j) 32 = m.readW (slotA B j) 32 :=
  Mem.readW_writeW_sep (slotA_sep B hj hk h) (by decide)

section
variable {is : List Instr} {s : State} {Q : State → Prop} {b : BitVec 32}

theorem wp_ldS {t : Reg} {k : Nat} (hb : s.gpr sb = b) (hscr : (⟨State.addr b, 2048⟩ : Region) ∈ s.wr)
    (hfit : b.toNat + 2048 ≤ 2 ^ 32) (hk : k < 512)
    (c : ∀ s', Upd s s' t (s.mem.readW (slotA (State.addr b) k) 32) → WP isa (.block is) s' Q) :
    WP isa (.block (ldS t k :: is)) s Q :=
  wp_ldr (by omega_arith) (by rw [hb]; exact slot_addr hfit hk)
    (slot_in (List.mem_append_right _ hscr) hfit hk) c

theorem wp_stS {t : Reg} {k : Nat} (hb : s.gpr sb = b) (hscr : (⟨State.addr b, 2048⟩ : Region) ∈ s.wr)
    (hfit : b.toNat + 2048 ≤ 2 ^ 32) (hk : k < 512)
    (c : ∀ s', Mupd s s' (s.mem.writeW (slotA (State.addr b) k) (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (stS k t :: is)) s Q :=
  wp_str (by omega_arith) (by rw [hb]; exact slot_addr hfit hk) (slot_in hscr hfit hk) c

end

/-! ## Flags -/

/-- The instruction leaves the Z flag. -/
def keepsZ : Instr → Bool
  | .adds .. | .subs .. | .cmp .. => false
  | _ => true

theorem exec_z {i : Instr} {s s' : State} (hi : keepsZ i = true) (h : exec i s = some s') : s'.z = s.z := by
  cases i <;> simp only [keepsZ, Bool.false_eq_true] at hi <;> simp only [exec, reduceCtorEq] at h
  all_goals try simp only [Option.map_eq_some_iff, State.store32, State.store8, State.load32, State.load8] at h
  all_goals try split at h
  all_goals try simp only [Option.map_eq_some_iff, reduceCtorEq, Option.some.injEq] at h
  all_goals first
    | (cases h; rfl)
    | (obtain ⟨_, _, rfl⟩ := h; rfl)
    | (split at h <;> cases h; rfl)
    | (split at h <;> simp only [reduceCtorEq, Option.some.injEq] at h; obtain rfl := h; rfl)

/-- A block none of whose instructions sets the flags. -/
theorem WP.keepZ {is : List Instr} {s : State} {Q : State → Prop} (h : WP isa (.block is) s Q)
    (hz : is.all keepsZ = true) : WP isa (.block is) s fun s' => Q s' ∧ s'.z = s.z := by
  induction is generalizing s with
  | nil => rw [WP.block_nil_iff] at h ⊢; exact ⟨h, rfl⟩
  | cons i is ih =>
    rw [WP.block_cons_iff] at h ⊢
    obtain ⟨s₁, e, h₁⟩ := h
    simp only [List.all_cons, Bool.and_eq_true] at hz
    refine ⟨s₁, e, ?_⟩
    have := ih h₁ hz.2
    rwa [exec_z hz.1 e] at this

/-! ## What the rounds need, and what they keep -/

/-- The bitsliced round keys `0 … R` of the schedule `w`, from `K0`, 32 bytes each. -/
def KeysAt (m : Mem) (K0 : BitVec 32) (R : Nat) (w : List Byte) : Prop :=
  ∀ j ≤ R, KeyRel j (fun k => m.readW (wordAddr (K0 + BitVec.ofNat 32 (32 * j)) k) 32) (rkByte w j)

/-- What encryption needs: the scratch buffer (2048 bytes at `r8`) is
writable and does not wrap around, the round keys are in it, the last at
byte `lastKey`, and `kp` is at the first. -/
structure EncPre (s₀ : State) (R : Nat) (w : List Byte) : Prop where
  scr : (⟨State.addr (s₀.gpr sb), 2048⟩ : Region) ∈ s₀.wr
  fit : (s₀.gpr sb).toNat + 2048 ≤ 2 ^ 32
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  k0 : s₀.gpr kp = s₀.gpr sb + BitVec.ofNat 32 (lastKey - 32 * R)
  keys : KeysAt s₀.mem (s₀.gpr kp) R w

/-- What stays the same during encryption. -/
structure Ctx (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  keep : ∀ r, r ∉ layerWrites → r ≠ kp → s.gpr r = s₀.gpr r
  frame : Frame [⟨State.addr (s₀.gpr sb), 128⟩] s₀.mem s.mem

theorem Ctx.refl (s₀ : State) : Ctx s₀ s₀ := ⟨rfl, rfl, rfl, fun _ _ _ => rfl, Frame.refl _ _⟩

theorem Ctx.base {s₀ s : State} (hc : Ctx s₀ s) : s.gpr sb = s₀.gpr sb := hc.keep _ (by decide) (by decide)

theorem only_sb {r : Reg} (h1 : r ∉ layerWrites) (h2 : r ≠ kp) : r = sb := by
  revert h1 h2; cases r <;> decide

theorem Ctx.step {s₀ s s' : State} (hc : Ctx s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hb : s'.gpr sb = s.gpr sb)
    (hfr : Frame [⟨State.addr (s.gpr sb), 128⟩] s.mem s'.mem) : Ctx s₀ s' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp,
    fun r h1 h2 => by obtain rfl := only_sb h1 h2; exact hb.trans hc.base,
    hc.frame.trans (by rw [← hc.base]; exact hfr)⟩

/-- The key area is outside what the layers write. -/
theorem keys_disjoint (b : Addr) : Region.Disjoint ⟨b + 224, 480⟩ ⟨b, 128⟩ := by
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  bv_omega

theorem key_contains {b : BitVec 32} (hfit : b.toNat + 2048 ≤ 2 ^ 32) {R j k : Nat} (hR : R ≤ 14)
    (hj : j ≤ R) (hk : k < 8) :
    (⟨State.addr b + 224, 480⟩ : Region).Contains
      (wordAddr (b + BitVec.ofNat 32 (lastKey - 32 * R) + BitVec.ofNat 32 (32 * j)) k) (32 / 8) := by
  simp only [wordAddr, lastKey]
  rw [add_ofNat_ofNat, add_ofNat_ofNat, addr_add (by omega_using [hfit, hR, hj, hk])]
  simp only [Region.Contains]
  rw [show State.addr b + BitVec.ofNat 64 (672 - 32 * R + (32 * j + 4 * k)) - (State.addr b + 224) =
    BitVec.ofNat 64 (672 - 32 * R + (32 * j + 4 * k) - 224) by bv_omega, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega_using [hR, hj, hk])]
  omega_using [hR, hj, hk]

theorem EncPre.le {s₀ : State} {R : Nat} {w : List Byte} (hp : EncPre s₀ R w) : R ≤ 14 := by
  rcases hp.rounds with h | h | h <;> omega_using [h]

theorem EncPre.even {s₀ : State} {R : Nat} {w : List Byte} (hp : EncPre s₀ R w) : R % 2 = 0 ∧ 10 ≤ R := by
  rcases hp.rounds with h | h | h <;> omega_using [h]

theorem EncPre.keysAt {s₀ s : State} {R : Nat} {w : List Byte} (hp : EncPre s₀ R w) (hc : Ctx s₀ s) :
    KeysAt s.mem (s₀.gpr kp) R w := by
  intro j hj
  refine keyRel_congr (hp.keys j hj) fun k hk => ?_
  rw [hp.k0]
  exact hc.frame.readW (key_contains hp.fit hp.le hj hk)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact keys_disjoint _) (by decide)

/-- The state between layers: the round keys' pointer in its slot is at round key `a`. -/
structure St (s₀ : State) (a : Nat) (s : State) : Prop where
  ctx : Ctx s₀ s
  kpm : s.mem.readW (slotA (State.addr (s₀.gpr sb)) kpSlot) 32 = s₀.gpr kp + BitVec.ofNat 32 (32 * a)

theorem q_ne : ∀ a < 8, ∀ c < 8, a ≠ c → q a ≠ q c := by decide
theorem q_ne_kp (i : Nat) : q i ≠ kp := by unfold q; split <;> decide
theorem q_ne_t0 (i : Nat) : q i ≠ t0 := by unfold q; split <;> decide
theorem p_ne_kp (i : Nat) : p i ≠ kp := by unfold p; split <;> decide
theorem p_ne_t0 (i : Nat) : p i ≠ t0 := by unfold p; split <;> decide

/-- The words after SubBytes. -/
abbrev P (s : State) (i : Nat) : BitVec 32 := s.gpr (p i)

section
variable {s₀ s : State} {R a : Nat} {w : List Byte} {rest : List Instr} {Z : State → Prop}

/-- A layer that writes at most the spills' slots. -/
theorem St.layer {is : List Instr} {X : State → Prop} (h : St s₀ a s)
    (hl : ∃ s', runBlock isa is s = some s' ∧ X s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.gpr sb = s.gpr sb ∧ Frame [⟨State.addr (s.gpr sb), 48⟩] s.mem s'.mem)
    (hQ : ∀ s', St s₀ a s' → X s' → WP isa (.block rest) s' Z) : WP isa (.block (is ++ rest)) s Z := by
  obtain ⟨s', hs', hX, hrd, hwr, hsp, hsb, hfr⟩ := hl
  rw [WP.block_append_iff (M := isa)]
  refine WP.of_runBlock ⟨s', hs', hQ s' ⟨h.ctx.step hrd hwr hsp hsb (hfr.sub fun r hr =>
    ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩), ?_⟩ hX⟩
  rw [← h.kpm, ← h.ctx.base]
  refine hfr.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact (VG.Offset.disjoint_base _ (by decide) (by decide))

theorem EncPre.spillOk (hp : EncPre s₀ R w) (h : Ctx s₀ s) : Ok spillCfg s :=
  Ok.of_off (off := 0) (by rw [h.wr]; exact hp.scr) hp.fit (by show s.gpr sb = _; rw [h.base]; simp)
    (by simp [spillCfg]) rfl

/-- SubBytes, and ShiftRows. -/
theorem St.sub (hp : EncPre s₀ R w) (h : St s₀ a s) {f : Nat} {T : Nat → Spec.Aes.State} (hb : BsRel f (Q s) T)
    (hQ : ∀ s', St s₀ a s' → BsRel (f + 1) (P s') (fun b => add63 (shiftRows (Spec.Aes.subBytes (T b)))) →
      WP isa (.block rest) s' Z) : WP isa (.block (subBytes ++ rest)) s Z := by
  obtain ⟨s', h1, h2, h3, h4, h5, h6, h7⟩ := subBytes_ok (hp.spillOk h.ctx)
  refine h.layer (X := fun s' => ∀ x < 32, bsByte (P s') x = Spec.Aes.sbox (bsByte (Q s) x) ^^^ 0x63)
    ⟨s', h1, h2, h3, h4, h5, h6 sb (by decide) (by decide), h7⟩ fun s' hs' hx => hQ s' hs' ?_
  exact (bs_shiftRows (bs_subBytes hx hb)).of_eq fun b => add63_shiftRows _

/-- MixColumns. -/
theorem St.mix (h : St s₀ a s) {f g : Nat} (hf : f < 4) (hg : g % 4 = f) {T : Nat → Spec.Aes.State}
    (hb : BsRel g (P s) fun b => add63 (T b))
    (hQ : ∀ s', St s₀ a s' → BsRel g (Q s') (fun b => add63 (Spec.Aes.mixColumns (T b))) →
      (f % 2 = 0 → s'.gpr kp = s.gpr kp) → WP isa (.block rest) s' Z) :
    WP isa (.block (mixColumns f ++ rest)) s Z := by
  obtain ⟨s', h1, h2, h3, h4, h5, h6, h7, h8⟩ := mix_ok hf s
  refine h.layer (X := fun s' => BsRel g (Q s') (fun b => add63 (Spec.Aes.mixColumns (T b))) ∧
      (f % 2 = 0 → s'.gpr kp = s.gpr kp))
    ⟨s', h1, ⟨?_, h8⟩, h3, h4, h5, h7, by rw [h6]; exact Frame.refl _ _⟩ fun s' hs' hx => hQ s' hs' hx.1 hx.2
  have := h2 _ (by rw [← hg]; exact BsRel.mod.mpr hb)
  rw [← hg] at this
  exact (BsRel.mod.mp this).of_eq fun b => mix_add63 _

theorem St.wr (hp : EncPre s₀ R w) (h : St s₀ a s) : (⟨State.addr (s₀.gpr sb), 2048⟩ : Region) ∈ s.wr := by
  rw [h.ctx.wr]; exact hp.scr

theorem St.upd (h : St s₀ a s) {s' : State} {r : Reg} {v : BitVec 32} (u : Upd s s' r v) (hr : r ≠ sb) : St s₀ a s' :=
  ⟨h.ctx.step u.rd u.wr u.sp (u.other _ hr.symm) (by rw [u.mem]; exact Frame.refl _ _), by rw [u.mem]; exact h.kpm⟩

theorem St.fupd (h : St s₀ a s) {s' : State} (u : Fupd s s') : St s₀ a s' :=
  ⟨h.ctx.step u.rd u.wr u.sp (by rw [u.gpr]) (by rw [u.mem]; exact Frame.refl _ _), by rw [u.mem]; exact h.kpm⟩

/-- The round keys' pointer from its slot. -/
theorem St.ldKp (hp : EncPre s₀ R w) (h : St s₀ a s)
    (hQ : ∀ s', St s₀ a s' → s'.gpr kp = s₀.gpr kp + BitVec.ofNat 32 (32 * a) → (∀ r, r ≠ kp → s'.gpr r = s.gpr r) →
      WP isa (.block rest) s' Z) : WP isa (.block (ldKp ++ rest)) s Z :=
  wp_ldS h.ctx.base (h.wr hp) hp.fit (by decide) fun s' u =>
    hQ s' (h.upd u (by decide)) (by rw [u.gpr, h.kpm]) u.other

/-! ## AddRoundKey -/

/-- The round key's words, `off` bytes after `kp`. -/
def arkCfg (off : Nat) : Cfg := { base := sb, slots := 0, ext := kp, exts := off / 4 + 8 }

def arkG (off j x : Nat) : List Nat := [32 * j + x, 32 * (8 + (off / 4 + j)) + x]

def arkCheck (off : Nat) (d a : Nat → Reg) : Bool :=
  check (lanes 32 11) (arkCfg off) (linExt 8) (addKey off d a) (linEnv (rIns a)) (linPost 11 (rOuts d (arkG off))) &&
    ((addKey off d a).all fun i => !clobbers i sb) && ((addKey off d a).all fun i => !clobbers i kp)

theorem arkQ_check : ∀ off ∈ [0, 32, 64, 96, 128], arkCheck off q q = true := by decide +kernel
theorem arkQP_check : ∀ off ∈ [0, 64, 128], arkCheck off q p = true := by decide +kernel
theorem arkP_check : ∀ off ∈ [0, 32], arkCheck off p p = true := by decide +kernel

theorem kp_off (K0 b : BitVec 32) {R j : Nat} (hk : K0 = b + BitVec.ofNat 32 (lastKey - 32 * R)) :
    K0 + BitVec.ofNat 32 (32 * j) = b + BitVec.ofNat 32 (lastKey - 32 * R + 32 * j) := by
  rw [hk, add_ofNat_ofNat]

/-- AddRoundKey of round key `j = i + off / 32`, with `kp` at round key `i`. -/
theorem St.ark (hp : EncPre s₀ R w) (h : St s₀ a s) {i off j : Nat} {d e : Nat → Reg}
    (hk : s.gpr kp = s₀.gpr kp + BitVec.ofNat 32 (32 * i)) (hchk : arkCheck off d e = true)
    (hij : i + off / 32 = j) (ho : off % 32 = 0) (hoff : off ≤ 128) (hj : j ≤ R)
    {S T : Nat → Spec.Aes.State} (hb : BsRel j (fun k => s.gpr (e k)) S)
    (hT : ∀ b < 2, ∀ i < 16, (T b).getD i 0 = (S b).getD i 0 ^^^ rkByte w j i)
    (hQ : ∀ s', St s₀ a s' → BsRel j (fun k => s'.gpr (d k)) T → s'.gpr kp = s.gpr kp → WP isa (.block rest) s' Z) :
    WP isa (.block (addKey off d e ++ rest)) s Z := by
  simp only [arkCheck, Bool.and_eq_true] at hchk
  obtain ⟨⟨hchk, hsb⟩, hkp⟩ := hchk
  have hR := hp.le
  have hok : Ok (arkCfg off) s := Ok.of_ext (b := s₀.gpr sb) (List.mem_append_right _ (h.wr hp)) hp.fit
    (by show s.gpr kp = _; rw [hk, kp_off _ _ hp.k0]) (by
      simp only [arkCfg, lastKey]; omega_using [hij, hj, hR, ho]) rfl
  let W : Nat → BitVec 32 := fun k => if k < 8 then s.gpr (e k) else s.mem.readW (wordAddr (s.gpr kp) (k - 8)) 32
  obtain ⟨s', hs', hout, hrd, hwr, hsp, hoth, hfr⟩ := linear_ok hchk hok W (fun r k hri => by
      simp only [rIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hri
      obtain ⟨k, hk8, rfl, rfl⟩ := hri
      exact ⟨by omega_using [hk8], by simp [W, hk8]⟩) (fun k hk8 => by
      simp only [arkCfg] at hk8 ⊢
      refine ⟨by omega_using [hk8, hoff], ?_⟩
      simp [W, show ¬ 8 + k < 8 by omega_using []])
  have hm : s'.mem = s.mem := frame_nil hfr
  refine h.layer (X := fun s' => BsRel j (fun k => s'.gpr (d k)) T ∧ s'.gpr kp = s.gpr kp)
    ⟨s', hs', ⟨?_, hoth kp hkp⟩, hrd, hwr, hsp, hoth sb hsb, by rw [hm]; exact Frame.refl _ _⟩
    fun s' hs' hx => hQ s' hs' hx.1 hx.2
  refine bs_ark (K := fun k => s.mem.readW (wordAddr (s₀.gpr kp + BitVec.ofNat 32 (32 * j)) k) 32)
    (fun k hk8 x hx => ?_) hb (hp.keysAt h.ctx j hj) hT
  have hmem : (d k, arkG off k) ∈ rOuts d (arkG off) := by
    simp only [rOuts, List.mem_map, List.mem_range]; exact ⟨k, hk8, rfl⟩
  rw [hout _ _ hmem x hx, arkG, Straight.xorBits_cons, Straight.xorBits_cons, Straight.xorBits_nil, Bool.xor_false,
    Straight.bitOf_word _ _ _ hx, Straight.bitOf_word _ _ _ hx]
  simp only [W, hk8, ite_true, show ¬ 8 + (off / 4 + k) < 8 by omega_using [], ite_false, Nat.add_sub_cancel_left]
  rw [hk, wordAddr, wordAddr, add_ofNat_ofNat, add_ofNat_ofNat,
    show 32 * i + 4 * (off / 4 + k) = 32 * j + 4 * k by omega_using [hij, ho]]

/-- Whether the last round key is `off` bytes after the pointer in the slot. -/
theorem St.test (hp : EncPre s₀ R w) (h : St s₀ a s) {off : Nat} (ho : off % 32 = 0)
    (hoff : off = 64 ∨ off = 128) (ha : a + off / 32 ≤ R)
    (hQ : ∀ s', St s₀ a s' → s'.gpr kp = s₀.gpr kp + BitVec.ofNat 32 (32 * a) → (∀ i, P s' i = P s i) →
      s'.z = decide (a + off / 32 = R) → Z s') : WP isa (.block (testLast off)) s Z := by
  refine wp_ldS h.ctx.base (h.wr hp) hp.fit (by decide) fun s₁ u₁ => ?_
  refine wp_sub (op2_reg _ _) fun s₂ u₂ => wp_cmp (op2_imm (by rcases hoff with rfl | rfl <;> decide))
    fun s₃ f₃ z₃ => WP.block_nil ?_
  have h₁ : s₁.gpr kp = s₀.gpr kp + BitVec.ofNat 32 (32 * a) := by rw [u₁.gpr, h.kpm]
  refine hQ s₃ (((h.upd u₁ (by decide)).upd u₂ (by decide)).fupd f₃) ?_ (fun i => ?_) ?_
  · rw [f₃.gpr, u₂.other _ (by decide), h₁]
  · rw [P, P, f₃.gpr, u₂.other _ (p_ne_t0 i), u₁.other _ (p_ne_kp i)]
  · rw [z₃, u₂.gpr, h₁, u₁.other _ (by decide), h.ctx.base, kp_off _ _ hp.k0]
    have hR := hp.le
    have e : s₀.gpr sb + BitVec.ofNat 32 (lastKey - 32 * R + 32 * a) - s₀.gpr sb =
        BitVec.ofNat 32 (lastKey - 32 * R + 32 * a) := by bv_omega
    rw [e]
    simp only [lastKey]
    by_cases he : a + off / 32 = R
    · rw [decide_eq_true he]
      rw [show 672 - 32 * R + 32 * a = 672 - off by omega_using [he, ho, hR, hoff]]
      simp
    · rw [decide_eq_false he, beq_eq_false_iff_ne]
      intro hc
      rcases hoff with rfl | rfl <;> bv_omega_using [hc, he, hR, ha]

/-- The transpose, to blocks' words. -/
theorem St.ortho (h : St s₀ a s) {f : Nat} {T : Nat → Spec.Aes.State} (hb : BsRel f (Q s) T)
    (hQ : ∀ s', St s₀ a s' → WRel f (Q s') T → WP isa (.block rest) s' Z) :
    WP isa (.block (ortho ++ rest)) s Z := by
  obtain ⟨s', h1, h2, h3, h4, h5, h6, h7⟩ := ortho_ok' s
  exact h.layer ⟨s', h1, h2, h3, h4, h5, h6 sb (by decide), by rw [h7]; exact Frame.refl _ _⟩
    fun s' hs' hx => hQ s' hs' (words_of_bs hx hb)

/-- The exchange between forms 0 and 2. -/
theorem St.sr2 (h : St s₀ a s) {f : Nat} {T : Nat → Spec.Aes.State} (hb : WRel f (Q s) T)
    (hQ : ∀ s', St s₀ a s' → WRel (f + 2) (Q s') T → WP isa (.block rest) s' Z) :
    WP isa (.block (sr2Words ++ rest)) s Z := by
  obtain ⟨s', h1, h2, h3, h4, h5, h6, h7⟩ := sr2Words_ok s
  exact h.layer ⟨s', h1, h2, h3, h4, h5, h6 sb (by decide), by rw [h7]; exact Frame.refl _ _⟩
    fun s' hs' hx => hQ s' hs' (words_sr2 hx hb)

end

/-! ## The rounds -/

/-- A middle round of the specification (round `j`). -/
def rnd (w : List Byte) (j : Nat) (x : Spec.Aes.State) : Spec.Aes.State :=
  addRoundKey (Spec.Aes.mixColumns (shiftRows (Spec.Aes.subBytes x))) (roundKey w j)

/-- Rounds `1 … m`, as `cipher` folds them. -/
def midRounds (w : List Byte) (m : Nat) (x : Spec.Aes.State) : Spec.Aes.State :=
  (List.range m).foldl (fun s j => rnd w (j + 1) s) x

theorem midRounds_succ (w : List Byte) (m : Nat) (x : Spec.Aes.State) :
    midRounds w (m + 1) x = rnd w (m + 1) (midRounds w m x) := by
  simp [midRounds, List.range_succ, List.foldl_append]

theorem cipher_eq (R : Nat) (w : List Byte) (x : Spec.Aes.State) :
    cipher R w x = addRoundKey (shiftRows (Spec.Aes.subBytes (midRounds w (R - 1)
      (addRoundKey x (roundKey w 0))))) (roundKey w R) := rfl

theorem cipher_last {R a : Nat} (w : List Byte) (x : Spec.Aes.State) (h : a + 1 = R) :
    addRoundKey (shiftRows (Spec.Aes.subBytes (midRounds w a (addRoundKey x (roundKey w 0))))) (roundKey w R) =
      cipher R w x := by
  rw [cipher_eq, ← h, Nat.add_sub_cancel]

theorem keepZ_last : encLast2.all keepsZ = true ∧ encLast4.all keepsZ = true ∧ encEnd.all keepsZ = true := by
  decide +kernel

/-- Four rounds, or the last two or four. -/
theorem encBody_ok {s₀ s : State} {R a : Nat} {w : List Byte} {X : Nat → Spec.Aes.State} (hp : EncPre s₀ R w)
    (h : St s₀ a s) (ha : a % 4 = 0) (haR : a < R)
    (hb : BsRel a (Q s) fun b => midRounds w a (addRoundKey (X b) (roundKey w 0))) :
    WP isa encBody s fun s' => (Arm.eval .ne s' = some false ∧ Ctx s₀ s' ∧ InRel (Q s') fun b => cipher R w (X b)) ∨
      (Arm.eval .ne s' = some true ∧ a + 4 < R ∧ St s₀ (a + 4) s' ∧
        BsRel (a + 4) (Q s') fun b => midRounds w (a + 4) (addRoundKey (X b) (roundKey w 0))) := by
  have hev := hp.even
  have hR := hp.le
  simp only [encBody, encTop, List.append_assoc]
  refine WP.seq ?_
  refine h.sub hp hb fun s₁ h₁ b₁ => h₁.mix (by decide) (by omega_using [ha]) b₁ fun s₂ h₂ b₂ _ => ?_
  refine h₂.ldKp hp fun s₃ h₃ k₃ o₃ => h₃.ark hp (j := a + 1) k₃ (arkQ_check 32 (by decide)) rfl (by decide) (by decide)
    (by omega_using [haR]) (b₂.congr fun j _ => o₃ _ (q_ne_kp j)) (fun b _ i hi => ark_next (by omega_using []) hi)
    fun s₄ h₄ b₄ _ => ?_
  refine h₄.sub hp (b₄.of_eq fun b => (midRounds_succ w a _).symm) fun s₅ h₅ b₅ => ?_
  refine h₅.test hp (by decide) (.inl rfl) (by omega_using [ha, haR, hev]) fun s₆ h₆ k₆ p₆ z₆ => ?_
  have b₆ := b₅.congr (Q' := P s₆) fun j _ => p₆ j
  refine WP.ite (decide (a + 64 / 32 = R)) (by show some s₆.z = _; rw [z₆]) (fun he => ?_) (fun he => ?_)
  · have he : a + 2 = R := by simpa using he
    refine WP.mono (WP.keepZ (Q := fun s' => Ctx s₀ s' ∧ InRel (Q s') fun b => cipher R w (X b)) ?_ keepZ_last.1)
      fun s' hs' => .inl ⟨by simp only [Arm.eval, hs'.2, z₆]; simp [he], hs'.1⟩
    simp only [encLast2, List.append_assoc]
    refine h₆.ark hp (j := a + 2) k₆ (arkQP_check 64 (by decide)) rfl (by decide) (by decide) (by omega_using [he]) b₆
      (fun b _ i hi => ark_next (by omega_using []) hi) fun s₇ h₇ b₇ _ => h₇.ortho b₇ fun s₈ h₈ w₈ => ?_
    rw [← List.append_nil sr2Words]
    refine h₈.sr2 w₈ fun s₉ h₉ w₉ => WP.block_nil ⟨h₉.ctx, inRel_iff.mp ?_⟩
    have := WRel.mod.mpr w₉
    rw [show (a + 2 + 2) % 4 = 0 by omega_using [ha]] at this
    have e : (fun b => addRoundKey (shiftRows (Spec.Aes.subBytes (midRounds w (a + 1)
        (addRoundKey (X b) (roundKey w 0))))) (roundKey w (a + 2))) = fun b => cipher R w (X b) :=
      funext fun b => by rw [he, cipher_last w _ (by omega_using [he])]
    rw [← e]; exact this
  · have he : a + 2 ≠ R := by simpa using he
    simp only [encMid, List.append_assoc]
    refine WP.seq ?_
    refine h₆.mix (by decide) (by omega_using [ha]) b₆ fun s₇ h₇ b₇ e₇ => ?_
    refine h₇.ark hp (j := a + 2) ((e₇ rfl).trans k₆) (arkQ_check 64 (by decide)) rfl (by decide) (by decide)
      (by omega_using [haR, he, ha, hev]) b₇ (fun b _ i hi => ark_next (by omega_using []) hi) fun s₈ h₈ b₈ _ => ?_
    refine h₈.sub hp (b₈.of_eq fun b => (midRounds_succ w (a + 1) _).symm) fun s₉ h₉ b₉ => ?_
    refine h₉.mix (by decide) (by omega_using [ha]) b₉ fun s₁₀ h₁₀ b₁₀ _ => ?_
    refine h₁₀.ldKp hp fun s₁₁ h₁₁ k₁₁ o₁₁ => h₁₁.ark hp (j := a + 3) k₁₁ (arkQ_check 96 (by decide)) rfl (by decide)
      (by decide) (by omega_using [haR, he, ha, hev]) (b₁₀.congr fun j _ => o₁₁ _ (q_ne_kp j))
      (fun b _ i hi => ark_next (by omega_using []) hi) fun s₁₂ h₁₂ b₁₂ _ => ?_
    refine h₁₂.sub hp (b₁₂.of_eq fun b => (midRounds_succ w (a + 2) _).symm) fun s₁₃ h₁₃ b₁₃ => ?_
    refine h₁₃.test hp (by decide) (.inr rfl) (by omega_using [ha, haR, hev, he]) fun s₁₄ h₁₄ k₁₄ p₁₄ z₁₄ => ?_
    have b₁₄ := b₁₃.congr (Q' := P s₁₄) fun j _ => p₁₄ j
    refine WP.ite (decide (a + 128 / 32 = R)) (by show some s₁₄.z = _; rw [z₁₄]) (fun hf => ?_) (fun hf => ?_)
    · have hf : a + 4 = R := by simpa using hf
      refine WP.mono (WP.keepZ (Q := fun s' => Ctx s₀ s' ∧ InRel (Q s') fun b => cipher R w (X b)) ?_ keepZ_last.2.1)
        fun s' hs' => .inl ⟨by simp only [Arm.eval, hs'.2, z₁₄]; simp [hf], hs'.1⟩
      simp only [encLast4]
      refine h₁₄.ark hp (j := a + 4) k₁₄ (arkQP_check 128 (by decide)) rfl (by decide) (by decide)
        (by omega_using [hf]) b₁₄ (fun b _ i hi => ark_next (by omega_using []) hi) fun s₁₅ h₁₅ b₁₅ _ => ?_
      rw [← List.append_nil ortho]
      refine h₁₅.ortho b₁₅ fun s₁₆ h₁₆ w₁₆ => WP.block_nil ⟨h₁₆.ctx, inRel_iff.mp ?_⟩
      have := WRel.mod.mpr w₁₆
      rw [show (a + 4) % 4 = 0 by omega_using [ha]] at this
      have e : (fun b => addRoundKey (shiftRows (Spec.Aes.subBytes (midRounds w (a + 3)
          (addRoundKey (X b) (roundKey w 0))))) (roundKey w (a + 4))) = fun b => cipher R w (X b) :=
        funext fun b => by rw [hf, cipher_last w _ (by omega_using [hf])]
      rw [← e]; exact this
    · have hf : a + 4 ≠ R := by simpa using hf
      refine WP.mono (WP.keepZ (Q := fun s' => St s₀ (a + 4) s' ∧
          BsRel (a + 4) (Q s') fun b => midRounds w (a + 4) (addRoundKey (X b) (roundKey w 0))) ?_ keepZ_last.2.2)
        fun s' hs' => .inr ⟨by simp only [Arm.eval, hs'.2, z₁₄]; simp [hf], by omega_using [haR, he, hf, ha, hev], hs'.1⟩
      simp only [encEnd, List.append_assoc]
      refine h₁₄.mix (by decide) (by omega_using [ha]) b₁₄ fun s₁₅ h₁₅ b₁₅ e₁₅ => ?_
      refine h₁₅.ark hp (j := a + 4) ((e₁₅ rfl).trans k₁₄) (arkQ_check 128 (by decide)) rfl (by decide) (by decide)
        (by omega_using [haR, he, hf, ha, hev]) b₁₅ (fun b _ i hi => ark_next (by omega_using []) hi)
        fun s₁₆ h₁₆ b₁₆ k₁₆ => ?_
      refine wp_add (op2_imm (by decide)) fun s₁₇ u₁₇ => ?_
      have h₁₇ := h₁₆.upd u₁₇ (by decide)
      have k₁₇ : s₁₇.gpr kp = s₀.gpr kp + BitVec.ofNat 32 (32 * (a + 4)) := by
        rw [u₁₇.gpr, k₁₆, (e₁₅ rfl).trans k₁₄, BitVec.add_assoc, show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl,
          ← BitVec.ofNat_add, show 32 * a + 128 = 32 * (a + 4) by omega_using []]
      refine wp_stS h₁₇.ctx.base (h₁₇.wr hp) hp.fit (by decide) fun s₁₈ u₁₈ => WP.block_nil ⟨⟨?_, ?_⟩, ?_⟩
      · refine h₁₇.ctx.step u₁₈.rd u₁₈.wr u₁₈.sp (by rw [u₁₈.gpr]) ?_
        rw [u₁₈.mem, h₁₇.ctx.base]
        exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (VG.Offset.contains_base _ (by decide) (by decide))
      · rw [u₁₈.mem, Mem.readW_writeW_self32, k₁₇]
      · exact (b₁₆.of_eq fun b => (midRounds_succ w (a + 3) _).symm).congr fun j _ => by
          show s₁₈.gpr (q j) = s₁₆.gpr (q j); rw [u₁₈.gpr, u₁₇.other _ (q_ne_kp j)]

/-- Two blocks, from `InRel` to `InRel` of their encryptions. -/
theorem encrypt2_ok {s₀ : State} {R : Nat} {w : List Byte} {S : Nat → Spec.Aes.State}
    (hp : EncPre s₀ R w) (hin : InRel (Q s₀) S) :
    WP isa encrypt2 s₀ fun s => Ctx s₀ s ∧ InRel (Q s) (fun b => cipher R w (S b)) := by
  have hev := hp.even
  let Inv : Nat → State → Prop := fun n s => ∃ a, n = R - a ∧ a < R ∧ a % 4 = 0 ∧ St s₀ a s ∧
    BsRel a (Q s) fun b => midRounds w a (addRoundKey (S b) (roundKey w 0))
  refine WP.seq (WP.mono (Q := Inv R) ?_ fun s h => WP.loop (M := isa) Inv (fun n s hs => ?_) R s h)
  · simp only [encStart, List.append_assoc]
    rw [WP.block_append_iff (M := isa)]
    obtain ⟨s₁, h1, h2, h3, h4, h5, h6, h7⟩ := ortho_ok' s₀
    refine WP.of_runBlock ⟨s₁, h1, ?_⟩
    have c₁ : Ctx s₀ s₁ := (Ctx.refl s₀).step h3 h4 h5 (h6 _ (by decide)) (by rw [h7]; exact Frame.refl _ _)
    refine wp_stS c₁.base (by rw [c₁.wr]; exact hp.scr) hp.fit (by decide) fun s₂ u₂ => ?_
    have k₂ : s₂.gpr kp = s₀.gpr kp + BitVec.ofNat 32 (32 * 0) := by rw [u₂.gpr, h6 _ (by decide)]; simp
    have hst : St s₀ 0 s₂ := by
      refine ⟨c₁.step u₂.rd u₂.wr u₂.sp (by rw [u₂.gpr]) ?_, ?_⟩
      · rw [u₂.mem, c₁.base]
        exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (VG.Offset.contains_base _ (by decide) (by decide))
      · rw [u₂.mem, Mem.readW_writeW_self32, h6 _ (by decide)]; simp
    have b₂ : BsRel 0 (Q s₂) S := (bs_of_words h2 (inRel_iff.mpr hin)).congr fun j _ => by
      show s₂.gpr (q j) = s₁.gpr (q j); rw [u₂.gpr]
    rw [← List.append_nil (addKey 0 q q)]
    exact hst.ark hp (j := 0) k₂ (arkQ_check 0 (by decide)) rfl (by decide) (by decide) (Nat.zero_le _) b₂
      (fun b _ i hi => ark_first hi) fun s₃ h₃ b₃ _ =>
      WP.block_nil ⟨0, rfl, by omega_using [hev], rfl, h₃, b₃⟩
  · obtain ⟨a, rfl, haR, ha, hst, hb⟩ := hs
    refine WP.mono (encBody_ok hp hst ha haR hb) fun s' h => ?_
    rcases h with ⟨e, h⟩ | ⟨e, h4, h5, h6⟩
    · exact .inl ⟨e, h⟩
    · exact .inr ⟨e, R - (a + 4), by omega_using [h4], a + 4, rfl, h4, by omega_using [ha], h5, h6⟩

end VG.Proof.Aes.Arm

end

end

/-!
# One group of counter-mode blocks on ARMv7

A group stores the data pointer, the blocks left and the first round key
in slots 45–47 of the scratch buffer (`groupSave`), `ctrBlocks` builds the
counter blocks `c + b` (`b < 2`) from the slots of the counter block
(`front_wp`, then `ctr_inRel` for `InRel`), `encrypt2` encrypts them
(`Encrypt.lean`), `groupLoad` loads the three values back, and `xorFull` or
`xorTail` XOR the keystream into the data, a word at a time. The
per-instruction rules are those of `Proof/MdStream/Arm/Common.lean`.
-/

@[expose] public section

namespace VG.Proof.Aes.Arm

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.Aes.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg op2_lsr wp_mov wp_add wp_sub wp_cmp wp_rev
  wp_ldr wp_str)
open VG.Proof.Aes (ctrState ctrBlock_byte toBytes_getD)

theorem wp_eor {is : List Instr} {s : State} {Q : State → Prop} {d n : Reg} {o : Op2}
    {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .eor d n o :: is)) s Q :=
  VG.Proof.MdStream.Arm.WP.cons (s' := s.setReg d (s.gpr n ^^^ y)) (by simp [exec, ho])
    (k _ (Upd.setReg _ _ _))

/-! ## The counter blocks -/

/-- The words of the counter block in the slots: words 0–2, and the counter. -/
abbrev cwW (m : Mem) (B : Addr) (k : Nat) : BitVec 32 := m.readW (slotA B (cW k)) 32
abbrev numW (m : Mem) (B : Addr) : BitVec 32 := m.readW (slotA B cNum) 32

theorem q_ctr : ∀ bb < 2, ∀ k < 4, q (2 * k + bb) ≠ sb ∧ q (2 * k + bb) ≠ t0 ∧ q (2 * k + bb) ≠ kp := by
  decide

theorem q_inj : ∀ bb < 2, ∀ j < 4, ∀ k < 4, j ≠ k → q (2 * j + bb) ≠ q (2 * k + bb) := by
  decide

theorem ctrBlock_wp {s : State} {b : BitVec 32} {bb : Nat} (hbb : bb < 2) (hb : s.gpr sb = b)
    (hscr : (⟨State.addr b, 2048⟩ : Region) ∈ s.wr) (hfit : b.toNat + 2048 ≤ 2 ^ 32) {P : State → Prop}
    (h : ∀ s', (∀ k < 3, s'.gpr (q (2 * k + bb)) = cwW s.mem (State.addr b) k) →
      s'.gpr (q (2 * 3 + bb)) = rev (numW s.mem (State.addr b) + BitVec.ofNat 32 bb) →
      (∀ r, (∀ k < 4, r ≠ q (2 * k + bb)) → r ≠ t0 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → P s') :
    WP isa (.block (ctrBlock bb)) s P := by
  obtain qc := q_ctr bb hbb
  obtain e0 : q bb = q (2 * 0 + bb) := by simp
  obtain e1 : q (2 + bb) = q (2 * 1 + bb) := by congr 1
  obtain e2 : q (4 + bb) = q (2 * 2 + bb) := by congr 1
  obtain e3 : q (6 + bb) = q (2 * 3 + bb) := by congr 1
  simp only [ctrBlock, e0, e1, e2, e3]
  refine wp_ldS hb hscr hfit (by decide) fun s₁ u₁ => ?_
  obtain hb₁ : s₁.gpr sb = b := (u₁.other _ (qc 0 (by omega_arith)).1.symm).trans hb
  refine wp_ldS hb₁ (u₁.wr ▸ hscr) hfit (by decide) fun s₂ u₂ => ?_
  obtain hb₂ : s₂.gpr sb = b := (u₂.other _ (qc 1 (by omega_arith)).1.symm).trans hb₁
  refine wp_ldS hb₂ (u₂.wr ▸ u₁.wr ▸ hscr) hfit (by decide) fun s₃ u₃ => ?_
  obtain hb₃ : s₃.gpr sb = b := (u₃.other _ (qc 2 (by omega_arith)).1.symm).trans hb₂
  refine wp_ldS hb₃ (u₃.wr ▸ u₂.wr ▸ u₁.wr ▸ hscr) hfit (by decide) fun s₄ u₄ => ?_
  refine wp_add (op2_imm (by rcases (show bb = 0 ∨ bb = 1 by omega_arith) with rfl | rfl <;> decide))
    fun s₅ u₅ => ?_
  refine wp_rev fun s₆ u₆ => ?_
  refine WP.block_nil (h s₆ (fun k hk => ?_) ?_ (fun r hr ht => ?_) ?_ ?_ ?_ ?_)
  · have hne : ∀ j < 4, j ≠ k → q (2 * k + bb) ≠ q (2 * j + bb) := fun j hj hjk =>
      q_inj bb hbb k (by omega_arith) j hj (Ne.symm hjk)
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega_arith) with rfl | rfl | rfl
    · rw [u₆.other _ (hne 3 (by omega_arith) (by omega_arith)), u₅.other _ (qc 0 (by omega_arith)).2.1,
        u₄.other _ (qc 0 (by omega_arith)).2.1, u₃.other _ (hne 2 (by omega_arith) (by omega_arith)),
        u₂.other _ (hne 1 (by omega_arith) (by omega_arith)), u₁.gpr]
    · rw [u₆.other _ (hne 3 (by omega_arith) (by omega_arith)), u₅.other _ (qc 1 (by omega_arith)).2.1,
        u₄.other _ (qc 1 (by omega_arith)).2.1, u₃.other _ (hne 2 (by omega_arith) (by omega_arith)), u₂.gpr,
        u₁.mem]
    · rw [u₆.other _ (hne 3 (by omega_arith) (by omega_arith)), u₅.other _ (qc 2 (by omega_arith)).2.1,
        u₄.other _ (qc 2 (by omega_arith)).2.1, u₃.gpr, u₂.mem, u₁.mem]
  · rw [u₆.gpr, u₅.gpr, u₄.gpr, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₆.other _ (hr 3 (by omega_arith)), u₅.other _ ht, u₄.other _ ht, u₃.other _ (hr 2 (by omega_arith)),
      u₂.other _ (hr 1 (by omega_arith)), u₁.other _ (hr 0 (by omega_arith))]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]

/-- The memory after `groupSave` and `ctrBlocks`. -/
def frontMem (m : Mem) (B : Addr) (d l f : BitVec 32) : Mem :=
  (((m.writeW (slotA B dSlot) d).writeW (slotA B lSlot) l).writeW (slotA B fkSlot) f).writeW
    (slotA B cNum) (numW m B + 2)

theorem q_other : ∀ r, r ∉ layerWrites → r ≠ kp → (∀ bb < 2, ∀ k < 4, r ≠ q (2 * k + bb)) ∧ r ≠ t0 := by
  intro r; cases r <;> decide

theorem gs_read (m : Mem) (B : Addr) (d l f : BitVec 32) {k : Nat} (hk : k < 45) :
    (((m.writeW (slotA B dSlot) d).writeW (slotA B lSlot) l).writeW (slotA B fkSlot) f).readW
      (slotA B k) 32 = m.readW (slotA B k) 32 := by
  rw [readW_writeW_slot _ _ (by omega_arith) (by decide) (by simp [fkSlot]; omega_arith),
    readW_writeW_slot _ _ (by omega_arith) (by decide) (by simp [lSlot]; omega_arith),
    readW_writeW_slot _ _ (by omega_arith) (by decide) (by simp [dSlot]; omega_arith)]

/-- `groupSave` and the two counter blocks, and `c := c + 2`. -/
theorem front_wp {s : State} {b : BitVec 32} (hb : s.gpr sb = b)
    (hscr : (⟨State.addr b, 2048⟩ : Region) ∈ s.wr) (hfit : b.toNat + 2048 ≤ 2 ^ 32) {P : State → Prop}
    (h : ∀ s', (∀ bb < 2, (∀ k < 3, s'.gpr (q (2 * k + bb)) = cwW s.mem (State.addr b) k) ∧
        s'.gpr (q (2 * 3 + bb)) = rev (numW s.mem (State.addr b) + BitVec.ofNat 32 bb)) →
      s'.gpr kp = s.gpr .r12 → (∀ r, r ∉ layerWrites → r ≠ kp → s'.gpr r = s.gpr r) →
      s'.mem = frontMem s.mem (State.addr b) (s.gpr .r10) (s.gpr .r11) (s.gpr .r12) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → P s') :
    WP isa (.block (groupSave ++ ctrBlocks)) s P := by
  simp only [groupSave, List.cons_append, List.nil_append]
  refine wp_stS hb hscr hfit (by decide) fun s₁ u₁ => ?_
  refine wp_stS (u₁.gpr ▸ hb) (u₁.wr ▸ hscr) hfit (by decide) fun s₂ u₂ => ?_
  refine wp_stS (u₂.gpr ▸ u₁.gpr ▸ hb) (u₂.wr ▸ u₁.wr ▸ hscr) hfit (by decide) fun s₃ u₃ => ?_
  refine wp_mov (op2_reg _ _) fun s₄ u₄ => ?_
  obtain hb₄ : s₄.gpr sb = b := by rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.gpr, hb]
  obtain hscr₄ : (⟨State.addr b, 2048⟩ : Region) ∈ s₄.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hscr
  obtain hm₄ : s₄.mem = ((s.mem.writeW (slotA (State.addr b) dSlot) (s.gpr .r10)).writeW
      (slotA (State.addr b) lSlot) (s.gpr .r11)).writeW (slotA (State.addr b) fkSlot) (s.gpr .r12) := by
    simp only [u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr]
  simp only [ctrBlocks]
  repeat rw [WP.block_append_iff (M := isa)]
  refine ctrBlock_wp (bb := 0) (by omega_arith) hb₄ hscr₄ hfit fun s₅ c₅ n₅ o₅ m₅ rd₅ wr₅ sp₅ => ?_
  obtain hb₅ : s₅.gpr sb = b := (o₅ _ (fun k hk => (q_ctr 0 (by omega_arith) k hk).1.symm) (by decide)).trans hb₄
  refine ctrBlock_wp (bb := 1) (by omega_arith) hb₅ (wr₅ ▸ hscr₄) hfit fun s₆ c₆ n₆ o₆ m₆ rd₆ wr₆ sp₆ => ?_
  obtain hb₆ : s₆.gpr sb = b := (o₆ _ (fun k hk => (q_ctr 1 (by omega_arith) k hk).1.symm) (by decide)).trans hb₅
  refine wp_ldS hb₆ (wr₆ ▸ wr₅ ▸ hscr₄) hfit (by decide) fun s₇ u₇ => ?_
  refine wp_add (op2_imm (by decide)) fun s₈ u₈ => ?_
  obtain hb₈ : s₈.gpr sb = b := by rw [u₈.other _ (by decide), u₇.other _ (by decide), hb₆]
  refine wp_stS hb₈ (by rw [u₈.wr, u₇.wr, wr₆, wr₅]; exact hscr₄) hfit (by decide) fun s₉ u₉ => ?_
  obtain mnum : numW s₄.mem (State.addr b) = numW s.mem (State.addr b) := by
    rw [numW, hm₄, gs_read _ _ _ _ _ (by decide)]
  obtain mcw : ∀ k < 3, cwW s₄.mem (State.addr b) k = cwW s.mem (State.addr b) k := by
    intro k hk
    rw [cwW, hm₄, gs_read _ _ _ _ _ (by simp [cW]; omega_arith)]
  refine WP.block_nil (h s₉ (fun bb hbb => ?_) ?_ (fun r h1 h2 => ?_) ?_ ?_ ?_ ?_)
  · have qo : ∀ k < 4, q (2 * k + bb) ≠ t0 := fun k hk => (q_ctr bb hbb k hk).2.1
    rcases (show bb = 0 ∨ bb = 1 by omega_arith) with rfl | rfl
    · refine ⟨fun k hk => ?_, ?_⟩
      · rw [u₉.gpr, u₈.other _ (qo k (by omega_arith)), u₇.other _ (qo k (by omega_arith)),
          o₆ _ (fun j hj => q_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)) (qo k (by omega_arith)), c₅ k hk, mcw k hk]
      · rw [u₉.gpr, u₈.other _ (qo 3 (by omega_arith)), u₇.other _ (qo 3 (by omega_arith)),
          o₆ _ (fun j hj => q_ne _ (by omega_arith) _ (by omega_arith) (by omega_arith)) (qo 3 (by omega_arith)), n₅, mnum]
    · refine ⟨fun k hk => ?_, ?_⟩
      · rw [u₉.gpr, u₈.other _ (qo k (by omega_arith)), u₇.other _ (qo k (by omega_arith)), c₆ k hk, m₅, mcw k hk]
      · rw [u₉.gpr, u₈.other _ (qo 3 (by omega_arith)), u₇.other _ (qo 3 (by omega_arith)), n₆, m₅, mnum]
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
      o₆ _ (fun j hj => (q_ctr 1 (by omega_arith) j hj).2.2.symm) (by decide),
      o₅ _ (fun j hj => (q_ctr 0 (by omega_arith) j hj).2.2.symm) (by decide), u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]
  · obtain ⟨hq, ht⟩ := q_other r h1 h2
    rw [u₉.gpr, u₈.other _ ht, u₇.other _ ht, o₆ _ (hq 1 (by omega_arith)) ht, o₅ _ (hq 0 (by omega_arith)) ht,
      u₄.other _ h2, u₃.gpr, u₂.gpr, u₁.gpr]
  · rw [u₉.mem, u₈.gpr, u₇.gpr, u₈.mem, u₇.mem, m₆, m₅, frontMem, ← mnum, hm₄]
  · rw [u₉.rd, u₈.rd, u₇.rd, rd₆, rd₅, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₉.wr, u₈.wr, u₇.wr, wr₆, wr₅, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₉.sp, u₈.sp, u₇.sp, sp₆, sp₅, u₄.sp, u₃.sp, u₂.sp, u₁.sp]

/-! ## The counter blocks as states -/

/-- The counter blocks `2g` and `2g + 1` in the words, as `InRel` has them. -/
theorem ctr_inRel {Q : Nat → BitVec 32} {icb : Spec.Gcm.Block} {W : Nat → BitVec 32} {C : BitVec 32}
    {g : Nat}
    (hw : ∀ k < 3, ∀ t < 4, ∀ j < 8, (W k).getLsbD (8 * t + j) = icb.getLsbD (8 * (15 - (4 * k + t)) + j))
    (hC : C = icb.extractLsb' 0 32 + BitVec.ofNat 32 (2 * g))
    (hQ : ∀ bb < 2, (∀ k < 3, Q (2 * k + bb) = W k) ∧ Q (2 * 3 + bb) = rev (C + BitVec.ofNat 32 bb)) :
    InRel Q (fun bb => ctrState icb (2 * g + bb)) := by
  intro bb hb i hi16 j hj
  obtain ⟨h0, h1⟩ := hQ bb hb
  simp only [ctrState, getD_eq _ hi16, Vector.getElem_ofFn]
  rw [ctrBlock_byte _ _ hi16]
  by_cases h12 : i < 12
  · rw [ite_eq_left h12, h0 _ (by omega_arith), toBytes_getD _ hi16, BitVec.getLsbD_extractLsb',
      hw _ (by omega_arith) _ (by omega_arith) _ hj, show 4 * (i / 4) + i % 4 = i by omega_arith]
    simp [hj]
  · rw [ite_eq_right h12, show i / 4 = 3 by omega_arith, h1, rev_bit _ (by omega_arith) hj, hC,
      BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.getLsbD_extractLsb']
    simp only [hj, decide_true, Bool.true_and]
    congr 1; omega_arith

/-! ## XOR into the data -/

/-- XOR `v` into the 4 bytes at `a`. -/
def xorW (m : Mem) (a : Addr) (v : BitVec 32) : Mem := m.writeW a (m.readW a 32 ^^^ v)

theorem xorW_apply (m : Mem) (a x : Addr) (v : BitVec 32) :
    xorW m a v x = if (x - a).toNat < 4 then m x ^^^ v.extractLsb' (8 * (x - a).toNat) 8 else m x := by
  unfold xorW Mem.writeW Mem.write
  split
  · rename_i h
    obtain hx : a + BitVec.ofNat 64 (x - a).toNat = x := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
    have := Mem.extractLsb'_read m a (n := 4) h
    rw [hx] at this
    rw [← this]
    ext t ht
    simp only [BitVec.getElem_extractLsb', BitVec.getElem_xor, Mem.readW]
    simp
  · rfl

/-- The data after `k` words: the keystream `ks` XORed into the first `4 k`
of the `16 n` bytes at `D`. -/
def DataInv (m₀ m : Mem) (D : Addr) (n k : Nat) (ks : Nat → Byte) : Prop :=
  ∀ i < 16 * n, m (D + BitVec.ofNat 64 i) =
    m₀ (D + BitVec.ofNat 64 i) ^^^ (if i < 4 * k then ks i else 0)

theorem off_toNat (D : Addr) {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) :
    (D + BitVec.ofNat 64 i - (D + BitVec.ofNat 64 j)).toNat =
      if j ≤ i then i - j else 2 ^ 64 + i - j := by
  rw [← BitVec.sub_sub, BitVec.add_comm D, BitVec.add_sub_cancel, BitVec.toNat_sub, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]
  split
  · rw [show 2 ^ 64 - j + i = (i - j) + 2 ^ 64 by omega_arith, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_arith)]
  · rw [show 2 ^ 64 - j + i = 2 ^ 64 + i - j by omega_arith]; exact Nat.mod_eq_of_lt (by omega_arith)

/-- One word of keystream XORed in. -/
theorem dataInv_step {m₀ m : Mem} {D : Addr} {n k : Nat} {ks : Nat → Byte} {v : BitVec 32}
    (hn : 16 * n ≤ 2 ^ 32) (hk : k < 4 * n) (h : DataInv m₀ m D n k ks)
    (hks : ∀ t < 4, v.extractLsb' (8 * t) 8 = ks (4 * k + t)) :
    DataInv m₀ (xorW m (D + BitVec.ofNat 64 (4 * k)) v) D n (k + 1) ks ∧
      Frame [⟨D, 16 * n⟩] m (xorW m (D + BitVec.ofNat 64 (4 * k)) v) := by
  refine ⟨fun i hi => ?_, fun x hx => ?_⟩
  · rw [xorW_apply, off_toNat D (by omega_arith) (by omega_arith), h i hi]
    by_cases h1 : 4 * k ≤ i
    · rw [ite_eq_left h1]
      by_cases h2 : i - 4 * k < 4
      · rw [ite_eq_left h2, hks _ h2, ite_eq_right (show ¬ i < 4 * k by omega_arith),
          ite_eq_left (show i < 4 * (k + 1) by omega_arith), show 4 * k + (i - 4 * k) = i by omega_arith]
        simp
      · rw [ite_eq_right h2, ite_eq_right (show ¬ i < 4 * k by omega_arith),
          ite_eq_right (show ¬ i < 4 * (k + 1) by omega_arith)]
    · rw [ite_eq_right h1, ite_eq_right (show ¬ 2 ^ 64 + i - 4 * k < 4 by omega_arith),
        ite_eq_left (show i < 4 * k by omega_arith), ite_eq_left (show i < 4 * (k + 1) by omega_arith)]
  · have hx' : ¬ (x - D).toNat + 1 ≤ 16 * n := hx _ (List.mem_singleton_self _)
    rw [xorW_apply, ite_eq_right]
    have : 4 * k < 2 ^ 64 := by omega_arith
    have : (BitVec.ofNat 64 (4 * k)).toNat = 4 * k := by simp; omega_arith
    bv_omega

theorem dataInv_mono {m₀ m : Mem} {D : Addr} {n k k' : Nat} {ks : Nat → Byte} (h : DataInv m₀ m D n k ks)
    (hk : 4 * n ≤ k) (hk' : 4 * n ≤ k') : DataInv m₀ m D n k' ks := by
  intro i hi
  rw [h i hi, ite_eq_left (show i < 4 * k by omega_arith), ite_eq_left (show i < 4 * k' by omega_arith)]

/-! ## Out of place -/

/-- A separate destination pointer may designate the source itself or a disjoint
range. The single-pointer entry always designates the source. -/
def ModeOk (to : Bool) (Sp Tp : BitVec 32) (n : Nat) : Prop :=
  if to then Sp = Tp ∨ Region.Disjoint ⟨State.addr Sp, 16 * n⟩ ⟨State.addr Tp, 16 * n⟩ else Sp = Tp

/-- The data after `k` words, read at `S` and written to `T`: the first `4 k`
bytes at `T` are those at `S` on entry with the keystream `ks` XORed in, and
the rest at `S` are as on entry. In place (`S = T`), `DataInv`. -/
def DataInvG (m₀ m : Mem) (S T : Addr) (n k : Nat) (ks : Nat → Byte) : Prop :=
  ∀ i < 16 * n, (i < 4 * k → m (T + BitVec.ofNat 64 i) = m₀ (S + BitVec.ofNat 64 i) ^^^ ks i) ∧
    (4 * k ≤ i → m (S + BitVec.ofNat 64 i) = m₀ (S + BitVec.ofNat 64 i))

theorem dataInvG_iff {m₀ m : Mem} {D : Addr} {n k : Nat} {ks : Nat → Byte} :
    DataInvG m₀ m D D n k ks ↔ DataInv m₀ m D n k ks := by
  constructor
  · intro h i hi
    by_cases h1 : i < 4 * k
    · rw [ite_eq_left h1]; exact (h i hi).1 h1
    · rw [ite_eq_right h1, (h i hi).2 (by omega_arith)]; ext; simp
  · intro h i hi
    exact ⟨fun h1 => by rw [h i hi, ite_eq_left h1],
      fun h1 => by rw [h i hi, ite_eq_right (show ¬ i < 4 * k by omega_arith)]; ext; simp⟩

theorem writeW32_apply (m : Mem) (a x : Addr) (v : BitVec 32) :
    m.writeW a v x = if (x - a).toNat < 4 then v.extractLsb' (8 * (x - a).toNat) 8 else m x := by
  unfold Mem.writeW Mem.write
  split
  · ext t ht
    simp only [BitVec.getElem_extractLsb']
    simp
  · rfl

theorem readW32_byte (m : Mem) (a : Addr) {j : Nat} (hj : j < 4) :
    (m.readW a 32).extractLsb' (8 * j) 8 = m (a + BitVec.ofNat 64 j) := by
  rw [← Mem.extractLsb'_read m a hj]
  ext t ht
  simp only [BitVec.getElem_extractLsb', Mem.readW]
  simp

/-- One word of keystream XORed in, from `S` to `T`. -/
theorem dataInvG_step {m₀ m : Mem} {S T : Addr} {n k : Nat} {ks : Nat → Byte} {v : BitVec 32}
    (hn : 16 * n ≤ 2 ^ 32) (hk : k < 4 * n)
    (hST : S = T ∨ Region.Disjoint ⟨S, 16 * n⟩ ⟨T, 16 * n⟩) (h : DataInvG m₀ m S T n k ks)
    (hks : ∀ t < 4, v.extractLsb' (8 * t) 8 = ks (4 * k + t)) :
    DataInvG m₀ (m.writeW (T + BitVec.ofNat 64 (4 * k)) (m.readW (S + BitVec.ofNat 64 (4 * k)) 32 ^^^ v))
        S T n (k + 1) ks ∧
      Frame [⟨T, 16 * n⟩] m
        (m.writeW (T + BitVec.ofNat 64 (4 * k)) (m.readW (S + BitVec.ofNat 64 (4 * k)) 32 ^^^ v)) := by
  rcases hST with rfl | hd
  · obtain ⟨h1, h2⟩ := dataInv_step (v := v) hn hk (dataInvG_iff.1 h) hks
    exact ⟨dataInvG_iff.2 h1, h2⟩
  obtain hf : Frame [⟨T, 16 * n⟩] m
      (m.writeW (T + BitVec.ofNat 64 (4 * k)) (m.readW (S + BitVec.ofNat 64 (4 * k)) 32 ^^^ v)) := by
    intro x hx
    obtain hx' : ¬ (x - T).toNat + 1 ≤ 16 * n := hx _ (List.mem_singleton_self _)
    rw [writeW32_apply, ite_eq_right]
    have : 4 * k < 2 ^ 64 := by omega_arith
    have : (BitVec.ofNat 64 (4 * k)).toNat = 4 * k := by simp; omega_arith
    bv_omega
  refine ⟨fun i hi => ⟨fun h1 => ?_, fun h1 => ?_⟩, hf⟩
  · rw [writeW32_apply, off_toNat T (by omega_arith) (by omega_arith)]
    by_cases h2 : 4 * k ≤ i
    · rw [ite_eq_left h2, ite_eq_left (show i - 4 * k < 4 by omega_arith), BitVec.extractLsb'_xor,
        readW32_byte _ _ (show i - 4 * k < 4 by omega_arith), hks _ (by omega_arith),
        BitVec.add_assoc, ← BitVec.ofNat_add, show 4 * k + (i - 4 * k) = i by omega_arith,
        (h i hi).2 h2]
    · rw [ite_eq_right h2, ite_eq_right (show ¬ 2 ^ 64 + i - 4 * k < 4 by omega_arith),
        (h i hi).1 (by omega_arith)]
  · rw [hf.bytes (R := ⟨S, 16 * n⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hd) (by simp only; omega_arith) hi,
      (h i hi).2 (by omega_arith)]

theorem dataInvG_mono {m₀ m : Mem} {S T : Addr} {n k k' : Nat} {ks : Nat → Byte}
    (h : DataInvG m₀ m S T n k ks) (hk : 4 * n ≤ k) (hk' : 4 * n ≤ k') : DataInvG m₀ m S T n k' ks :=
  fun i hi => ⟨fun _ => (h i hi).1 (by omega_arith), fun h1 => by omega_arith⟩

/-- The keystream, byte by byte: byte `i` is byte `i mod 16` of the
encrypted counter block `i / 16`. -/
def keyStream (R : Nat) (w : List Byte) (icb : Spec.Gcm.Block) (i : Nat) : Byte :=
  (Spec.Aes.cipher R w (ctrState icb (i / 16))).getD (i % 16) 0

theorem ks_of_inRel {Q : Nat → BitVec 32} {R g : Nat} {w : List Byte} {icb : Spec.Gcm.Block}
    (h : InRel Q (fun bb => Spec.Aes.cipher R w (ctrState icb (2 * g + bb)))) {k t : Nat} (hk : k < 8)
    (ht : t < 4) :
    (Q (2 * (k % 4) + k / 4)).extractLsb' (8 * t) 8 = keyStream R w icb (4 * (8 * g + k) + t) := by
  apply byte_ext
  intro j hj
  have := h (k / 4) (by omega_arith) (4 * (k % 4) + t) (by omega_arith) j hj
  rw [show (4 * (k % 4) + t) / 4 = k % 4 by omega_arith, show (4 * (k % 4) + t) % 4 = t by omega_arith] at this
  rw [BitVec.getLsbD_extractLsb', this, keyStream,
    show (4 * (8 * g + k) + t) / 16 = 2 * g + k / 4 by omega_arith,
    show (4 * (8 * g + k) + t) % 16 = 4 * (k % 4) + t by omega_arith]
  simp [hj]

/-- Word `k` of a group of two blocks: `ldr`, `eor` with its keystream word, `str`. -/
def triple (to : Bool) (k : Nat) : List Instr :=
  [.ldr .lr .r10 (4 * k), eorR .lr .lr (q (2 * (k % 4) + k / 4)), .str .lr (dstReg to) (4 * k)]

theorem xorFull_eq (to : Bool) : xorFullG to = triple to 0 ++ triple to 1 ++ triple to 2 ++
    triple to 3 ++ triple to 4 ++ triple to 5 ++ triple to 6 ++ triple to 7 ++
    ([.dp .add .r10 .r10 (.imm 32), .dp .sub .r11 .r11 (.imm 2)] : List Instr) := by
  cases to <;> rfl

theorem xorTail_eq (to : Bool) : xorTailG to = triple to 0 ++ triple to 1 ++ triple to 2 ++
    triple to 3 ++ ([.mov .r11 (.imm 0)] : List Instr) := by
  cases to <;> rfl

theorem dstReg_ne (to : Bool) : dstReg to ≠ .lr ∧ dstReg to ≠ .r11 ∧ dstReg to ≠ sb := by
  cases to <;> decide

/-- After `k` words of the group have been XORed in, from `s₃`. -/
structure XS (to : Bool) (m₀ : Mem) (S T : Addr) (n g : Nat) (ks : Nat → Byte) (s₃ : State) (k : Nat)
    (s : State) : Prop where
  data : DataInvG m₀ s.mem S T n (8 * g + k) ks
  frame : Frame [⟨T, 16 * n⟩] s₃.mem s.mem
  keep : ∀ r, r ≠ .lr → s.gpr r = s₃.gpr r
  rd : s.rd = s₃.rd
  wr : s.wr = s₃.wr
  sp : s.sp = s₃.sp

/-- Before the XOR phase of group `g`: the keystream is in the words, the
source at `r10` and, out of place, the destination in slot 48. -/
structure XPre (to : Bool) (m₀ : Mem) (b Sp Tp : BitVec 32) (n g : Nat) (ks : Nat → Byte) (s₃ : State) :
    Prop where
  hg : 2 * g < n
  fit : Sp.toNat + 16 * n ≤ 2 ^ 32
  fitT : Tp.toNat + 16 * n ≤ 2 ^ 32
  src : (⟨State.addr Sp, 16 * n⟩ : Region) ∈ s₃.rd ++ s₃.wr
  dat : (⟨State.addr Tp, 16 * n⟩ : Region) ∈ s₃.wr
  mode : ModeOk to Sp Tp n
  base : s₃.gpr sb = b
  scr : (⟨State.addr b, 2048⟩ : Region) ∈ s₃.wr
  fitB : b.toNat + 2048 ≤ 2 ^ 32
  sepS : Region.Disjoint ⟨State.addr Sp, 16 * n⟩ ⟨State.addr b, 2048⟩
  sepT : Region.Disjoint ⟨State.addr Tp, 16 * n⟩ ⟨State.addr b, 2048⟩
  slot : to = true → s₃.mem.readW (slotA (State.addr b) dstSlot) 32 = Tp + BitVec.ofNat 32 (32 * g)
  r10 : s₃.gpr .r10 = Sp + BitVec.ofNat 32 (32 * g)
  r11 : s₃.gpr .r11 = BitVec.ofNat 32 (n - 2 * g)
  data : DataInvG m₀ s₃.mem (State.addr Sp) (State.addr Tp) n (8 * g) ks
  ks : ∀ k < 8, ∀ t < 4, (s₃.gpr (q (2 * (k % 4) + k / 4))).extractLsb' (8 * t) 8 = ks (4 * (8 * g + k) + t)

section Xor

variable {to : Bool} {m₀ : Mem} {b Sp Tp : BitVec 32} {n g : Nat} {ks : Nat → Byte}

theorem XPre.apart {s : State} (hp : XPre to m₀ b Sp Tp n g ks s) :
    State.addr Sp = State.addr Tp ∨
      Region.Disjoint ⟨State.addr Sp, 16 * n⟩ ⟨State.addr Tp, 16 * n⟩ := by
  have h := hp.mode
  unfold ModeOk at h
  cases to
  · exact .inl (congrArg _ h)
  · exact h.imp (congrArg State.addr) id

theorem xs_step {s₃ : State} (hp : XPre to m₀ b Sp Tp n g ks s₃) {k : Nat} (hk : k < 8)
    (hkn : 8 * g + k < 4 * n) {sB : State} (hd : sB.gpr (dstReg to) = Tp + BitVec.ofNat 32 (32 * g))
    (h10 : sB.gpr .r10 = Sp + BitVec.ofNat 32 (32 * g))
    (hq : ∀ k < 8, sB.gpr (q (2 * (k % 4) + k / 4)) = s₃.gpr (q (2 * (k % 4) + k / 4)))
    (hrw : sB.rd = s₃.rd ∧ sB.wr = s₃.wr) {s : State}
    (hs : XS to m₀ (State.addr Sp) (State.addr Tp) n g ks sB k s) {is : List Instr} {P : State → Prop}
    (h : ∀ s', XS to m₀ (State.addr Sp) (State.addr Tp) n g ks sB (k + 1) s' → WP isa (.block is) s' P) :
    WP isa (.block (triple to k ++ is)) s P := by
  have hn := hp.fit
  have hnT := hp.fitT
  obtain ha : State.addr (s.gpr .r10 + BitVec.ofNat 32 (4 * k)) =
      State.addr Sp + BitVec.ofNat 64 (4 * (8 * g + k)) := by
    rw [hs.keep _ (by decide), h10, add_ofNat_ofNat, addr_add (by omega_arith)]
    congr 2; omega_arith
  obtain hl : (dstReg to) ≠ .lr := (dstReg_ne to).1
  obtain haT : State.addr (s.gpr (dstReg to) + BitVec.ofNat 32 (4 * k)) =
      State.addr Tp + BitVec.ofNat 64 (4 * (8 * g + k)) := by
    rw [hs.keep _ hl, hd, add_ofNat_ofNat, addr_add (by omega_arith)]
    congr 2; omega_arith
  obtain hin : InRegions (s.rd ++ s.wr) (State.addr Sp + BitVec.ofNat 64 (4 * (8 * g + k))) 4 := by
    obtain hsrc : (⟨State.addr Sp, 16 * n⟩ : Region) ∈ s.rd ++ s.wr := by
      rw [hs.rd, hs.wr, hrw.1, hrw.2]; exact hp.src
    have := in_off hsrc hp.fit (off := 4 * (8 * g + k)) (n := 4) (by omega_arith) (by omega_arith)
    rwa [addr_add (by omega_arith)] at this
  obtain hout : InRegions s.wr (State.addr Tp + BitVec.ofNat 64 (4 * (8 * g + k))) 4 := by
    have := in_off (show (⟨State.addr Tp, 16 * n⟩ : Region) ∈ s.wr by rw [hs.wr, hrw.2]; exact hp.dat) hp.fitT (off := 4 * (8 * g + k)) (n := 4)
      (by omega_arith) (by omega_arith)
    rwa [addr_add (by omega_arith)] at this
  obtain hql : q (2 * (k % 4) + k / 4) ≠ .lr := by unfold q; split <;> decide
  simp only [triple, List.cons_append, List.nil_append]
  refine wp_ldr (by omega_arith) ha hin fun s₁ u₁ => ?_
  refine wp_eor (op2_reg _ _) fun s₂ u₂ => ?_
  refine wp_str (a := State.addr Tp + BitVec.ofNat 64 (4 * (8 * g + k))) (by omega_arith)
    (by rw [u₂.other _ hl, u₁.other _ hl]; exact haT)
    (by rw [u₂.wr, u₁.wr]; exact hout) fun s₃' u₃ => ?_
  obtain hst := dataInvG_step (v := s.gpr (q (2 * (k % 4) + k / 4))) (by omega_arith) hkn hp.apart hs.data
    (fun t ht => by rw [hs.keep _ hql, hq k hk]; exact hp.ks k hk t ht)
  obtain hm : s₃'.mem = s.mem.writeW (State.addr Tp + BitVec.ofNat 64 (4 * (8 * g + k)))
      (s.mem.readW (State.addr Sp + BitVec.ofNat 64 (4 * (8 * g + k))) 32 ^^^
        s.gpr (q (2 * (k % 4) + k / 4))) := by
    rw [u₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr, u₁.other _ hql]
  rw [← hm] at hst
  refine h s₃' ⟨by rw [show 8 * g + (k + 1) = 8 * g + k + 1 by omega_arith]; exact hst.1,
    hs.frame.trans hst.2, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [u₃.gpr, u₂.other _ hr, u₁.other _ hr, hs.keep r hr]
  · rw [u₃.rd, u₂.rd, u₁.rd, hs.rd]
  · rw [u₃.wr, u₂.wr, u₁.wr, hs.wr]
  · rw [u₃.sp, u₂.sp, u₁.sp, hs.sp]

/-- The frame of the XOR phase: the destination, and the slot of its pointer. -/
abbrev xRegions (B T : Addr) (n : Nat) : List Region := [⟨T, 16 * n⟩, ⟨B + BitVec.ofNat 64 192, 4⟩]

/-- After the XOR: `r11` is zero if no data is left; out of place, `kp`
still holds the destination of the group. -/
def XMid (to : Bool) (m₀ : Mem) (Sp Tp : BitVec 32) (n g : Nat) (ks : Nat → Byte) (s₃ s : State) :
    Prop :=
  Frame [⟨State.addr Tp, 16 * n⟩] s₃.mem s.mem ∧
    (∀ r, r ≠ .lr → r ≠ kp → r ≠ .r10 → r ≠ .r11 → s.gpr r = s₃.gpr r) ∧
    s.rd = s₃.rd ∧ s.wr = s₃.wr ∧ s.sp = s₃.sp ∧
    (to = true → s.gpr kp = Tp + BitVec.ofNat 32 (32 * g)) ∧
    ((s.gpr .r11 = 0 ∧ DataInvG m₀ s.mem (State.addr Sp) (State.addr Tp) n (4 * n) ks) ∨
     (2 * g + 2 < n ∧ DataInvG m₀ s.mem (State.addr Sp) (State.addr Tp) n (8 * (g + 1)) ks ∧
      s.gpr .r10 = Sp + BitVec.ofNat 32 (32 * (g + 1)) ∧
      s.gpr .r11 = BitVec.ofNat 32 (n - 2 * (g + 1))))

/-- After the XOR phase, and the destination pointer stored back. -/
def XDone (to : Bool) (m₀ : Mem) (b Sp Tp : BitVec 32) (n g : Nat) (ks : Nat → Byte) (s₃ s : State) :
    Prop :=
  Frame (xRegions (State.addr b) (State.addr Tp) n) s₃.mem s.mem ∧
    (∀ r, r ≠ .lr → r ≠ kp → r ≠ .r10 → r ≠ .r11 → s.gpr r = s₃.gpr r) ∧
    s.rd = s₃.rd ∧ s.wr = s₃.wr ∧ s.sp = s₃.sp ∧
    ((s.gpr .r11 = 0 ∧ DataInvG m₀ s.mem (State.addr Sp) (State.addr Tp) n (4 * n) ks) ∨
     (2 * g + 2 < n ∧ DataInvG m₀ s.mem (State.addr Sp) (State.addr Tp) n (8 * (g + 1)) ks ∧
      s.gpr .r10 = Sp + BitVec.ofNat 32 (32 * (g + 1)) ∧
      s.gpr .r11 = BitVec.ofNat 32 (n - 2 * (g + 1)) ∧
      (to = true → s.mem.readW (slotA (State.addr b) dstSlot) 32 = Tp + BitVec.ofNat 32 (32 * (g + 1)))))

theorem shr1_eq (x : Nat) (hx : x < 2 ^ 32) :
    (!(BitVec.ofNat 32 x >>> 1 - 0 == 0)) = decide (2 ≤ x) := by
  by_cases h : 2 ≤ x
  · have : BitVec.ofNat 32 x >>> 1 - 0 ≠ 0 := by bv_omega
    simpa [h] using this
  · have : BitVec.ofNat 32 x >>> 1 - 0 = 0 := by bv_omega
    rw [this]; simp [h]

/-- The destination pointer to `dstReg to`; the flags are kept. -/
theorem dstLoad_wp {s₃ : State} (hp : XPre to m₀ b Sp Tp n g ks s₃) {s : State}
    (hs : ∀ r, r ≠ kp → s.gpr r = s₃.gpr r) (hm : s.mem = s₃.mem) (hwr : s.wr = s₃.wr)
    {is : List Instr} {P : State → Prop}
    (h : ∀ s', s'.gpr (dstReg to) = Tp + BitVec.ofNat 32 (32 * g) → (∀ r, r ≠ kp → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → s'.z = s.z → WP isa (.block is) s' P) :
    WP isa (.block (dstLoad to ++ is)) s P := by
  cases to
  · refine h s ?_ (fun _ _ => rfl) rfl rfl rfl rfl rfl
    rw [show dstReg false = .r10 from rfl, hs _ (by decide), hp.r10, show Sp = Tp from hp.mode]
  · simp only [dstLoad, ite_true, List.cons_append, List.nil_append]
    obtain ha : State.addr (s.gpr sb + BitVec.ofNat 32 (4 * dstSlot)) = slotA (State.addr b) dstSlot := by
      rw [hs _ (by decide), hp.base]; exact slot_addr hp.fitB (by decide)
    obtain hin : InRegions (s.rd ++ s.wr) (slotA (State.addr b) dstSlot) 4 :=
      slot_in (List.mem_append_right _ (by rw [hwr]; exact hp.scr)) hp.fitB (by decide)
    rw [← ha] at hin
    refine VG.Proof.MdStream.Arm.WP.cons (exec_ldr (by decide) hin) ?_
    refine h _ ?_ (fun r hr => ?_) rfl rfl rfl rfl rfl
    · rw [show dstReg true = kp from rfl, VG.Arm.RegUpd.gpr_setReg_self, ha, hm, hp.slot rfl]
    · exact VG.Arm.RegUpd.gpr_setReg_of_ne _ _ hr

theorem xorPhase_wp {s₃ : State} (hp : XPre to m₀ b Sp Tp n g ks s₃) :
    WP isa (.block (([.mov kp (lsrOp .r11 1), .cmp kp (.imm 0)] : List Instr) ++ dstLoad to)) s₃ fun s =>
      WP isa (.ite .ne (.block (xorFullG to)) (.block (xorTailG to))) s (XMid to m₀ Sp Tp n g ks s₃) := by
  have hg := hp.hg
  have hn := hp.fit
  have hnT := hp.fitT
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_lsr (by decide)) fun s₄ u₄ => wp_cmp (op2_imm (by decide)) fun s₅ f₅ z₅ => ?_
  obtain g₅ : ∀ r, r ≠ kp → s₅.gpr r = s₃.gpr r := fun r hr => by rw [f₅.gpr, u₄.other r hr]
  obtain m₅ : s₅.mem = s₃.mem := by rw [f₅.mem, u₄.mem]
  obtain rd₅ : s₅.rd = s₃.rd := by rw [f₅.rd, u₄.rd]
  obtain wr₅ : s₅.wr = s₃.wr := by rw [f₅.wr, u₄.wr]
  obtain sp₅ : s₅.sp = s₃.sp := by rw [f₅.sp, u₄.sp]
  rw [← List.append_nil (dstLoad to)]
  refine dstLoad_wp hp g₅ m₅ wr₅ fun sB dB hB mB rdB wrB spB zB => WP.block_nil ?_
  obtain ev : Arm.eval .ne sB = some (decide (2 ≤ n - 2 * g)) := by
    rw [Arm.eval, zB, z₅, u₄.gpr, hp.r11, shr1_eq _ (by omega_arith)]
  obtain gB : ∀ r, r ≠ kp → sB.gpr r = s₃.gpr r := fun r hr => (hB r hr).trans (g₅ r hr)
  obtain mB' : sB.mem = s₃.mem := mB.trans m₅
  obtain rdB' : sB.rd = s₃.rd := rdB.trans rd₅
  obtain wrB' : sB.wr = s₃.wr := wrB.trans wr₅
  obtain spB' : sB.sp = s₃.sp := spB.trans sp₅
  obtain x₀ : XS to m₀ (State.addr Sp) (State.addr Tp) n g ks sB 0 sB :=
    ⟨by rw [mB']; exact hp.data, Frame.refl _ _, fun _ _ => rfl, rfl, rfl, rfl⟩
  obtain hqk : ∀ k < 8, q (2 * (k % 4) + k / 4) ≠ kp := fun k hk =>
    (q_ctr (k / 4) (by omega_arith) (k % 4) (by omega_arith)).2.2
  obtain h10 : sB.gpr .r10 = Sp + BitVec.ofNat 32 (32 * g) := by rw [gB _ (by decide), hp.r10]
  obtain hq : ∀ k < 8, sB.gpr (q (2 * (k % 4) + k / 4)) = s₃.gpr (q (2 * (k % 4) + k / 4)) :=
    fun k hk => gB _ (hqk k hk)
  obtain hrw : sB.rd = s₃.rd ∧ sB.wr = s₃.wr := ⟨rdB', wrB'⟩
  obtain hkp : ∀ s, XS to m₀ (State.addr Sp) (State.addr Tp) n g ks sB 8 s ∨
      XS to m₀ (State.addr Sp) (State.addr Tp) n g ks sB 4 s → s.gpr kp = sB.gpr kp := fun s h =>
    by rcases h with h | h <;> exact h.keep _ (by decide)
  obtain kpB : to = true → sB.gpr kp = Tp + BitVec.ofNat 32 (32 * g) := fun ht => by subst ht; exact dB
  refine WP.ite (decide (2 ≤ n - 2 * g)) ev (fun hb => ?_) (fun hb => ?_)
  · -- Two blocks.
    obtain h2 : 2 ≤ n - 2 * g := by simpa using hb
    rw [xorFull_eq]
    simp only [List.append_assoc]
    refine xs_step hp (k := 0) (by omega_arith) (by omega_arith) dB h10 hq hrw x₀ fun s₆ x₆ => ?_
    refine xs_step hp (k := 1) (by omega_arith) (by omega_arith) dB h10 hq hrw x₆ fun s₇ x₇ => ?_
    refine xs_step hp (k := 2) (by omega_arith) (by omega_arith) dB h10 hq hrw x₇ fun s₈ x₈ => ?_
    refine xs_step hp (k := 3) (by omega_arith) (by omega_arith) dB h10 hq hrw x₈ fun s₉ x₉ => ?_
    refine xs_step hp (k := 4) (by omega_arith) (by omega_arith) dB h10 hq hrw x₉ fun s₁₀ x₁₀ => ?_
    refine xs_step hp (k := 5) (by omega_arith) (by omega_arith) dB h10 hq hrw x₁₀ fun s₁₁ x₁₁ => ?_
    refine xs_step hp (k := 6) (by omega_arith) (by omega_arith) dB h10 hq hrw x₁₁ fun s₁₂ x₁₂ => ?_
    refine xs_step hp (k := 7) (by omega_arith) (by omega_arith) dB h10 hq hrw x₁₂ fun s₁₃ x₁₃ => ?_
    refine wp_add (op2_imm (by decide)) fun s₁₄ u₁₄ => wp_sub (op2_imm (by decide)) fun s₁₅ u₁₅ =>
      WP.block_nil ⟨by rw [u₁₅.mem, u₁₄.mem, ← mB']; exact x₁₃.frame, fun r h1 h2 h3 h4 => ?_,
        by rw [u₁₅.rd, u₁₄.rd, x₁₃.rd, rdB'], by rw [u₁₅.wr, u₁₄.wr, x₁₃.wr, wrB'],
        by rw [u₁₅.sp, u₁₄.sp, x₁₃.sp, spB'], fun ht => ?_, ?_⟩
    · rw [u₁₅.other _ h4, u₁₄.other _ h3, x₁₃.keep r h1, gB r h2]
    · rw [u₁₅.other _ (by decide), u₁₄.other _ (by decide), x₁₃.keep _ (by decide)]; exact kpB ht
    obtain e₁₀ : s₁₅.gpr .r10 = Sp + BitVec.ofNat 32 (32 * (g + 1)) := by
      rw [u₁₅.other _ (by decide), u₁₄.gpr, x₁₃.keep _ (by decide), h10]
      rw [BitVec.add_assoc, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, ← BitVec.ofNat_add]
      congr 2
    obtain e₁₁ : s₁₅.gpr .r11 = BitVec.ofNat 32 (n - 2 * (g + 1)) := by
      rw [u₁₅.gpr, u₁₄.other _ (by decide), x₁₃.keep _ (by decide), gB _ (by decide), hp.r11]
      bv_omega
    obtain d : DataInvG m₀ s₁₅.mem (State.addr Sp) (State.addr Tp) n (8 * (g + 1)) ks := by
      rw [u₁₅.mem, u₁₄.mem]; exact x₁₃.data
    by_cases hl : n - 2 * g = 2
    · exact .inl ⟨by rw [e₁₁, show n - 2 * (g + 1) = 0 by omega_arith]; rfl,
        dataInvG_mono d (by omega_arith) (by omega_arith)⟩
    · exact .inr ⟨by omega_arith, d, e₁₀, e₁₁⟩
  · -- The last block.
    obtain h1 : n - 2 * g = 1 := by simp at hb; omega_arith
    rw [xorTail_eq]
    simp only [List.append_assoc]
    refine xs_step hp (k := 0) (by omega_arith) (by omega_arith) dB h10 hq hrw x₀ fun s₆ x₆ => ?_
    refine xs_step hp (k := 1) (by omega_arith) (by omega_arith) dB h10 hq hrw x₆ fun s₇ x₇ => ?_
    refine xs_step hp (k := 2) (by omega_arith) (by omega_arith) dB h10 hq hrw x₇ fun s₈ x₈ => ?_
    refine xs_step hp (k := 3) (by omega_arith) (by omega_arith) dB h10 hq hrw x₈ fun s₉ x₉ => ?_
    refine wp_mov (op2_imm (by decide)) fun s₁₀ u₁₀ =>
      WP.block_nil ⟨by rw [u₁₀.mem, ← mB']; exact x₉.frame, fun r h1 h2 _ h4 => ?_,
        by rw [u₁₀.rd, x₉.rd, rdB'], by rw [u₁₀.wr, x₉.wr, wrB'], by rw [u₁₀.sp, x₉.sp, spB'],
        fun ht => ?_, .inl ⟨u₁₀.gpr, ?_⟩⟩
    · rw [u₁₀.other _ h4, x₉.keep r h1, gB r h2]
    · rw [u₁₀.other _ (by decide), x₉.keep _ (by decide)]; exact kpB ht
    · rw [u₁₀.mem]; exact dataInvG_mono x₉.data (by omega_arith) (by omega_arith)

/-- Out of place, the destination pointer advanced and stored back. -/
theorem dstStep_wp {s₃ s : State} (hp : XPre to m₀ b Sp Tp n g ks s₃) (hm : XMid to m₀ Sp Tp n g ks s₃ s)
    {is : List Instr} {P : State → Prop}
    (h : ∀ s', XDone to m₀ b Sp Tp n g ks s₃ s' → WP isa (.block is) s' P) :
    WP isa (.block (dstStep to ++ is)) s P := by
  obtain ⟨f, k, rd, wr, sp, hkp, hz⟩ := hm
  have hn := hp.fit
  have hnT := hp.fitT
  obtain fx : Frame (xRegions (State.addr b) (State.addr Tp) n) s₃.mem s.mem :=
    f.mono fun r hr => by simp at hr; simp [hr]
  cases to
  · refine h s ⟨fx, k, rd, wr, sp, ?_⟩
    rcases hz with h0 | ⟨h1, h2, h3, h4⟩
    · exact .inl h0
    · exact .inr ⟨h1, h2, h3, h4, fun h => nomatch h⟩
  · simp only [dstStep, ite_true, List.cons_append, List.nil_append]
    refine wp_add (op2_imm (by decide)) fun s₁ u₁ => ?_
    refine wp_stS (by rw [u₁.other _ (by decide), k _ (by decide) (by decide) (by decide) (by decide), hp.base])
      (by rw [u₁.wr, wr]; exact hp.scr) hp.fitB (by decide) fun s₂ u₂ => ?_
    obtain hslot : (⟨State.addr b + BitVec.ofNat 64 192, 4⟩ : Region).Contains
        (slotA (State.addr b) dstSlot) (32 / 8) := Region.contains_self _ _
    obtain fs : Frame [⟨State.addr b + BitVec.ofNat 64 192, 4⟩] s.mem s₂.mem := by
      rw [u₂.mem, u₁.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hslot
    obtain bS : ∀ i < 16 * n, s₂.mem (State.addr Sp + BitVec.ofNat 64 i) = s.mem (State.addr Sp + BitVec.ofNat 64 i) :=
      fun i hi => Frame.bytes (R := ⟨State.addr Sp, 16 * n⟩) fs (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.sepS.sub_right (VG.Offset.sub_base _ (by omega_arith))) (by simp only; omega_arith) hi
    obtain bT : ∀ i < 16 * n, s₂.mem (State.addr Tp + BitVec.ofNat 64 i) = s.mem (State.addr Tp + BitVec.ofNat 64 i) :=
      fun i hi => Frame.bytes (R := ⟨State.addr Tp, 16 * n⟩) fs (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.sepT.sub_right (VG.Offset.sub_base _ (by omega_arith))) (by simp only; omega_arith) hi
    obtain dd : ∀ {k}, DataInvG m₀ s.mem (State.addr Sp) (State.addr Tp) n k ks →
        DataInvG m₀ s₂.mem (State.addr Sp) (State.addr Tp) n k ks := fun hd i hi =>
      ⟨fun h1 => by rw [bT i hi]; exact (hd i hi).1 h1, fun h1 => by rw [bS i hi]; exact (hd i hi).2 h1⟩
    obtain g₂ : ∀ r, r ≠ kp → s₂.gpr r = s.gpr r := fun r hr => by rw [u₂.gpr, u₁.other _ hr]
    refine h s₂ ⟨fx.trans (fs.mono fun r hr => by simp at hr; simp [hr]),
      fun r h1 h2 h3 h4 => by rw [g₂ r h2, k r h1 h2 h3 h4], by rw [u₂.rd, u₁.rd, rd],
      by rw [u₂.wr, u₁.wr, wr], by rw [u₂.sp, u₁.sp, sp], ?_⟩
    rcases hz with ⟨h0, h1⟩ | ⟨h1, h2, h3, h4⟩
    · exact .inl ⟨by rw [g₂ _ (by decide), h0], dd h1⟩
    · refine .inr ⟨h1, dd h2, by rw [g₂ _ (by decide), h3], by rw [g₂ _ (by decide), h4], fun _ => ?_⟩
      rw [u₂.mem, u₁.mem, Mem.readW_writeW_self32, u₁.gpr, hkp rfl, BitVec.add_assoc,
        show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, ← BitVec.ofNat_add]
      congr 2

end Xor

/-! ## A group -/

/-- What the group loop runs with: `s₂` is the state after the round keys
are bitsliced, `b` the scratch buffer, `Sp` the source and `Tp` the
destination (`n` blocks; the same in place), `icb` the first counter block. -/
structure GSetup (to : Bool) (s₂ : State) (b Sp Tp : BitVec 32) (n R : Nat) (w : List Byte)
    (icb : Spec.Gcm.Block) : Prop where
  scr : (⟨State.addr b, 2048⟩ : Region) ∈ s₂.wr
  fit : b.toNat + 2048 ≤ 2 ^ 32
  src : (⟨State.addr Sp, 16 * n⟩ : Region) ∈ s₂.rd ++ s₂.wr
  dat : (⟨State.addr Tp, 16 * n⟩ : Region) ∈ s₂.wr
  fitS : Sp.toNat + 16 * n ≤ 2 ^ 32
  fitD : Tp.toNat + 16 * n ≤ 2 ^ 32
  mode : ModeOk to Sp Tp n
  sepS : Region.Disjoint ⟨State.addr Sp, 16 * n⟩ ⟨State.addr b, 2048⟩
  sep : Region.Disjoint ⟨State.addr Tp, 16 * n⟩ ⟨State.addr b, 2048⟩
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  keys : KeysAt s₂.mem (b + BitVec.ofNat 32 (lastKey - 32 * R)) R w
  words : ∀ k < 3, ∀ t < 4, ∀ j < 8,
    (cwW s₂.mem (State.addr b) k).getLsbD (8 * t + j) = icb.getLsbD (8 * (15 - (4 * k + t)) + j)

/-- The memory a group writes: the S-box's slots, slots 44–48 and the destination. -/
abbrev gRegions (B T : Addr) (n : Nat) : List Region :=
  [⟨B, 128⟩, ⟨B + BitVec.ofNat 64 176, 20⟩, ⟨T, 16 * n⟩]

/-- Before group `g`. -/
structure GInv (to : Bool) (m₀ : Mem) (s₂ : State) (b Sp Tp : BitVec 32) (n R : Nat) (w : List Byte)
    (icb : Spec.Gcm.Block) (g : Nat) (s : State) : Prop where
  hg : 2 * g < n
  r10 : s.gpr .r10 = Sp + BitVec.ofNat 32 (32 * g)
  r11 : s.gpr .r11 = BitVec.ofNat 32 (n - 2 * g)
  r12 : s.gpr .r12 = b + BitVec.ofNat 32 (lastKey - 32 * R)
  base : s.gpr sb = b
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  sp : s.sp = s₂.sp
  frame : Frame (gRegions (State.addr b) (State.addr Tp) n) s₂.mem s.mem
  num : numW s.mem (State.addr b) = icb.extractLsb' 0 32 + BitVec.ofNat 32 (2 * g)
  slot : to = true → s.mem.readW (slotA (State.addr b) dstSlot) 32 = Tp + BitVec.ofNat 32 (32 * g)
  data : DataInvG m₀ s.mem (State.addr Sp) (State.addr Tp) n (8 * g) (keyStream R w icb)

/-- After the last group. -/
structure GDone (m₀ : Mem) (s₂ : State) (b Sp Tp : BitVec 32) (n R : Nat) (w : List Byte)
    (icb : Spec.Gcm.Block) (s : State) : Prop where
  base : s.gpr sb = b
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  sp : s.sp = s₂.sp
  frame : Frame (gRegions (State.addr b) (State.addr Tp) n) s₂.mem s.mem
  data : DataInvG m₀ s.mem (State.addr Sp) (State.addr Tp) n (4 * n) (keyStream R w icb)

theorem scr_disj (B : Addr) {lx y ly : Nat} (h : lx ≤ y) (hy : y + ly ≤ 2048) :
    Region.Disjoint ⟨B, lx⟩ ⟨B + BitVec.ofNat 64 y, ly⟩ :=
  (VG.Offset.disjoint_base B h (by omega_arith)).symm

theorem scr_sub (B : Addr) {x lx : Nat} (h : x + lx ≤ 2048) :
    Region.Sub ⟨B + BitVec.ofNat 64 x, lx⟩ ⟨B, 2048⟩ :=
  VG.Offset.sub_base B h

theorem keysAt_frame {m m' : Mem} {b : BitVec 32} (hfit : b.toNat + 2048 ≤ 2 ^ 32) {R : Nat}
    {w : List Byte} {rs : List Region} (hR : R ≤ 14) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨State.addr b + 224, 480⟩ r)
    (h : KeysAt m (b + BitVec.ofNat 32 (lastKey - 32 * R)) R w) :
    KeysAt m' (b + BitVec.ofNat 32 (lastKey - 32 * R)) R w :=
  fun j hj => keyRel_congr (h j hj) fun k hk => hf.readW (key_contains hfit hR hj hk) hd (by decide)

theorem dataInv_frame {m₀ m m' : Mem} {D : Addr} {n k : Nat} {ks : Nat → Byte} {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r) (hn : 16 * n < 2 ^ 64)
    (h : DataInv m₀ m D n k ks) : DataInv m₀ m' D n k ks := fun i hi => by
  rw [← h i hi]
  exact hf.bytes (R := ⟨D, 16 * n⟩) hd (by simp only; omega_arith) hi

theorem dataInvG_frame {m₀ m m' : Mem} {S T : Addr} {n k : Nat} {ks : Nat → Byte} {rs : List Region}
    (hf : Frame rs m m') (hdS : ∀ r ∈ rs, Region.Disjoint ⟨S, 16 * n⟩ r)
    (hdT : ∀ r ∈ rs, Region.Disjoint ⟨T, 16 * n⟩ r) (hn : 16 * n < 2 ^ 64)
    (h : DataInvG m₀ m S T n k ks) : DataInvG m₀ m' S T n k ks := fun i hi =>
  ⟨fun h1 => by rw [hf.bytes (R := ⟨T, 16 * n⟩) hdT (by simp only; omega_arith) hi]; exact (h i hi).1 h1,
   fun h1 => by rw [hf.bytes (R := ⟨S, 16 * n⟩) hdS (by simp only; omega_arith) hi]; exact (h i hi).2 h1⟩

/-- Slots 44–47 lie in the slots a group writes. -/
theorem front_sub (B : Addr) :
    Region.Sub ⟨B + BitVec.ofNat 64 176, 16⟩ ⟨B + BitVec.ofNat 64 176, 20⟩ :=
  VG.Offset.sub _ (by omega_arith) (by omega_arith)

theorem front_frame (m : Mem) (B : Addr) (d l f : BitVec 32) :
    Frame [⟨B + BitVec.ofNat 64 176, 20⟩] m (frontMem m B d l f) := by
  obtain c : ∀ k, 44 ≤ k → k < 48 →
      (⟨B + BitVec.ofNat 64 176, 20⟩ : Region).Contains (slotA B k) (32 / 8) := by
    intro k h1 h2
    simp only [Region.Contains, slotA]
    rw [VG.Offset.add_sub_add B (show 176 ≤ 4 * k by omega_arith), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  exact ((((Frame.refl _ m).writeW (List.mem_singleton_self _) _ (c 45 (by omega_arith) (by omega_arith))).writeW
    (List.mem_singleton_self _) _ (c 46 (by omega_arith) (by omega_arith))).writeW (List.mem_singleton_self _) _
    (c 47 (by omega_arith) (by omega_arith))).writeW (List.mem_singleton_self _) _ (c 44 (by omega_arith) (by omega_arith))

theorem front_read (m : Mem) (B : Addr) (d l f : BitVec 32) :
    (frontMem m B d l f).readW (slotA B dSlot) 32 = d ∧
      (frontMem m B d l f).readW (slotA B lSlot) 32 = l ∧
      (frontMem m B d l f).readW (slotA B fkSlot) 32 = f ∧
      numW (frontMem m B d l f) B = numW m B + 2 ∧
      (frontMem m B d l f).readW (slotA B dstSlot) 32 = m.readW (slotA B dstSlot) 32 := by
  simp only [frontMem, numW]
  refine ⟨?_, ?_, ?_, Mem.readW_writeW_self32 _ _ _, ?_⟩
  · rw [readW_writeW_slot _ _ (by decide) (by decide) (by decide),
      readW_writeW_slot _ _ (by decide) (by decide) (by decide),
      readW_writeW_slot _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [readW_writeW_slot _ _ (by decide) (by decide) (by decide),
      readW_writeW_slot _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [readW_writeW_slot _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [readW_writeW_slot _ _ (by decide) (by decide) (by decide),
      readW_writeW_slot _ _ (by decide) (by decide) (by decide),
      readW_writeW_slot _ _ (by decide) (by decide) (by decide),
      readW_writeW_slot _ _ (by decide) (by decide) (by decide)]

theorem slot_disj_regions {b Dp : BitVec 32} {n : Nat}
    (hsep : Region.Disjoint ⟨State.addr Dp, 16 * n⟩ ⟨State.addr b, 2048⟩) {x lx : Nat}
    (h1 : 128 ≤ x) (h2 : x + lx ≤ 176 ∨ 196 ≤ x) (h3 : x + lx ≤ 2048) :
    ∀ r ∈ gRegions (State.addr b) (State.addr Dp) n,
      Region.Disjoint ⟨State.addr b + BitVec.ofNat 64 x, lx⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (scr_disj _ h1 h3).symm
  · exact off_disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  · exact (hsep.sub_right (scr_sub _ h3)).symm

theorem keys_disj_regions {b Dp : BitVec 32} {n : Nat}
    (hsep : Region.Disjoint ⟨State.addr Dp, 16 * n⟩ ⟨State.addr b, 2048⟩) :
    ∀ r ∈ gRegions (State.addr b) (State.addr Dp) n,
      Region.Disjoint ⟨State.addr b + 224, 480⟩ r :=
  slot_disj_regions hsep (x := 224) (lx := 480) (by omega_arith) (by omega_arith) (by omega_arith)

/-- One group: from before group `g`, to after the last group or before
group `g + 1`. -/
theorem group_ok {to : Bool} {m₀ : Mem} {s₂ : State} {b Sp Tp : BitVec 32} {n R : Nat} {w : List Byte}
    {icb : Spec.Gcm.Block} (hs : GSetup to s₂ b Sp Tp n R w icb) {g : Nat} {s : State}
    (hi : GInv to m₀ s₂ b Sp Tp n R w icb g s) :
    WP isa (groupG to) s fun s' => (Arm.eval .ne s' = some false ∧ GDone m₀ s₂ b Sp Tp n R w icb s') ∨
      (Arm.eval .ne s' = some true ∧ GInv to m₀ s₂ b Sp Tp n R w icb (g + 1) s') := by
  obtain hR : R ≤ 14 := by rcases hs.rounds with h | h | h <;> omega_arith
  have hfit := hs.fit
  have hfitD := hs.fitD
  have hfitS := hs.fitS
  obtain hscr : (⟨State.addr b, 2048⟩ : Region) ∈ s.wr := hi.wr ▸ hs.scr
  obtain dS : ∀ {x lx : Nat}, x + lx ≤ 2048 →
      Region.Disjoint ⟨State.addr Sp, 16 * n⟩ ⟨State.addr b + BitVec.ofNat 64 x, lx⟩ :=
    fun h => hs.sepS.sub_right (scr_sub _ h)
  obtain dT : ∀ {x lx : Nat}, x + lx ≤ 2048 →
      Region.Disjoint ⟨State.addr Tp, 16 * n⟩ ⟨State.addr b + BitVec.ofNat 64 x, lx⟩ :=
    fun h => hs.sep.sub_right (scr_sub _ h)
  unfold groupG
  refine WP.seq (front_wp hi.base hscr hfit fun s₁ hq₁ hkp₁ o₁ m₁ rd₁ wr₁ sp₁ => ?_)
  obtain hb₁ : s₁.gpr sb = b := (o₁ sb (by decide) (by decide)).trans hi.base
  obtain f₁ : Frame [⟨State.addr b + BitVec.ofNat 64 176, 20⟩] s.mem s₁.mem := by
    rw [m₁]; exact front_frame _ _ _ _ _
  obtain hf₁ : Frame (gRegions (State.addr b) (State.addr Tp) n) s₂.mem s₁.mem :=
    hi.frame.trans (f₁.mono fun r hr => by simp at hr; simp [hr])
  obtain hcw : ∀ k < 3, cwW s.mem (State.addr b) k = cwW s₂.mem (State.addr b) k := fun k hk =>
    hi.frame.readW (Region.contains_self _ _)
      (slot_disj_regions hs.sep (by simp [cW]; omega_arith) (by simp [cW]; omega_arith) (by simp [cW]; omega_arith))
      (by decide)
  obtain hp : EncPre s₁ R w :=
    ⟨by rw [hb₁, wr₁, hi.wr]; exact hs.scr, by rw [hb₁]; exact hfit, hs.rounds,
      by rw [hkp₁, hi.r12, hb₁],
      by rw [hkp₁, hi.r12]; exact keysAt_frame hfit hR hf₁ (keys_disj_regions hs.sep) hs.keys⟩
  obtain hin : InRel (Q s₁) (fun bb => ctrState icb (2 * g + bb)) :=
    ctr_inRel (W := fun k => cwW s.mem (State.addr b) k)
      (fun k hk => by rw [hcw k hk]; exact hs.words k hk) hi.num
      (fun bb hbb => ⟨fun k hk => (hq₁ bb hbb).1 k hk, (hq₁ bb hbb).2⟩)
  refine WP.seq (WP.mono (encrypt2_ok hp hin) fun s₃ ⟨hc₃, hin₃⟩ => ?_)
  have fr₃ := hc₃.frame
  rw [hb₁] at fr₃
  obtain hb₃ : s₃.gpr sb = b := hc₃.base.trans hb₁
  obtain hscr₃ : (⟨State.addr b, 2048⟩ : Region) ∈ s₃.wr := by rw [hc₃.wr, wr₁]; exact hscr
  obtain mslot : ∀ k, 45 ≤ k → k < 49 → s₃.mem.readW (slotA (State.addr b) k) 32 =
      s₁.mem.readW (slotA (State.addr b) k) 32 := fun k h1 h2 =>
    fr₃.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (scr_disj _ (by omega_arith) (by omega_arith)).symm)
      (by decide)
  obtain ⟨rd10, rd11, rd12, rnum, rdst⟩ := front_read s.mem (State.addr b) (s.gpr .r10) (s.gpr .r11)
    (s.gpr .r12)
  refine WP.seq ?_
  simp only [groupLoad, List.cons_append, List.nil_append]
  refine wp_ldS hb₃ hscr₃ hfit (by decide) fun s₄ u₄ => ?_
  refine wp_ldS (by rw [u₄.other _ (by decide), hb₃]) (by rw [u₄.wr]; exact hscr₃) hfit (by decide)
    fun s₅ u₅ => ?_
  refine wp_ldS (by rw [u₅.other _ (by decide), u₄.other _ (by decide), hb₃])
    (by rw [u₅.wr, u₄.wr]; exact hscr₃) hfit (by decide) fun s₆ u₆ => ?_
  obtain e10 : s₆.gpr .r10 = Sp + BitVec.ofNat 32 (32 * g) := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, mslot dSlot (by decide) (by decide), m₁,
      rd10, hi.r10]
  obtain e11 : s₆.gpr .r11 = BitVec.ofNat 32 (n - 2 * g) := by
    rw [u₆.other _ (by decide), u₅.gpr, u₄.mem, mslot lSlot (by decide) (by decide), m₁, rd11, hi.r11]
  obtain e12 : s₆.gpr .r12 = b + BitVec.ofNat 32 (lastKey - 32 * R) := by
    rw [u₆.gpr, u₅.mem, u₄.mem, mslot fkSlot (by decide) (by decide), m₁, rd12, hi.r12]
  obtain mm₆ : s₆.mem = s₃.mem := by rw [u₆.mem, u₅.mem, u₄.mem]
  obtain gq₆ : ∀ i < 8, s₆.gpr (q i) = s₃.gpr (q i) := fun i hi' => by
    have : q i ≠ .r10 ∧ q i ≠ .r11 ∧ q i ≠ .r12 := by revert hi'; revert i; decide
    rw [u₆.other _ this.2.2, u₅.other _ this.2.1, u₄.other _ this.1]
  obtain d384S : ∀ r ∈ [(⟨State.addr b, 128⟩ : Region)], Region.Disjoint ⟨State.addr Sp, 16 * n⟩ r := by
    simpa using hs.sepS.sub_right (Region.sub_prefix (by omega_arith))
  obtain d384T : ∀ r ∈ [(⟨State.addr b, 128⟩ : Region)], Region.Disjoint ⟨State.addr Tp, 16 * n⟩ r := by
    simpa using hs.sep.sub_right (Region.sub_prefix (by omega_arith))
  obtain hx : XPre to m₀ b Sp Tp n g (keyStream R w icb) s₆ :=
    { hg := hi.hg, fit := hfitS, fitT := hfitD
      src := by rw [u₆.rd, u₅.rd, u₄.rd, hc₃.rd, rd₁, hi.rd, u₆.wr, u₅.wr, u₄.wr, hc₃.wr, wr₁, hi.wr]; exact hs.src
      dat := by rw [u₆.wr, u₅.wr, u₄.wr, hc₃.wr, wr₁, hi.wr]; exact hs.dat
      mode := hs.mode
      base := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), hb₃]
      scr := by rw [u₆.wr, u₅.wr, u₄.wr]; exact hscr₃
      fitB := hfit, sepS := hs.sepS, sepT := hs.sep
      slot := fun ht => by
        rw [mm₆, mslot dstSlot (by decide) (by decide), m₁, rdst, hi.slot ht]
      r10 := e10, r11 := e11
      data := by
        rw [mm₆]
        refine dataInvG_frame fr₃ d384S d384T (by omega_arith)
          (dataInvG_frame f₁ (by simpa using dS (by omega_arith)) (by simpa using dT (by omega_arith))
            (by omega_arith) hi.data)
      ks := fun k hk t ht => by rw [gq₆ _ (by omega_arith)]; exact ks_of_inRel hin₃ hk ht }
  refine WP.mono (xorPhase_wp hx) fun s₇ h₇ => WP.seq (WP.mono h₇ fun s₇' hm => ?_)
  refine dstStep_wp hx hm fun s₈ hd₈ => ?_
  obtain ⟨f₈, o₈, rd₈, wr₈, sp₈, hz⟩ := hd₈
  refine wp_cmp (op2_imm (by decide)) fun s₉ f₉ z₉ => WP.block_nil ?_
  obtain keep : ∀ r, r ∉ layerWrites → r ≠ kp → s₉.gpr r = s.gpr r := by
    intro r h1 h2
    have : r ≠ .lr ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r12 := by revert h1 h2; cases r <;> decide
    rw [f₉.gpr, o₈ r this.1 h2 this.2.1 this.2.2.1, u₆.other _ this.2.2.2, u₅.other _ this.2.2.1,
      u₄.other _ this.2.1, hc₃.keep r h1 h2, o₁ r h1 h2]
  obtain base' : s₉.gpr sb = b := (keep sb (by decide) (by decide)).trans hi.base
  obtain rd' : s₉.rd = s₂.rd := by rw [f₉.rd, rd₈, u₆.rd, u₅.rd, u₄.rd, hc₃.rd, rd₁, hi.rd]
  obtain wr' : s₉.wr = s₂.wr := by rw [f₉.wr, wr₈, u₆.wr, u₅.wr, u₄.wr, hc₃.wr, wr₁, hi.wr]
  obtain sp' : s₉.sp = s₂.sp := by rw [f₉.sp, sp₈, u₆.sp, u₅.sp, u₄.sp, hc₃.sp, sp₁, hi.sp]
  obtain frame' : Frame (gRegions (State.addr b) (State.addr Tp) n) s₂.mem s₉.mem := by
    rw [f₉.mem]
    refine hf₁.trans ((fr₃.mono fun r hr => by simp at hr; simp [hr]).trans ?_)
    rw [← mm₆]
    exact f₈.sub fun r hr => by
      simp only [xRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨State.addr b + BitVec.ofNat 64 176, 20⟩, by simp,
          VG.Offset.sub _ (by omega_arith) (by omega_arith)⟩
  obtain ev : Arm.eval .ne s₉ = some (!(s₈.gpr .r11 == 0)) := by
    have e0 : ∀ x : BitVec 32, x - (0 : BitVec 32) = x := BitVec.sub_zero
    simp only [Arm.eval, z₉, e0]
  rcases hz with ⟨z, d⟩ | ⟨h4, d, x10, x11, xs⟩
  · exact .inl ⟨by rw [ev, z]; rfl, base', rd', wr', sp', frame', by rw [f₉.mem]; exact d⟩
  · refine .inr ⟨?_, ⟨by omega_arith, by rw [f₉.gpr]; exact x10, by rw [f₉.gpr]; exact x11,
      by rw [f₉.gpr, o₈ _ (by decide) (by decide) (by decide) (by decide), e12], base', rd', wr', sp',
      frame', ?_, fun ht => by rw [f₉.mem]; exact xs ht, by rw [f₉.mem]; exact d⟩⟩
    · have hne : BitVec.ofNat 32 (n - 2 * (g + 1)) ≠ 0 := by
        intro h; have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
        simp at this; omega_arith
      rw [ev, x11]; simpa using hne
    · have e₁ : numW s₈.mem (State.addr b) = numW s₆.mem (State.addr b) :=
        f₈.readW (Region.contains_self _ _)
          (fun r hr => by
            simp only [xRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · exact (hs.sep.sub_right (scr_sub (x := 176) (lx := 4) _ (by decide))).symm
            · exact off_disjoint (x := 176) (lx := 4) _ (by omega_arith) (by omega_arith) (by omega_arith))
          (by decide)
      rw [f₉.mem]
      obtain e₂ : numW s₃.mem (State.addr b) = numW s₁.mem (State.addr b) :=
        fr₃.readW (Region.contains_self _ _)
          (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact (scr_disj (lx := 128) (y := 176) (ly := 4) _ (by omega_arith) (by omega_arith)).symm) (by decide)
      rw [e₁, mm₆, e₂, m₁, rnum, hi.num, BitVec.add_assoc]
      congr 1
      bv_omega

/-- The loop over the groups. -/
theorem groups_ok {to : Bool} {m₀ : Mem} {s₂ : State} {b Sp Tp : BitVec 32} {n R : Nat} {w : List Byte}
    {icb : Spec.Gcm.Block} (hs : GSetup to s₂ b Sp Tp n R w icb) {s : State}
    (hi : GInv to m₀ s₂ b Sp Tp n R w icb 0 s) :
    WP isa (.loop (groupG to) .ne) s (GDone m₀ s₂ b Sp Tp n R w icb) := by
  refine WP.loop (M := isa) (fun k s => ∃ g, k = n - 2 * g ∧ GInv to m₀ s₂ b Sp Tp n R w icb g s)
    (fun k s ⟨g, hk, hg⟩ => WP.mono (group_ok hs hg) fun s' h => ?_) n s ⟨0, by omega_arith, hi⟩
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨z, d⟩
  · exact .inr ⟨z, n - 2 * (g + 1), by have := hg.hg; omega_arith, g + 1, rfl, d⟩

end VG.Proof.Aes.Arm
