module

public import VerifiedGarbage.Spec.Aes
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Bitslice.Table
public import VerifiedGarbage.Proof.Aes.InvRounds
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Bitsliced words and AES states

Slice `j` (a word, `W j`) holds bit `j` of every byte. A word of `16 B` bits
holds `B` states: the byte of row `r` and column `c` of state `k` is at
position `k + B (c + 4 r)` (`posAt`). In *form 1*, the form of states that
ShiftRows was left out of, the byte of column `c` is at column `c + r`
instead. `BsRel B f W S` says that the slices `W` hold the states `S` in
form `f`; the lemmas say what the layers do to it, the linear ones given as
the (slice, position) pairs each output bit XORs.
-/

@[expose] public section

namespace VG.Proof.Aes

open VG VG.Bitslice

/-! ## Bits, bytes and slices -/

theorem byte_ext {a b : Byte} (h : ∀ j < 8, a.getLsbD j = b.getLsbD j) : a = b :=
  BitVec.eq_of_getLsbD_eq h

theorem getD_eq {α : Type} {n : Nat} (v : Vector α n) {i : Nat} {d : α} (hi : i < n) :
    v.getD i d = v[i] := by
  simp only [Vector.getD, Array.getD, Vector.size_toArray, hi, dite_true]; rfl

/-- The byte at position `p` of the slices. -/
def bsByte {w : Nat} (W : Nat → BitVec w) (p : Nat) : Byte := ofBits 8 fun j => (W j).getLsbD p

theorem getLsbD_bsByte {w : Nat} (W : Nat → BitVec w) (p : Nat) {j : Nat} (hj : j < 8) :
    (bsByte W p).getLsbD j = (W j).getLsbD p := by
  rw [bsByte, getLsbD_ofBits, decide_eq_true hj, Bool.true_and]

/-- The XOR of the bits given as (word, position). -/
def termsXor {w : Nat} (W : Nat → BitVec w) (l : List (Nat × Nat)) : Bool :=
  l.foldr (fun t b => (W t.1).getLsbD t.2 ^^ b) false

theorem xorBits_map {w : Nat} (W : Nat → BitVec w) (l : List (Nat × Nat)) (h : ∀ t ∈ l, t.2 < w) :
    xorBits W (l.map fun t => w * t.1 + t.2) = termsXor W l := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    have ht := h t List.mem_cons_self
    have := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [xorBits, List.map_cons, List.foldr_cons, termsXor] at this ⊢
    rw [this, bitOf_word W t.1 t.2 ht]

/-! ## The layout -/

/-- The position of byte `n` (`r + 4 c`) of state `k` in form `f`. -/
def posAt (B : Nat) (f : Bool) (n k : Nat) : Nat :=
  k + B * ((if f then (n / 4 + n % 4) % 4 else n / 4) + 4 * (n % 4))

/-- The byte at position `p` in form `f`, of state `p % B`. -/
def byteAt (B : Nat) (f : Bool) (p : Nat) : Nat :=
  p / B / 4 + 4 * (if f then (p / B % 4 + 4 - p / B / 4) % 4 else p / B % 4)

def BsRel {w : Nat} (B : Nat) (f : Bool) (W : Nat → BitVec w) (S : Nat → Spec.Aes.State) : Prop :=
  ∀ j < 8, ∀ n < 16, ∀ k < B, (W j).getLsbD (posAt B f n k) = ((S k).getD n 0).getLsbD j

/-- The grid's facts, which a finite check proves. -/
theorem grid : ∀ f : Bool, ∀ n < 16,
    (if f then (n / 4 + n % 4) % 4 else n / 4) + 4 * (n % 4) < 16 ∧
    (let g := (if f then (n / 4 + n % 4) % 4 else n / 4) + 4 * (n % 4)
     g / 4 + 4 * (if f then (g % 4 + 4 - g / 4) % 4 else g % 4) = n) := by decide

theorem posAt_lt {B : Nat} (f : Bool) {n k : Nat} (hn : n < 16) (hk : k < B) : posAt B f n k < 16 * B := by
  have h := (grid f n hn).1
  unfold posAt
  generalize (if f then (n / 4 + n % 4) % 4 else n / 4) + 4 * (n % 4) = g at h ⊢
  have : B * (g + 1) ≤ B * 16 := Nat.mul_le_mul_left _ h
  rw [Nat.mul_add] at this
  omega

theorem posAt_div {B : Nat} (f : Bool) (n : Nat) {k : Nat} (hk : k < B) :
    posAt B f n k / B = (if f then (n / 4 + n % 4) % 4 else n / 4) + 4 * (n % 4) := by
  rw [posAt, Nat.add_comm, Nat.mul_add_div (Nat.zero_lt_of_lt hk), Nat.div_eq_of_lt hk, Nat.add_zero]

theorem posAt_mod {B : Nat} (f : Bool) (n : Nat) {k : Nat} (hk : k < B) : posAt B f n k % B = k := by
  rw [posAt, Nat.add_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hk]

theorem byteAt_posAt {B : Nat} (f : Bool) {n k : Nat} (hn : n < 16) (hk : k < B) :
    byteAt B f (posAt B f n k) = n := by
  simp only [byteAt, posAt_div f n hk]
  exact (grid f n hn).2

theorem BsRel.congr {w B : Nat} {f : Bool} {W : Nat → BitVec w} {S S' : Nat → Spec.Aes.State}
    (h : BsRel B f W S) (hS : ∀ k < B, S k = S' k) : BsRel B f W S' :=
  fun j hj n hn k hk => by rw [h j hj n hn k hk, hS k hk]

theorem BsRel.congrW {w B : Nat} {f : Bool} {W W' : Nat → BitVec w} {S : Nat → Spec.Aes.State}
    (h : BsRel B f W S) (hW : ∀ j < 8, W j = W' j) : BsRel B f W' S :=
  fun j hj n hn k hk => by rw [← hW j hj, h j hj n hn k hk]

theorem BsRel.byte {w B : Nat} {f : Bool} {W : Nat → BitVec w} {S : Nat → Spec.Aes.State}
    (h : BsRel B f W S) {n k : Nat} (hn : n < 16) (hk : k < B) :
    bsByte W (posAt B f n k) = (S k).getD n 0 :=
  byte_ext fun j hj => by rw [getLsbD_bsByte _ _ hj, h j hj n hn k hk]

/-- The bytes of a `Vector.ofFn` state. -/
theorem getD_ofFn (g : Fin 16 → Byte) {n : Nat} (hn : n < 16) :
    (Vector.ofFn g : Spec.Aes.State).getD n 0 = g ⟨n, hn⟩ := by
  rw [getD_eq _ hn, Vector.getElem_ofFn]

theorem getD_map (g : Byte → Byte) (s : Spec.Aes.State) {n : Nat} (hn : n < 16) :
    (s.map g : Spec.Aes.State).getD n 0 = g (s.getD n 0) := by
  rw [getD_eq _ hn, getD_eq _ hn, Vector.getElem_map]

theorem state_ext {s t : Spec.Aes.State} (h : ∀ n < 16, s.getD n 0 = t.getD n 0) : s = t :=
  Vector.ext fun n hn => by
    have := h n hn
    rwa [getD_eq _ hn, getD_eq _ hn] at this

/-! ## The layers -/

/-- A layer that maps every byte by `g`. -/
theorem BsRel.map {w B : Nat} {f : Bool} {W W' : Nat → BitVec w} {S : Nat → Spec.Aes.State}
    (h : BsRel B f W S) (g : Byte → Byte)
    (hW : ∀ j < 8, ∀ p < 16 * B, (W' j).getLsbD p = (g (bsByte W p)).getLsbD j) :
    BsRel B f W' fun k => (S k).map g := fun j hj n hn k hk => by
  rw [hW j hj _ (posAt_lt f hn hk), h.byte hn hk, getD_map g _ hn]

/-- ShiftRows, left out: form 0 of the states is form 1 of the shifted ones. -/
theorem BsRel.skipShift {w B : Nat} {W : Nat → BitVec w} {S : Nat → Spec.Aes.State}
    (h : BsRel B false W S) : BsRel B true W fun k => Spec.Aes.shiftRows (S k) :=
  fun j hj n hn k hk => by
    have e : ∀ n < 16, (n / 4 + n % 4) % 4 + 4 * (n % 4) =
        (n % 4 + 4 * ((n / 4 + n % 4) % 4)) / 4 + 4 * ((n % 4 + 4 * ((n / 4 + n % 4) % 4)) % 4) ∧
        n % 4 + 4 * ((n / 4 + n % 4) % 4) < 16 := by decide
    have := h j hj (n % 4 + 4 * ((n / 4 + n % 4) % 4)) (e n hn).2 k hk
    simp only [posAt, Bool.false_eq_true, ite_false, ite_true] at this ⊢
    rw [(e n hn).1, this, Spec.Aes.shiftRows, getD_ofFn _ hn]

/-- InvShiftRows, left out: form 1 of the states is form 0 of the unshifted ones. -/
theorem BsRel.skipInvShift {w B : Nat} {W : Nat → BitVec w} {S : Nat → Spec.Aes.State}
    (h : BsRel B true W S) : BsRel B false W fun k => Spec.Aes.invShiftRows (S k) :=
  fun j hj n hn k hk => by
    have e : ∀ n < 16, n / 4 + 4 * (n % 4) =
        ((n % 4 + 4 * ((n / 4 + 4 - n % 4) % 4)) / 4 + (n % 4 + 4 * ((n / 4 + 4 - n % 4) % 4)) % 4) % 4 +
          4 * ((n % 4 + 4 * ((n / 4 + 4 - n % 4) % 4)) % 4) ∧
        n % 4 + 4 * ((n / 4 + 4 - n % 4) % 4) < 16 := by decide
    have := h j hj (n % 4 + 4 * ((n / 4 + 4 - n % 4) % 4)) (e n hn).2 k hk
    simp only [posAt, Bool.false_eq_true, ite_false, ite_true] at this ⊢
    rw [(e n hn).1, this, Spec.Aes.invShiftRows, getD_ofFn _ hn]

/-- The source, in a word's 16 groups, of ShiftRows done twice: the odd rows
move by two columns. -/
def sr2Src (B p : Nat) : Nat := p % B + B * ((p / B % 4 + 2 * (p / B / 4)) % 4 + 4 * (p / B / 4))

/-- ShiftRows twice. -/
def sr2T (B j p : Nat) : List (Nat × Nat) := [(j, sr2Src B p)]

theorem BsRel.sr2 {w B : Nat} {W W' : Nat → BitVec w} {S : Nat → Spec.Aes.State}
    (h : BsRel B true W S)
    (hW : ∀ j < 8, ∀ p < 16 * B, (W' j).getLsbD p = termsXor W (sr2T B j p)) :
    BsRel B false W' fun k => Spec.Aes.shiftRows (S k) := fun j hj n hn k hk => by
  have e : ∀ n < 16, (((n / 4 + 4 * (n % 4)) % 4 + 2 * ((n / 4 + 4 * (n % 4)) / 4)) % 4 + 4 * ((n / 4 + 4 * (n % 4)) / 4)) =
      ((n % 4 + 4 * ((n / 4 + n % 4) % 4)) / 4 + (n % 4 + 4 * ((n / 4 + n % 4) % 4)) % 4) % 4 +
        4 * ((n % 4 + 4 * ((n / 4 + n % 4) % 4)) % 4) ∧ n % 4 + 4 * ((n / 4 + n % 4) % 4) < 16 := by decide
  rw [hW j hj _ (posAt_lt false hn hk)]
  simp only [sr2T, termsXor, List.foldr_cons, List.foldr_nil, Bool.xor_false, sr2Src, posAt_mod false n hk,
    posAt_div false n hk, Bool.false_eq_true, ite_false]
  have := h j hj (n % 4 + 4 * ((n / 4 + n % 4) % 4)) (e n hn).2 k hk
  simp only [posAt, ite_true] at this
  rw [(e n hn).1, this, Spec.Aes.shiftRows, getD_ofFn _ hn]

theorem BsRel.invSr2 {w B : Nat} {W W' : Nat → BitVec w} {S : Nat → Spec.Aes.State}
    (h : BsRel B false W S)
    (hW : ∀ j < 8, ∀ p < 16 * B, (W' j).getLsbD p = termsXor W (sr2T B j p)) :
    BsRel B true W' fun k => Spec.Aes.invShiftRows (S k) := fun j hj n hn k hk => by
  have e : ∀ n < 16, ((((n / 4 + n % 4) % 4 + 4 * (n % 4)) % 4 + 2 * (((n / 4 + n % 4) % 4 + 4 * (n % 4)) / 4)) % 4 +
        4 * (((n / 4 + n % 4) % 4 + 4 * (n % 4)) / 4)) =
      (n % 4 + 4 * ((n / 4 + 4 - n % 4) % 4)) / 4 + 4 * ((n % 4 + 4 * ((n / 4 + 4 - n % 4) % 4)) % 4) ∧
      n % 4 + 4 * ((n / 4 + 4 - n % 4) % 4) < 16 := by decide
  rw [hW j hj _ (posAt_lt true hn hk)]
  simp only [sr2T, termsXor, List.foldr_cons, List.foldr_nil, Bool.xor_false, sr2Src, posAt_mod true n hk,
    posAt_div true n hk, ite_true]
  have := h j hj (n % 4 + 4 * ((n / 4 + 4 - n % 4) % 4)) (e n hn).2 k hk
  simp only [posAt, Bool.false_eq_true, ite_false] at this
  rw [(e n hn).1, this, Spec.Aes.invShiftRows, getD_ofFn _ hn]

/-! ### MixColumns and its inverse -/

/-- The bits of a byte `a` whose XOR is bit `j` of `c • a`. -/
def mulTerms (c j : Nat) : List Nat :=
  (List.range 8).filter fun i => (Spec.Aes.mul (BitVec.ofNat 8 c) (1 <<< i)).getLsbD j

theorem mulTerms_ok : ∀ c ∈ [0x02, 0x03, 0x01, 0x0e, 0x0b, 0x0d, 0x09], ∀ a : Byte, ∀ j < 8,
    (Spec.Aes.mul (BitVec.ofNat 8 c) a).getLsbD j = (mulTerms c j).foldr (fun i b => a.getLsbD i ^^ b) false := by
  decide +kernel

/-- The byte `i` rows on in the column of byte `n`. -/
def down (n i : Nat) : Nat := (n % 4 + i) % 4 + 4 * (n / 4)

/-- MixColumns with the coefficients `cs`, of a row's own byte and the next
rows': slice `j`, position `p`, of states in form `f`. -/
def mixT (cs : List Nat) (B : Nat) (f : Bool) (j p : Nat) : List (Nat × Nat) :=
  (List.range 4).flatMap fun i =>
    (mulTerms (cs.getD i 0) j).map fun b => (b, posAt B f (down (byteAt B f p) i) (p % B))

def mcCoeffs : List Nat := [0x02, 0x03, 0x01, 0x01]
def invMcCoeffs : List Nat := [0x0e, 0x0b, 0x0d, 0x09]

theorem termsXor_append {w : Nat} (W : Nat → BitVec w) (l l' : List (Nat × Nat)) :
    termsXor W (l ++ l') = (termsXor W l ^^ termsXor W l') := by
  induction l with
  | nil => simp [termsXor]
  | cons t l ih => simp only [termsXor, List.cons_append, List.foldr_cons] at ih ⊢; rw [ih, Bool.xor_assoc]

theorem termsXor_row {w B : Nat} {f : Bool} {W : Nat → BitVec w} {S : Nat → Spec.Aes.State} (h : BsRel B f W S)
    {m k : Nat} (hm : m < 16) (hk : k < B) (l : List Nat) (hl : ∀ b ∈ l, b < 8) :
    termsXor W (l.map fun b => (b, posAt B f m k)) =
      l.foldr (fun i b => ((S k).getD m 0).getLsbD i ^^ b) false := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    simp only [termsXor, List.map_cons, List.foldr_cons] at ih ⊢
    rw [ih fun x hx => hl x (List.mem_cons_of_mem _ hx), h t (hl t List.mem_cons_self) m hm k hk]

theorem mulTerms_lt (c j : Nat) : ∀ b ∈ mulTerms c j, b < 8 := fun _ hb =>
  List.mem_range.mp (List.mem_filter.mp hb).1

theorem down_lt {n i : Nat} (hn : n < 16) : down n i < 16 := by unfold down; omega

/-- What the layer gives, byte by byte. -/
theorem mixT_bit {w B : Nat} {f : Bool} {W : Nat → BitVec w} {S : Nat → Spec.Aes.State} (h : BsRel B f W S)
    (cs : List Nat) (hc : ∀ i < 4, cs.getD i 0 ∈ [0x02, 0x03, 0x01, 0x0e, 0x0b, 0x0d, 0x09])
    {j n k : Nat} (hj : j < 8) (hn : n < 16) (hk : k < B) :
    termsXor W (mixT cs B f j (posAt B f n k)) =
      (Spec.Aes.mul (BitVec.ofNat 8 (cs.getD 0 0)) ((S k).getD (down n 0) 0) ^^^
       Spec.Aes.mul (BitVec.ofNat 8 (cs.getD 1 0)) ((S k).getD (down n 1) 0) ^^^
       Spec.Aes.mul (BitVec.ofNat 8 (cs.getD 2 0)) ((S k).getD (down n 2) 0) ^^^
       Spec.Aes.mul (BitVec.ofNat 8 (cs.getD 3 0)) ((S k).getD (down n 3) 0)).getLsbD j := by
  simp only [mixT, show List.range 4 = [0, 1, 2, 3] from rfl, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, termsXor_append, byteAt_posAt f hn hk, posAt_mod f n hk, BitVec.getLsbD_xor]
  rw [termsXor_row h (down_lt hn) hk _ (mulTerms_lt _ _), termsXor_row h (down_lt hn) hk _ (mulTerms_lt _ _),
    termsXor_row h (down_lt hn) hk _ (mulTerms_lt _ _), termsXor_row h (down_lt hn) hk _ (mulTerms_lt _ _),
    mulTerms_ok _ (hc 0 (by decide)) _ j hj, mulTerms_ok _ (hc 1 (by decide)) _ j hj,
    mulTerms_ok _ (hc 2 (by decide)) _ j hj, mulTerms_ok _ (hc 3 (by decide)) _ j hj]
  simp only [Bool.xor_assoc]

theorem mul_one_byte : ∀ a : Byte, Spec.Aes.mul 1 a = a := by decide +kernel

theorem BsRel.mixColumns {w B : Nat} {f : Bool} {W W' : Nat → BitVec w} {S : Nat → Spec.Aes.State}
    (h : BsRel B f W S)
    (hW : ∀ j < 8, ∀ p < 16 * B, (W' j).getLsbD p = termsXor W (mixT mcCoeffs B f j p)) :
    BsRel B f W' fun k => Spec.Aes.mixColumns (S k) := fun j hj n hn k hk => by
  show _ = ((Spec.Aes.mixColumns (S k)).getD n 0).getLsbD j
  rw [hW j hj _ (posAt_lt f hn hk), mixT_bit h mcCoeffs (by decide) hj hn hk, Spec.Aes.mixColumns, getD_ofFn _ hn]
  simp only [mcCoeffs, List.getD_cons_zero, List.getD_cons_succ, down, mul_one_byte,
    show (BitVec.ofNat 8 1) = (1 : Byte) from rfl]
  rfl

theorem BsRel.invMixColumns {w B : Nat} {f : Bool} {W W' : Nat → BitVec w} {S : Nat → Spec.Aes.State}
    (h : BsRel B f W S)
    (hW : ∀ j < 8, ∀ p < 16 * B, (W' j).getLsbD p = termsXor W (mixT invMcCoeffs B f j p)) :
    BsRel B f W' fun k => Spec.Aes.invMixColumns (S k) := fun j hj n hn k hk => by
  show _ = ((Spec.Aes.invMixColumns (S k)).getD n 0).getLsbD j
  rw [hW j hj _ (posAt_lt f hn hk), mixT_bit h invMcCoeffs (by decide) hj hn hk, Spec.Aes.invMixColumns, getD_ofFn _ hn]
  rfl

/-! ### Round keys -/

/-- The state whose bytes are the round key's. -/
theorem getD_rkState (rk : List Byte) {n : Nat} (hn : n < 16) : (rkState rk).getD n 0 = rk.getD n 0 := by
  rw [rkState, getD_ofFn _ hn]

theorem BsRel.addRoundKey {w B : Nat} {f : Bool} {W K W' : Nat → BitVec w} {S : Nat → Spec.Aes.State}
    {rk : Nat → List Byte} (h : BsRel B f W S) (hK : BsRel B f K fun k => rkState (rk k))
    (hW : ∀ j < 8, ∀ p < 16 * B, (W' j).getLsbD p = ((W j).getLsbD p ^^ (K j).getLsbD p)) :
    BsRel B f W' fun k => Spec.Aes.addRoundKey (S k) (rk k) := fun j hj n hn k hk => by
  show _ = ((Spec.Aes.addRoundKey (S k) (rk k)).getD n 0).getLsbD j
  rw [hW j hj _ (posAt_lt f hn hk), h j hj n hn k hk, hK j hj n hn k hk, getD_rkState _ hn,
    Spec.Aes.addRoundKey, getD_ofFn _ hn, BitVec.getLsbD_xor]

/-! ### The S-box's constant, added to the round keys -/

/-- `{63}` added to every byte. -/
def c63 (s : Spec.Aes.State) : Spec.Aes.State := s.map (· ^^^ 0x63)

/-- A round key with `{63}` added to every byte. -/
def rk63 (rk : List Byte) : List Byte := rk.map (· ^^^ 0x63)

/-- The S-box without its constant. -/
def sbox0 (b : Byte) : Byte := Spec.Aes.sbox b ^^^ 0x63

theorem mc63 : ∀ c ∈ [0x02, 0x03, 0x01, 0x0e, 0x0b, 0x0d, 0x09], ∀ a : Byte,
    Spec.Aes.mul (BitVec.ofNat 8 c) (a ^^^ 0x63) =
      Spec.Aes.mul (BitVec.ofNat 8 c) a ^^^ Spec.Aes.mul (BitVec.ofNat 8 c) 0x63 := by decide +kernel

theorem getD_c63 (s : Spec.Aes.State) {n : Nat} (hn : n < 16) : (c63 s).getD n 0 = s.getD n 0 ^^^ 0x63 :=
  getD_map _ s hn

theorem shiftRows_c63 (s : Spec.Aes.State) : Spec.Aes.shiftRows (c63 s) = c63 (Spec.Aes.shiftRows s) :=
  state_ext fun n hn => by
    rw [getD_c63 _ hn, Spec.Aes.shiftRows, Spec.Aes.shiftRows, getD_ofFn _ hn, getD_ofFn _ hn,
      getD_c63 _ (by dsimp only; omega)]

theorem invShiftRows_c63 (s : Spec.Aes.State) :
    Spec.Aes.invShiftRows (c63 s) = c63 (Spec.Aes.invShiftRows s) :=
  state_ext fun n hn => by
    rw [getD_c63 _ hn, Spec.Aes.invShiftRows, Spec.Aes.invShiftRows, getD_ofFn _ hn, getD_ofFn _ hn,
      getD_c63 _ (by dsimp only; omega)]

theorem xor_consts (a b c d p q : Byte) :
    (a ^^^ (p ^^^ q)) ^^^ (b ^^^ p) ^^^ (c ^^^ q) ^^^ (d ^^^ q) = (a ^^^ b ^^^ c ^^^ d) ^^^ q := by
  apply byte_ext
  intro j _
  simp only [BitVec.getLsbD_xor]
  exact (by decide : ∀ a b c d p q : Bool, (((((a ^^ (p ^^ q)) ^^ (b ^^ p)) ^^ (c ^^ q)) ^^ (d ^^ q))) =
    ((((a ^^ b) ^^ c) ^^ d) ^^ q)) _ _ _ _ _ _

theorem mc2 (a : Byte) : Spec.Aes.mul 0x02 (a ^^^ 0x63) = Spec.Aes.mul 0x02 a ^^^ Spec.Aes.mul 0x02 0x63 := mc63 2 (by decide) a
theorem mc3 (a : Byte) : Spec.Aes.mul 0x03 (a ^^^ 0x63) = Spec.Aes.mul 0x03 a ^^^ Spec.Aes.mul 0x03 0x63 := mc63 3 (by decide) a
theorem mce (a : Byte) : Spec.Aes.mul 0x0e (a ^^^ 0x63) = Spec.Aes.mul 0x0e a ^^^ Spec.Aes.mul 0x0e 0x63 := mc63 14 (by decide) a
theorem mcb (a : Byte) : Spec.Aes.mul 0x0b (a ^^^ 0x63) = Spec.Aes.mul 0x0b a ^^^ Spec.Aes.mul 0x0b 0x63 := mc63 11 (by decide) a
theorem mcd (a : Byte) : Spec.Aes.mul 0x0d (a ^^^ 0x63) = Spec.Aes.mul 0x0d a ^^^ Spec.Aes.mul 0x0d 0x63 := mc63 13 (by decide) a
theorem mc9 (a : Byte) : Spec.Aes.mul 0x09 (a ^^^ 0x63) = Spec.Aes.mul 0x09 a ^^^ Spec.Aes.mul 0x09 0x63 := mc63 9 (by decide) a

theorem xor_consts4 (a b c d p q r s t : Byte) (h : p ^^^ q ^^^ r ^^^ s = t) :
    (a ^^^ p) ^^^ (b ^^^ q) ^^^ (c ^^^ r) ^^^ (d ^^^ s) = (a ^^^ b ^^^ c ^^^ d) ^^^ t := by
  subst h
  apply byte_ext
  intro j _
  simp only [BitVec.getLsbD_xor]
  exact (by decide : ∀ a b c d p q r s : Bool, ((((a ^^ p) ^^ (b ^^ q)) ^^ (c ^^ r)) ^^ (d ^^ s)) =
    ((((a ^^ b) ^^ c) ^^ d) ^^ (((p ^^ q) ^^ r) ^^ s))) _ _ _ _ _ _ _ _

theorem mixColumns_c63 (s : Spec.Aes.State) : Spec.Aes.mixColumns (c63 s) = c63 (Spec.Aes.mixColumns s) :=
  state_ext fun n hn => by
    rw [getD_c63 _ hn, Spec.Aes.mixColumns, Spec.Aes.mixColumns, getD_ofFn _ hn, getD_ofFn _ hn]
    simp only [getD_c63 _ (show (n % 4 + 0) % 4 + 4 * (n / 4) < 16 by omega),
      getD_c63 _ (show (n % 4 + 1) % 4 + 4 * (n / 4) < 16 by omega),
      getD_c63 _ (show (n % 4 + 2) % 4 + 4 * (n / 4) < 16 by omega),
      getD_c63 _ (show (n % 4 + 3) % 4 + 4 * (n / 4) < 16 by omega)]
    rw [mc2, mc3, show Spec.Aes.mul 0x02 0x63 = (0xa5 : Byte) ^^^ 0x63 by decide +kernel,
      show Spec.Aes.mul 0x03 0x63 = (0xa5 : Byte) by decide +kernel]
    exact xor_consts _ _ _ _ _ _

theorem invMixColumns_c63 (s : Spec.Aes.State) :
    Spec.Aes.invMixColumns (c63 s) = c63 (Spec.Aes.invMixColumns s) :=
  state_ext fun n hn => by
    rw [getD_c63 _ hn, Spec.Aes.invMixColumns, Spec.Aes.invMixColumns, getD_ofFn _ hn, getD_ofFn _ hn]
    simp only [getD_c63 _ (show (n % 4 + 0) % 4 + 4 * (n / 4) < 16 by omega),
      getD_c63 _ (show (n % 4 + 1) % 4 + 4 * (n / 4) < 16 by omega),
      getD_c63 _ (show (n % 4 + 2) % 4 + 4 * (n / 4) < 16 by omega),
      getD_c63 _ (show (n % 4 + 3) % 4 + 4 * (n / 4) < 16 by omega)]
    rw [mce, mcb, mcd, mc9]
    exact xor_consts4 _ _ _ _ _ _ _ _ _ (by decide +kernel)

theorem getD_rk63 (rk : List Byte) {n : Nat} (hn : n < rk.length) :
    (rk63 rk).getD n 0 = rk.getD n 0 ^^^ 0x63 := by
  simp [rk63, List.getD_eq_getElem?_getD, hn]

theorem addRoundKey_rk63 (s : Spec.Aes.State) {rk : List Byte} (h : rk.length = 16) :
    Spec.Aes.addRoundKey s (rk63 rk) = c63 (Spec.Aes.addRoundKey s rk) :=
  state_ext fun n hn => by
    rw [getD_c63 _ hn, Spec.Aes.addRoundKey, Spec.Aes.addRoundKey, getD_ofFn _ hn, getD_ofFn _ hn,
      getD_rk63 _ (by rw [h]; exact hn), BitVec.xor_assoc]

theorem c63_c63 (s : Spec.Aes.State) : c63 (c63 s) = s :=
  state_ext fun n hn => by rw [getD_c63 _ hn, getD_c63 _ hn, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem addRoundKey_c63 (s : Spec.Aes.State) (rk : List Byte) :
    Spec.Aes.addRoundKey (c63 s) rk = c63 (Spec.Aes.addRoundKey s rk) :=
  state_ext fun n hn => by
    rw [getD_c63 _ hn, Spec.Aes.addRoundKey, Spec.Aes.addRoundKey, getD_ofFn _ hn, getD_ofFn _ hn,
      getD_c63 _ hn, BitVec.xor_assoc, BitVec.xor_assoc, BitVec.xor_comm 0x63]

theorem map_sbox0 (s : Spec.Aes.State) : s.map sbox0 = c63 (Spec.Aes.subBytes s) :=
  state_ext fun n hn => by rw [getD_c63 _ hn, Spec.Aes.subBytes, getD_map _ _ hn, getD_map _ _ hn, sbox0]

/-- The inverse S-box of an input with `{63}` added. -/
def invSbox0 (b : Byte) : Byte := Spec.Aes.invSbox (b ^^^ 0x63)

theorem map_invSbox0 (s : Spec.Aes.State) : (c63 s).map invSbox0 = Spec.Aes.invSubBytes s :=
  state_ext fun n hn => by
    rw [getD_map _ _ hn, getD_c63 _ hn, Spec.Aes.invSubBytes, getD_map _ _ hn, invSbox0, BitVec.xor_assoc,
      BitVec.xor_self, BitVec.xor_zero]

/-! ### Rounds, with the round keys that have `{63}` added -/

/-- A middle round. -/
theorem round63 (s : Spec.Aes.State) {rk : List Byte} (h : rk.length = 16) :
    Spec.Aes.addRoundKey (Spec.Aes.mixColumns (Spec.Aes.shiftRows (s.map sbox0))) (rk63 rk) =
      Spec.Aes.addRoundKey (Spec.Aes.mixColumns (Spec.Aes.shiftRows (Spec.Aes.subBytes s))) rk := by
  rw [map_sbox0, shiftRows_c63, mixColumns_c63, addRoundKey_rk63 _ h, addRoundKey_c63, c63_c63]

/-- The last round. -/
theorem lastRound63 (s : Spec.Aes.State) {rk : List Byte} (h : rk.length = 16) :
    Spec.Aes.addRoundKey (Spec.Aes.shiftRows (s.map sbox0)) (rk63 rk) =
      Spec.Aes.addRoundKey (Spec.Aes.shiftRows (Spec.Aes.subBytes s)) rk := by
  rw [map_sbox0, shiftRows_c63, addRoundKey_rk63 _ h, addRoundKey_c63, c63_c63]

/-- A middle round of the inverse cipher, between states with `{63}` added. -/
theorem invRound63 (s : Spec.Aes.State) {rk : List Byte} (h : rk.length = 16) :
    Spec.Aes.invMixColumns (Spec.Aes.addRoundKey ((Spec.Aes.invShiftRows (c63 s)).map invSbox0) (rk63 rk)) =
      c63 (Spec.Aes.invMixColumns (Spec.Aes.addRoundKey (Spec.Aes.invSubBytes (Spec.Aes.invShiftRows s)) rk)) := by
  rw [invShiftRows_c63, map_invSbox0, addRoundKey_rk63 _ h, invMixColumns_c63]

end VG.Proof.Aes
