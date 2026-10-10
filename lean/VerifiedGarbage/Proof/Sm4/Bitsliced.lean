import VerifiedGarbage.Proof.Sm4.SboxTable
import VerifiedGarbage.Proof.Aes.Bitsliced
import VerifiedGarbage.Impl.Sm4.Lin

/-!
# Bitsliced SM4: the layout and the layers

Sixteen blocks at a time. A 32-bit word of each block is held in eight 64-bit
*planes*: bit `16 i + b` of plane `j` is bit `j` of byte `i` (from the most
significant) of the word of block `b` (`WordRel`). So rotating the words by
`8 m` bits rotates the planes by `16 m` (`rotP`), and the round's linear
transformations are, plane by plane, XORs of rotations of planes: `linTerms`
for `L`, `keyTerms` for `L'`, as pairs (plane, rotation in bytes).

The lemmas here turn what each layer of the code does to the bits (as its
proof states it, by evaluation) into the function of the specification it
computes on the words: the S-box (`tau_rel`), `L` and `L'` (`lin_rel`), and
a round (`round_rel`). Nothing here depends on the target.
-/

namespace VG.Proof.Sm4

open VG VG.Spec.Sm4 VG.Bitslice
open VG.Proof.Aes (bsByte getLsbD_bsByte byte_ext termsXor)
open VG.Impl.Sm4 (Lin)

/-! ## The layout -/

/-- The planes `Q` hold the words `v b` of the sixteen blocks. -/
def WordRel (Q : Nat → BitVec 64) (v : Nat → Word) : Prop :=
  ∀ b < 16, ∀ i < 4, ∀ j < 8, (Q j).getLsbD (16 * i + b) = (v b).getLsbD (8 * (3 - i) + j)

theorem WordRel.congr {Q Q' : Nat → BitVec 64} {v : Nat → Word} (h : WordRel Q v)
    (he : ∀ j < 8, Q' j = Q j) : WordRel Q' v := fun b hb i hi j hj => by
  rw [he j hj]; exact h b hb i hi j hj

theorem WordRel.congr_right {Q : Nat → BitVec 64} {v v' : Nat → Word} (h : WordRel Q v)
    (he : ∀ b < 16, v' b = v b) : WordRel Q v' := fun b hb i hi j hj => by
  rw [he b hb]; exact h b hb i hi j hj

/-- XORing the planes of two words. -/
theorem WordRel.xor {Q K Q' : Nat → BitVec 64} {v u : Nat → Word} (hq : WordRel Q v) (hk : WordRel K u)
    (h : ∀ j < 8, ∀ p < 64, (Q' j).getLsbD p = ((Q j).getLsbD p ^^ (K j).getLsbD p)) :
    WordRel Q' (fun b => v b ^^^ u b) := fun b hb i hi j hj => by
  rw [h j hj _ (by omega), hq b hb i hi j hj, hk b hb i hi j hj, BitVec.getLsbD_xor]

/-! ## The S-box -/

/-- Byte `i` (from the most significant) of a word. -/
def byteAt (x : Word) (i : Nat) : Byte := (x >>> (8 * (3 - i))).setWidth 8

theorem getLsbD_byteAt (x : Word) {i j : Nat} (_hi : i < 4) (hj : j < 8) :
    (byteAt x i).getLsbD j = x.getLsbD (8 * (3 - i) + j) := by
  simp only [byteAt, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hj, decide_true,
    Bool.true_and]

/-- The byte of `x` at bits `8 k … 8 k + 7`, through the S-box. -/
def subAt (x : Word) (k : Nat) : Byte := sbox.getD ((x >>> (8 * k)).setWidth 8).toNat 0

theorem tau_eq (x : Word) (k : Nat) :
    (tau x).getLsbD k = (subAt x 3 ++ subAt x 2 ++ subAt x 1 ++ subAt x 0 : BitVec (8 + 8 + 8 + 8)).getLsbD k :=
  rfl

theorem getLsbD_tau (x : Word) {i j : Nat} (hi : i < 4) (hj : j < 8) :
    (tau x).getLsbD (8 * (3 - i) + j) = (sboxB (byteAt x i)).getLsbD j := by
  rw [tau_eq]
  simp only [BitVec.getLsbD_append]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;>
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [subAt, sboxB, byteAt, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Nat.reduceLT, ↓reduceIte, Nat.lt_irrefl]

/-- The S-box layer: `S` holds, at each position, the S-box of the byte the
planes `X` hold there. -/
theorem tau_rel {X S : Nat → BitVec 64} {v : Nat → Word} (hX : WordRel X v)
    (hS : ∀ j < 8, ∀ p < 64, (S j).getLsbD p = (sboxB (bsByte X p)).getLsbD j) :
    WordRel S (fun b => tau (v b)) := by
  intro b hb i hi j hj
  rw [hS j hj _ (by omega), getLsbD_tau _ hi hj]
  congr 2
  refine byte_ext fun k hk => ?_
  rw [getLsbD_bsByte _ _ hk, hX b hb i hi k hk, getLsbD_byteAt _ hi hk]

/-! ## The linear transformations -/

/-- Position `p` of a plane rotated by `m` bytes: `ror 16 m`. -/
def rotP (p m : Nat) : Nat := (p + 16 * m) % 64

/-- Plane `j` of `L(B)`: `Bⱼ ⊕ (Bⱼ ⋘ 24) ⊕ Qⱼ ⊕ (Qⱼ ⋘ 8) ⊕ (Qⱼ ⋘ 16)`, `Qⱼ` the
planes of `B ⋘ 2`, as (plane, bytes of rotation). -/
def linTerms (j : Nat) : List (Nat × Nat) :=
  [(j, 0), (j, 3)] ++ if 2 ≤ j then [(j - 2, 0), (j - 2, 1), (j - 2, 2)] else [(j + 6, 1), (j + 6, 2), (j + 6, 3)]

/-- Plane `j` of `L'(B) = B ⊕ (B ⋘ 13) ⊕ (B ⋘ 23)`. -/
def keyTerms (j : Nat) : List (Nat × Nat) :=
  [(j, 0), if 5 ≤ j then (j - 5, 1) else (j + 3, 2), if j = 7 then (0, 2) else (j + 1, 3)]

/-- The linear transformation of encryption or of the key schedule, and
its planes. -/
def _root_.VG.Impl.Sm4.Lin.fn : Lin → Word → Word
  | .enc => linear
  | .key => keyLinear

def _root_.VG.Impl.Sm4.Lin.terms : Lin → Nat → List (Nat × Nat)
  | .enc => linTerms
  | .key => keyTerms

/-- The XOR of the bits `l` of `x`. -/
def idxXor (x : Word) (l : List Nat) : Bool := l.foldr (fun k acc => x.getLsbD k ^^ acc) false

theorem idxXor_perm (x : Word) {l l' : List Nat} (h : l.Perm l') : idxXor x l = idxXor x l' := by
  unfold idxXor
  exact h.foldr_eq' (fun _ _ _ _ _ => by simp only [Bool.xor_left_comm]) false

theorem getLsbD_rotateLeft32 (x : Word) (r : Nat) (hr : r < 32) {k : Nat} (hk : k < 32) :
    (x.rotateLeft r).getLsbD k = x.getLsbD ((k + (32 - r)) % 32) := by
  rw [BitVec.getLsbD_rotateLeft]
  simp only [Nat.mod_eq_of_lt hr]
  split
  · congr 1; omega
  · simp only [hk, decide_true, Bool.true_and]; congr 1; omega

/-- The bits of `x` whose XOR is bit `k` of `L x` and of `L' x`. -/
def linIdx (k : Nat) : List Nat := [k, (k + 30) % 32, (k + 22) % 32, (k + 14) % 32, (k + 8) % 32]
def keyIdx (k : Nat) : List Nat := [k, (k + 19) % 32, (k + 9) % 32]

def _root_.VG.Impl.Sm4.Lin.idx : Lin → Nat → List Nat
  | .enc => linIdx
  | .key => keyIdx

theorem getLsbD_fn (l : Lin) (x : Word) {k : Nat} (hk : k < 32) :
    (l.fn x).getLsbD k = idxXor x (l.idx k) := by
  cases l
  · simp only [Impl.Sm4.Lin.fn, Impl.Sm4.Lin.idx, linear, linIdx, idxXor, List.foldr_cons, List.foldr_nil,
      BitVec.getLsbD_xor, getLsbD_rotateLeft32 x 2 (by decide) hk, getLsbD_rotateLeft32 x 10 (by decide) hk,
      getLsbD_rotateLeft32 x 18 (by decide) hk, getLsbD_rotateLeft32 x 24 (by decide) hk, Bool.xor_false,
      Bool.xor_assoc]
  · simp only [Impl.Sm4.Lin.fn, Impl.Sm4.Lin.idx, keyLinear, keyIdx, idxXor, List.foldr_cons, List.foldr_nil,
      BitVec.getLsbD_xor, getLsbD_rotateLeft32 x 13 (by decide) hk, getLsbD_rotateLeft32 x 23 (by decide) hk,
      Bool.xor_false, Bool.xor_assoc]

/-- The bits of the word that a plane's terms read at byte `i`. -/
def termIdx (i : Nat) (l : List (Nat × Nat)) : List Nat :=
  l.map fun sm => 8 * (3 - (i + sm.2) % 4) + sm.1

theorem terms_perm (l : Lin) : ∀ i < 4, ∀ j < 8, (termIdx i (l.terms j)).Perm (l.idx (8 * (3 - i) + j)) := by
  cases l <;> decide

theorem terms_lt (l : Lin) : ∀ j < 8, ∀ sm ∈ l.terms j, sm.1 < 8 := by
  cases l <;> decide

theorem rotP_pos {i b m : Nat} (hb : b < 16) (_hi : i < 4) : rotP (16 * i + b) m = 16 * ((i + m) % 4) + b := by
  simp only [rotP]; omega

theorem termsXor_rel {S : Nat → BitVec 64} {u : Nat → Word} (hS : WordRel S u) {b i : Nat} (hb : b < 16)
    (hi : i < 4) (l : List (Nat × Nat)) (hl : ∀ sm ∈ l, sm.1 < 8) :
    termsXor S (l.map fun sm => (sm.1, rotP (16 * i + b) sm.2)) = idxXor (u b) (termIdx i l) := by
  induction l with
  | nil => rfl
  | cons sm l ih =>
    simp only [List.map_cons, termsXor, List.foldr_cons, termIdx, idxXor] at ih ⊢
    rw [ih fun x hx => hl x (List.mem_cons_of_mem _ hx), rotP_pos hb hi,
      hS b hb _ (Nat.mod_lt _ (by decide)) _ (hl sm List.mem_cons_self)]

/-- The linear layer: `Y`'s planes are the XORs of the rotated planes of `S`. -/
theorem lin_rel (l : Lin) {S Y : Nat → BitVec 64} {u : Nat → Word} (hS : WordRel S u)
    (hY : ∀ j < 8, ∀ p < 64, (Y j).getLsbD p = termsXor S ((l.terms j).map fun sm => (sm.1, rotP p sm.2))) :
    WordRel Y (fun b => l.fn (u b)) := by
  intro b hb i hi j hj
  rw [hY j hj _ (by omega), termsXor_rel hS hb hi _ (terms_lt l j hj), getLsbD_fn l _ (by omega),
    idxXor_perm _ (terms_perm l i hi j hj)]

/-! ## A round -/

/-- `T` and `T'`: the S-box layer, then `L` or `L'`. -/
def _root_.VG.Impl.Sm4.Lin.t (l : Lin) (x : Word) : Word := l.fn (tau x)

theorem _root_.VG.Impl.Sm4.Lin.t_enc (x : Word) : Lin.enc.t x = Spec.Sm4.t x := rfl
theorem _root_.VG.Impl.Sm4.Lin.t_key (x : Word) : Lin.key.t x = keyT x := rfl

/-- A round: from the words `xb`, `xc`, `xd` and the round key `k` in the
planes `B`, `C`, `D` and `K`, the code computes `X` (their XOR), `S` (the
S-box layer) and XORs the linear layer of `S` into the word `xa` in `A`,
giving `A'`. -/
theorem round_rel (l : Lin) {A B C D K X S A' : Nat → BitVec 64} {xa xb xc xd : Nat → Word} {k : Word}
    (hB : WordRel B xb) (hC : WordRel C xc) (hD : WordRel D xd) (hK : WordRel K fun _ => k)
    (hA : WordRel A xa)
    (hX : ∀ j < 8, ∀ p < 64, (X j).getLsbD p =
      ((((B j).getLsbD p ^^ (C j).getLsbD p) ^^ (D j).getLsbD p) ^^ (K j).getLsbD p))
    (hS : ∀ j < 8, ∀ p < 64, (S j).getLsbD p = (sboxB (bsByte X p)).getLsbD j)
    (hA' : ∀ j < 8, ∀ p < 64, (A' j).getLsbD p =
      ((A j).getLsbD p ^^ termsXor S ((l.terms j).map fun sm => (sm.1, rotP p sm.2)))) :
    WordRel A' (fun b => xa b ^^^ l.t (xb b ^^^ xc b ^^^ xd b ^^^ k)) := by
  have hx : WordRel X (fun b => xb b ^^^ xc b ^^^ xd b ^^^ k) := by
    intro b hb i hi j hj
    rw [hX j hj _ (by omega), hB b hb i hi j hj, hC b hb i hi j hj, hD b hb i hi j hj,
      hK b hb i hi j hj]
    simp only [BitVec.getLsbD_xor]
  have hy := lin_rel l (tau_rel hx hS) (Y := fun j => A j ^^^ A' j) fun j hj p hp => by
    rw [BitVec.getLsbD_xor, hA' j hj p hp, ← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]
  intro b hb i hi j hj
  have := hy b hb i hi j hj
  dsimp only at this
  rw [BitVec.getLsbD_xor, hA b hb i hi j hj] at this
  rw [BitVec.getLsbD_xor, Lin.t, ← this, ← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]

end VG.Proof.Sm4
