import VerifiedGarbage.Proof.Sm4.Bitsliced

/-!
# Bitsliced SM4 on 32-bit planes

The layout of the 32-bit targets: eight blocks at a time, a 32-bit word of
each block held in eight 32-bit planes, bit `8 i + b` of plane `j` being
bit `j` of byte `i` (from the most significant) of the word of block `b`
(`WordRel`). Rotating the words by `8 m` bits rotates the planes by `8 m`
(`rotP`). The lemmas are those of `Bitsliced.lean` for this layout: the
S-box layer (`tau_rel`), `L` and `L'` (`lin_rel`) and a round
(`round_rel`). Nothing here depends on the target.
-/

namespace VG.Proof.Sm4.W32

open VG VG.Spec.Sm4 VG.Bitslice
open VG.Proof.Aes (byte_ext)
open VG.Proof.Sm4 (byteAt getLsbD_byteAt getLsbD_tau idxXor idxXor_perm getLsbD_fn termIdx terms_perm
  terms_lt)
open VG.Impl.Sm4 (Lin)

/-! ## The layout -/

/-- The byte formed by bit `p` of the eight planes. -/
def bsByte (Q : Nat → BitVec 32) (p : Nat) : Byte := ofBits 8 fun k => (Q k).getLsbD p

theorem getLsbD_bsByte (Q : Nat → BitVec 32) (p : Nat) {k : Nat} (hk : k < 8) :
    (bsByte Q p).getLsbD k = (Q k).getLsbD p := by
  rw [bsByte, getLsbD_ofBits]; simp [hk]

/-- The planes `Q` hold the words `v b` of the eight blocks. -/
def WordRel (Q : Nat → BitVec 32) (v : Nat → Word) : Prop :=
  ∀ b < 8, ∀ i < 4, ∀ j < 8, (Q j).getLsbD (8 * i + b) = (v b).getLsbD (8 * (3 - i) + j)

theorem WordRel.congr {Q Q' : Nat → BitVec 32} {v : Nat → Word} (h : WordRel Q v)
    (he : ∀ j < 8, Q' j = Q j) : WordRel Q' v := fun b hb i hi j hj => by
  rw [he j hj]; exact h b hb i hi j hj

theorem WordRel.congr_right {Q : Nat → BitVec 32} {v v' : Nat → Word} (h : WordRel Q v)
    (he : ∀ b < 8, v' b = v b) : WordRel Q v' := fun b hb i hi j hj => by
  rw [he b hb]; exact h b hb i hi j hj

/-! ## The S-box -/

/-- The S-box layer: `S` holds, at each position, the S-box of the byte the
planes `X` hold there. -/
theorem tau_rel {X S : Nat → BitVec 32} {v : Nat → Word} (hX : WordRel X v)
    (hS : ∀ j < 8, ∀ p < 32, (S j).getLsbD p = (sboxB (bsByte X p)).getLsbD j) :
    WordRel S (fun b => tau (v b)) := by
  intro b hb i hi j hj
  rw [hS j hj _ (by omega), getLsbD_tau _ hi hj]
  congr 2
  refine byte_ext fun k hk => ?_
  rw [getLsbD_bsByte _ _ hk, hX b hb i hi k hk, getLsbD_byteAt _ hi hk]

/-! ## The linear transformations -/

/-- Position `p` of a plane rotated by `m` bytes: `ror 8 m`. -/
def rotP (p m : Nat) : Nat := (p + 8 * m) % 32

/-- The XOR of the bits `l` (plane, position) of the planes `Q`. -/
def termsXor (Q : Nat → BitVec 32) (l : List (Nat × Nat)) : Bool :=
  l.foldr (fun wk acc => (Q wk.1).getLsbD wk.2 ^^ acc) false

theorem rotP_pos {i b m : Nat} (hb : b < 8) (_hi : i < 4) : rotP (8 * i + b) m = 8 * ((i + m) % 4) + b := by
  simp only [rotP]; omega

theorem termsXor_rel {S : Nat → BitVec 32} {u : Nat → Word} (hS : WordRel S u) {b i : Nat} (hb : b < 8)
    (hi : i < 4) (l : List (Nat × Nat)) (hl : ∀ sm ∈ l, sm.1 < 8) :
    termsXor S (l.map fun sm => (sm.1, rotP (8 * i + b) sm.2)) = idxXor (u b) (termIdx i l) := by
  induction l with
  | nil => rfl
  | cons sm l ih =>
    simp only [List.map_cons, termsXor, List.foldr_cons, termIdx, idxXor] at ih ⊢
    rw [ih fun x hx => hl x (List.mem_cons_of_mem _ hx), rotP_pos hb hi,
      hS b hb _ (Nat.mod_lt _ (by decide)) _ (hl sm List.mem_cons_self)]

/-- The linear layer: `Y`'s planes are the XORs of the rotated planes of `S`. -/
theorem lin_rel (l : Lin) {S Y : Nat → BitVec 32} {u : Nat → Word} (hS : WordRel S u)
    (hY : ∀ j < 8, ∀ p < 32, (Y j).getLsbD p = termsXor S ((l.terms j).map fun sm => (sm.1, rotP p sm.2))) :
    WordRel Y (fun b => l.fn (u b)) := by
  intro b hb i hi j hj
  rw [hY j hj _ (by omega), termsXor_rel hS hb hi _ (terms_lt l j hj), getLsbD_fn l _ (by omega),
    idxXor_perm _ (terms_perm l i hi j hj)]

/-! ## A round -/

/-- A round, as `Bitsliced.round_rel`, on 32-bit planes. -/
theorem round_rel (l : Lin) {A B C D K X S A' : Nat → BitVec 32} {xa xb xc xd : Nat → Word} {k : Word}
    (hB : WordRel B xb) (hC : WordRel C xc) (hD : WordRel D xd) (hK : WordRel K fun _ => k)
    (hA : WordRel A xa)
    (hX : ∀ j < 8, ∀ p < 32, (X j).getLsbD p =
      ((((B j).getLsbD p ^^ (C j).getLsbD p) ^^ (D j).getLsbD p) ^^ (K j).getLsbD p))
    (hS : ∀ j < 8, ∀ p < 32, (S j).getLsbD p = (sboxB (bsByte X p)).getLsbD j)
    (hA' : ∀ j < 8, ∀ p < 32, (A' j).getLsbD p =
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

end VG.Proof.Sm4.W32
