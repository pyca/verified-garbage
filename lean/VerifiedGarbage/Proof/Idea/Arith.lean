import VerifiedGarbage.Proof.Idea.KeyBits

/-!
# IDEA: word arithmetic the implementations share

Target-independent facts about the operations the implementations compute
⊙, ⊞ and the words of a block and of the schedule with: ⊙'s operands'
residues (`prep_toNat`) and its reduction from the product's halves
(`reduce`); ⊞ and XOR on zero-extended words (`add_mask`, `xor_setWidth`);
two bytes as a big-endian word (`bytes16`) and back (`lo8`, `hi8`); and what
each decryption subkey is (`invertKey_getD`).
-/

namespace VG.Proof.Idea

open VG VG.Impl.Idea

theorem mask_toNat (x m : BitVec 64) (hm : m.toNat = 65535) :
    (x &&& m).toNat = x.toNat % 65536 := by
  rw [BitVec.toNat_and, hm, show 65535 = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem setWidth16_toNat (x : BitVec 64) : (x.setWidth 16).toNat = x.toNat % 65536 := by
  simp [BitVec.toNat_setWidth]

/-- `((x - 1) & 0xffff) + 1` is the residue of `x`'s low word. -/
theorem prep_toNat (a m : BitVec 64) (hm : m.toNat = 65535) :
    (((a - 1) &&& m) + 1 : BitVec 64).toNat = Spec.Idea.residue (a.setWidth 16) := by
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  rw [BitVec.toNat_add, mask_toNat _ _ hm, BitVec.toNat_sub, h1]
  unfold Spec.Idea.residue
  have hs := setWidth16_toNat a
  split
  · rename_i h
    have h' : a.toNat % 65536 = 0 := by rw [← hs, h]; rfl
    omega
  · rename_i h
    have h' : a.toNat % 65536 ≠ 0 := by
      intro h''; apply h; apply BitVec.eq_of_toNat_eq; rw [hs, h'']; rfl
    rw [hs]; omega

theorem residue_le (a : Spec.Idea.Word) : Spec.Idea.residue a ≤ 2 ^ 16 := by
  unfold Spec.Idea.residue
  split
  · exact Nat.le_refl _
  · exact Nat.le_of_lt a.isLt

theorem residue_pos (a : Spec.Idea.Word) : 0 < Spec.Idea.residue a := by
  unfold Spec.Idea.residue
  split
  · decide
  · rename_i h
    exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq h')

/-- The product modulo 2¹⁶ + 1 from its halves, as `mulCode` computes it. -/
theorem reduce (p : Nat) (hp : p ≤ 2 ^ 32) (m : BitVec 64) (hm : m.toNat = 65535) :
    (((BitVec.ofNat 64 p &&& m) - BitVec.ofNat 64 p >>> 16) +
      ((BitVec.ofNat 64 p &&& m) - BitVec.ofNat 64 p >>> 16) >>> 63 +
      (((BitVec.ofNat 64 p &&& m) - BitVec.ofNat 64 p >>> 16) >>> 63) <<< 16) &&& m =
      BitVec.ofNat 64 (p % 65537 % 65536) := by
  have hlo : (BitVec.ofNat 64 p &&& m).toNat = p % 65536 := by
    rw [mask_toNat _ _ hm, BitVec.toNat_ofNat]; omega
  have hhi : (BitVec.ofNat 64 p >>> 16).toNat = p / 65536 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega
  generalize hr : (BitVec.ofNat 64 p &&& m) - BitVec.ofNat 64 p >>> 16 = r
  have hrn : r.toNat = (2 ^ 64 - p / 65536 + p % 65536) % 2 ^ 64 := by
    rw [← hr, BitVec.toNat_sub, hlo, hhi]
  apply BitVec.eq_of_toNat_eq
  rw [mask_toNat _ _ hm, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hrn, BitVec.toNat_ofNat]
  generalize hH : p / 65536 = H
  generalize hL : p % 65536 = L
  have hdec : p = 65536 * H + L := by omega
  have hL' : L < 65536 := by omega
  have hH' : H ≤ 65536 := by omega
  subst hdec
  clear hrn hr hlo hhi hH hL hp
  have e1 : (65536 * H + L) % 65537 = (L + 65537 - H) % 65537 := by omega
  rw [e1]
  by_cases hc : L < H
  · have hR : (2 ^ 64 - H + L) % 2 ^ 64 = 2 ^ 64 - (H - L) := by
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    have ht : (2 ^ 64 - (H - L)) / 2 ^ 63 = 1 := by omega
    rw [hR, ht, Nat.mod_mod_of_dvd _ (by decide : 65536 ∣ 2 ^ 64),
      show 1 * 2 ^ 16 % 2 ^ 64 = 65536 * 1 from rfl, Nat.add_mul_mod_self_left,
      Nat.mod_mod_of_dvd _ (by decide : 65536 ∣ 2 ^ 64),
      show 2 ^ 64 - (H - L) + 1 = (L + 65537 - H) + 65536 * (2 ^ 48 - 1) by omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (a := L + 65537 - H) (b := 65537) (by omega)]
    exact (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (show 65536 > 0 by decide)) (show 65536 ≤ 2 ^ 64 by decide))).symm
  · have hR : (2 ^ 64 - H + L) % 2 ^ 64 = L - H := by omega
    have ht : (L - H) / 2 ^ 63 = 0 := by omega
    rw [hR, ht, Nat.mod_mod_of_dvd _ (by decide : 65536 ∣ 2 ^ 64)]
    simp only [Nat.add_zero, Nat.zero_mul, Nat.zero_mod]
    rw [Nat.mod_eq_of_lt (a := L - H) (b := 2 ^ 64) (by omega),
      show L + 65537 - H = (L - H) + 65537 * 1 by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (a := L - H) (b := 65537) (by omega)]
    exact (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (show 65536 > 0 by decide)) (show 65536 ≤ 2 ^ 64 by decide))).symm

theorem mul_toNat (a b : Spec.Idea.Word) :
    (Spec.Idea.mul a b).setWidth 64 =
      BitVec.ofNat 64 (Spec.Idea.residue a * Spec.Idea.residue b % 65537 % 65536) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Spec.Idea.mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat]

theorem setWidth_setWidth16 (x : BitVec 16) : (x.setWidth 64).setWidth 16 = x := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

/-- `add r, y; and r, 0xffff` on a zero-extended word. -/
theorem add_mask (x : BitVec 16) (y : BitVec 64) :
    (x.setWidth 64 + y) &&& 65535 = (x + y.setWidth 16).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  rw [mask_toNat _ _ rfl]
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth]
  omega

theorem add_setWidth (x y : BitVec 16) :
    (x.setWidth 64 + y.setWidth 64).setWidth 16 = x + y := by
  rw [BitVec.setWidth_add _ _ (by decide), setWidth_setWidth16, setWidth_setWidth16]

theorem xor_setWidth (x y : BitVec 16) : x.setWidth 64 ^^^ y.setWidth 64 = (x ^^^ y).setWidth 64 := by
  rw [BitVec.setWidth_xor]

/-- Two bytes, big-endian, as the code assembles them. -/
theorem bytes16 (x y : BitVec 8) :
    (x.setWidth 64 <<< 8 ||| y.setWidth 64) = (x ++ y).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_append,
    Nat.shiftLeft_eq]
  have hx := x.isLt
  have hy := y.isLt
  rw [Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 64), Nat.mod_eq_of_lt (by omega : y.toNat < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : x.toNat * 2 ^ 8 < 2 ^ 64)]
  exact (Nat.mod_eq_of_lt (Nat.or_lt_two_pow (by omega) (by omega))).symm

theorem output_getD0 (a b c d : Spec.Idea.Word) (x : Spec.Idea.State) :
    (Spec.Idea.output a b c d x).getD 0 0 = Spec.Idea.mul (x.getD 0 0) a := rfl

theorem output_getD1 (a b c d : Spec.Idea.Word) (x : Spec.Idea.State) :
    (Spec.Idea.output a b c d x).getD 1 0 = x.getD 2 0 + b := rfl

theorem output_getD2 (a b c d : Spec.Idea.Word) (x : Spec.Idea.State) :
    (Spec.Idea.output a b c d x).getD 2 0 = x.getD 1 0 + c := rfl

theorem output_getD3 (a b c d : Spec.Idea.Word) (x : Spec.Idea.State) :
    (Spec.Idea.output a b c d x).getD 3 0 = Spec.Idea.mul (x.getD 3 0) d := rfl

theorem lo8 (x : BitVec 16) : (x.setWidth 64).setWidth 8 = x.setWidth 8 :=
  BitVec.setWidth_setWidth_of_le _ (by decide)

theorem hi8 (x : BitVec 16) : ((x.setWidth 64) >>> 8).setWidth 8 = (x >>> 8).setWidth 8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 64)]

/-- The state after `n` rounds (`Spec.Idea.crypt` before the output transformation). -/
def roundsSpec (z : Spec.Idea.Schedule) (n : Nat) (x : Spec.Idea.State) : Spec.Idea.State :=
  (List.range n).foldl (fun x r =>
    Spec.Idea.round (z.getD (6 * r) 0) (z.getD (6 * r + 1) 0) (z.getD (6 * r + 2) 0)
      (z.getD (6 * r + 3) 0) (z.getD (6 * r + 4) 0) (z.getD (6 * r + 5) 0) x) x

theorem crypt_eq (z : Spec.Idea.Schedule) (x : Spec.Idea.State) :
    Spec.Idea.crypt z x =
      Spec.Idea.output (z.getD 48 0) (z.getD 49 0) (z.getD 50 0) (z.getD 51 0) (roundsSpec z 8 x) :=
  rfl

/-- What `invOp` says decryption subkey `n` is. -/
def applyOp (z : Spec.Idea.Schedule) : Op × Nat → Spec.Idea.Word
  | (.copy, k) => z.getD k 0
  | (.neg, k) => -z.getD k 0
  | (.inv, k) => Spec.Idea.inv (z.getD k 0)

theorem invertKey_getD (z : Spec.Idea.Schedule) {n : Nat} (hn : n < 52) :
    (Spec.Idea.invertKey z).getD n 0 = applyOp z (invOp n) := by
  rw [getD_lt _ _ hn]
  simp only [Spec.Idea.invertKey, Vector.getElem_ofFn, invOp]
  obtain h | h | h | h | h | h : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨
    n % 6 = 5 := by omega
  all_goals simp only [h, applyOp]

theorem invOp_lt {n : Nat} (hn : n < 52) : (invOp n).2 < 52 := by
  simp only [invOp]
  obtain h | h | h | h | h | h : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨
    n % 6 = 5 := by omega
  all_goals simp only [h]; first | omega | (split <;> omega)

theorem mask_setWidth (x : BitVec 64) : x &&& 65535 = (x.setWidth 16).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  rw [mask_toNat _ _ rfl]
  simp only [BitVec.toNat_setWidth]
  omega

theorem neg_mask (x : BitVec 64) : (0 - x) &&& 65535 = (-(x.setWidth 16)).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  rw [mask_toNat _ _ rfl]
  simp only [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_neg, show (0 : BitVec 64).toNat = 0 from rfl]
  omega

theorem scheduleAt_congr {m m' : Mem} {p : Addr}
    (h : ∀ i < 104, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    Spec.Idea.scheduleAt m' p = Spec.Idea.scheduleAt m p := by
  simp only [Spec.Idea.scheduleAt]
  congr 1
  funext i
  rw [h _ (by omega), h _ (by omega)]

theorem blockAt_congr {m m' : Mem} {p : Addr}
    (h : ∀ i < 8, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    Spec.Idea.blockAt m' p = Spec.Idea.blockAt m p := by
  simp only [Spec.Idea.blockAt]
  congr 1
  funext i
  exact h _ i.isLt

theorem toNat_one : (1 : BitVec 64).toNat = 1 := rfl

theorem toNat_zero : (0 : BitVec 64).toNat = 0 := rfl

theorem beq_zero (x : BitVec 64) : (x == 0) = decide (x.toNat = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  exact ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq h⟩

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq; simp

theorem blocksAt_eq (m m₀ : Mem) (z : Spec.Idea.Schedule) (a : Addr) (n : Nat)
    (h : ∀ j < n, Spec.Idea.blockAt m (a + BitVec.ofNat 64 (8 * j)) =
      Spec.Idea.cryptBlock z (Spec.Idea.blockAt m₀ (a + BitVec.ofNat 64 (8 * j)))) :
    Spec.Idea.blocksAt m a n = Spec.Idea.ecb z (Spec.Idea.blocksAt m₀ a n) := by
  simp only [Spec.Idea.blocksAt, Spec.Idea.ecb, List.map_map]
  exact List.map_congr_left fun j hj => h j (List.mem_range.mp hj)

end VG.Proof.Idea
