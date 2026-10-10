import VerifiedGarbage.Proof.Ed25519.X86_64.BaseOdd
import VerifiedGarbage.Proof.Ed25519.X86_64.BaseEntry
import VerifiedGarbage.Proof.Ed25519.X86_64.CombSelect

/-!
# The static's words are its entries

Word `16 j + 4 f + w` of `baseOddWords` is word `w` of field `f` of entry `j`, so a memory
holding the words at `T` holds entry `j` at `T + 128 j` (`baseTbl_entry`).
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs fe val4 F)

/-- The words of an entry: `X`, `Y`, `Z`, `T`. -/
abbrev entry4Words (p : Spec.Ed25519.Point) : List (BitVec 64) :=
  [p.X, p.Y, p.Z, p.T].flatMap feWords

theorem feWords_length (v : Spec.X25519.Fe) : (feWords v).length = 4 := by simp [feWords]

theorem entry4Words_length (p : Spec.Ed25519.Point) : (entry4Words p).length = 16 := by
  rw [entry4Words, length_flatMap_const _ 4 _ (fun v _ => feWords_length v)]
  rfl

theorem entry4Words_getD (p : Spec.Ed25519.Point) {f w : Nat} (hf : f < 4) (hw : w < 4) :
    (entry4Words p).getD (f * 4 + w) 0 = feWord ([p.X, p.Y, p.Z, p.T].getD f 0) w := by
  rw [entry4Words, getD_flatMap_const _ 4 0 [p.X, p.Y, p.Z, p.T] 0 (fun v _ => feWords_length v) f hf w hw,
    feWords_getD _ hw]

theorem baseOddWords_eq :
    baseOddWords = baseOddAffine.flatMap fun q => entry4Words (baseOddCached q) := by
  unfold baseOddWords
  congr 1

theorem baseOddWords_length : baseOddWords.length = 2048 := by
  rw [baseOddWords_eq, length_flatMap_const _ 16 _ (fun q _ => entry4Words_length _),
    baseOddAffine_length]

theorem baseOddWords_getD {j f w : Nat} (hj : j < 128) (hf : f < 4) (hw : w < 4) :
    baseOddWords.getD (j * 16 + (f * 4 + w)) 0 =
      feWord ([(baseOddCached (baseOddAffine.getD j (0, 1))).X,
        (baseOddCached (baseOddAffine.getD j (0, 1))).Y,
        (baseOddCached (baseOddAffine.getD j (0, 1))).Z,
        (baseOddCached (baseOddAffine.getD j (0, 1))).T].getD f 0) w := by
  rw [baseOddWords_eq, getD_flatMap_const _ 16 0 baseOddAffine (0, 1)
      (fun q _ => entry4Words_length _) j (by rw [baseOddAffine_length]; exact hj) _ (by omega),
    entry4Words_getD _ hf hw]

/-- Field `f` of entry `j`, from the words at `T`. -/
theorem baseField {m : Mem} {T : Addr}
    (hheld : ∀ i < 2048, m.readW (T + BitVec.ofNat 64 (8 * i)) 64 = baseOddWords.getD i 0)
    {j f : Nat} (hj : j < 128) (hf : f < 4) :
    F m (off T (128 * j)) (32 * f) =
      [(baseOddCached (baseOddAffine.getD j (0, 1))).X,
        (baseOddCached (baseOddAffine.getD j (0, 1))).Y,
        (baseOddCached (baseOddAffine.getD j (0, 1))).Z,
        (baseOddCached (baseOddAffine.getD j (0, 1))).T].getD f 0 := by
  have hword : ∀ w < 4, Proof.X25519.X86_64.word m (off T (128 * j)) (32 * f + 8 * w) =
      feWord ([(baseOddCached (baseOddAffine.getD j (0, 1))).X,
        (baseOddCached (baseOddAffine.getD j (0, 1))).Y,
        (baseOddCached (baseOddAffine.getD j (0, 1))).Z,
        (baseOddCached (baseOddAffine.getD j (0, 1))).T].getD f 0) w := by
    intro w hw
    simp only [Proof.X25519.X86_64.word, off, Offset.add_add]
    rw [show 128 * j + (32 * f + 8 * w) = 8 * (j * 16 + (f * 4 + w)) by omega,
      hheld _ (by omega), baseOddWords_getD hj hf hw]
  simp only [F, fe]
  have h0 := hword 0 (by decide)
  have h1 := hword 1 (by decide)
  have h2 := hword 2 (by decide)
  have h3 := hword 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul] at h0 h1 h2 h3
  rw [h0, h1, h2, h3, feWord_val, Proof.X25519.toFe_self]

/-- The words of `baseOddWords` at `T` are the entries. -/
theorem baseTbl_entry {m : Mem} {T : Addr}
    (hheld : ∀ i < 2048, m.readW (T + BitVec.ofNat 64 (8 * i)) 64 = baseOddWords.getD i 0)
    (j : Nat) (hj : j < 128) :
    tablePoint m (off T (128 * j)) 0 = baseOddCached (baseOddAffine.getD j (0, 1)) := by
  have h0 := baseField hheld hj (f := 0) (by decide)
  have h1 := baseField hheld hj (f := 1) (by decide)
  have h2 := baseField hheld hj (f := 2) (by decide)
  have h3 := baseField hheld hj (f := 3) (by decide)
  simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul] at h0 h1 h2 h3
  simp only [tablePoint, Nat.zero_add, h0, h1, h2, h3]
  rfl

end VG.Proof.Ed25519.X86_64
