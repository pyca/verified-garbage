import VerifiedGarbage.Proof.Camellia.X86_64.Keys

/-!
# Halves as little-endian words

The key schedule keeps the 64-bit halves of `KL`, `KR`, `KA` and `KB` as ECB
loads them: little-endian words of their big-endian bytes (`WordOf`).
`bswap` turns such a word into the half as a number (`bswap_of_wordOf`).
-/

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64

/-- The little-endian word `w` holds the bytes of `h`, the most significant first. -/
def WordOf (w h : BitVec 64) : Prop :=
  ∀ i < 8, ∀ j < 8, w.getLsbD (8 * i + j) = (Camellia.byteOf h i).getLsbD j

theorem WordOf.xor {w x h k : BitVec 64} (hw : WordOf w h) (hx : WordOf x k) : WordOf (w ^^^ x) (h ^^^ k) :=
  fun i hi j hj => by
    rw [BitVec.getLsbD_xor, hw i hi j hj, hx i hi j hj, Camellia.byteOf_xor, BitVec.getLsbD_xor]

theorem WordOf.congr {w w' h : BitVec 64} (hw : WordOf w h) (he : w' = w) : WordOf w' h := he ▸ hw

theorem wordOf_readW (m : Mem) (a : Addr) : WordOf (m.readW a 64) (Spec.Camellia.wordAt m a) :=
  fun i hi j hj => by rw [readW64_bit m a hi hj, byteOf_wordAt m a hi]

theorem wordOf_iff_rel {w h : BitVec 64} : WordOf w h ↔ Camellia.WordRel (fun _ => w) (fun _ => h) :=
  ⟨fun hw _ _ i hi j hj => hw i hi j hj, fun hw i hi j hj => hw 0 (by decide) i hi j hj⟩

theorem bswap64_bit (a : BitVec 64) {i j : Nat} (hi : i < 8) (hj : j < 8) :
    (bswap64 a).getLsbD (56 - 8 * i + j) = a.getLsbD (8 * i + j) := by
  unfold bswap64
  change BitVec.getLsbD (w := 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8) _ _ = _
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  repeat' split
  all_goals (rw [decide_eq_true (by omega), Bool.true_and]; congr 1; omega)

/-- `bswap` of such a word is the half. -/
theorem bswap_of_wordOf {w h : BitVec 64} (hw : WordOf w h) : bswap64 w = h := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  have h1 := bswap64_bit w (i := (63 - t) / 8) (j := t % 8) (by omega) (by omega)
  rw [show 56 - 8 * ((63 - t) / 8) + t % 8 = t by omega] at h1
  rw [h1, hw _ (by omega) _ (by omega), Camellia.getLsbD_byteOf _ (by omega) (by omega)]
  congr 1; omega

end VG.Proof.Camellia.X86_64
