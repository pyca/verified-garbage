import VerifiedGarbage.Proof.Mont.Words

/-!
# Numbers in memory as `Mem.read` reads them

`Mem.read` reads `n` bytes little-endian; split after `p` bytes, its value is
that of the first `p` bytes plus `2^(8p)` times that of the rest
(`read_toNat_add`), so the `k` 64-bit words at `base + d` are the `8k` bytes
there (`read_eq_wordsVal`).
-/

namespace VG.Proof.Mont

theorem read_toNat_succ (m : Mem) (a : Addr) (n : Nat) :
    (m.read a (n + 1)).toNat = (m a).toNat + 2 ^ 8 * (m.read (a + 1) n).toNat := by
  show (m.read (a + 1) n ++ m a).toNat = _
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (m a).isLt, Nat.shiftLeft_eq, Nat.mul_comm]
  omega

theorem read_toNat_add (m : Mem) (n : Nat) : ∀ (p : Nat) (a : Addr),
    (m.read a (n + p)).toNat = (m.read a p).toNat + 2 ^ (8 * p) * (m.read (a + BitVec.ofNat 64 p) n).toNat
  | 0, a => by simp [Mem.read]
  | p + 1, a => by
    rw [show n + (p + 1) = n + p + 1 from rfl, read_toNat_succ, read_toNat_add m n p (a + 1), read_toNat_succ,
      show a + 1 + BitVec.ofNat 64 p = a + BitVec.ofNat 64 (p + 1) by
        rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega,
      show 8 * (p + 1) = 8 + 8 * p by omega, Nat.pow_add]
    grind

/-- The `k` words at `base + d` are its `8k` bytes. -/
theorem read_eq_wordsVal (m : Mem) (base : Addr) : ∀ (k d : Nat),
    (m.read (off base d) (8 * k)).toNat = wordsVal m base d k
  | 0, d => by simp [Mem.read, wordsVal]
  | k + 1, d => by
    rw [show 8 * (k + 1) = 8 * k + 8 from rfl, read_toNat_add, wordsVal, ← read_eq_wordsVal m base k (d + 8),
      Offset.add_add]
    congr 1

end VG.Proof.Mont
