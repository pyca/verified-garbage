import VerifiedGarbage.Proof.Modes.Addr

/-!
# Unchaining CBC blocks, in memory

What one word of a CBC decryption's unchaining does to memory
(`unchainMem`), on any 64-bit target: the decrypted word at `a` XORed with
the chaining value's at `h`, back to `a`; the ciphertext's word at `e` to
`h`; the plaintext's from `a` to `e`. `unchainBlock_apply` reads a byte
after both words of a block. Each target's loop (`Proof/Modes/<Target>/Unchain.lean`)
makes these stores. Nothing here depends on a cipher or a target.
-/

namespace VG.Proof.Modes

open VG

/-! ## Addresses -/

theorem off_self (p : Addr) {i : Nat} (hi : i < 2 ^ 64) : (p + BitVec.ofNat 64 i - p).toNat = i := by
  rw [VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]

/-- A byte of one region is not within `n` bytes of another's (disjoint)
region's address `q`. -/
theorem not_near {p q : Addr} {np nq i n : Nat} (hd : Region.Disjoint ⟨p, np⟩ ⟨q, nq⟩) (hi : i < np)
    (hn : n ≤ nq) (hnp : np ≤ 2 ^ 64) : ¬ (p + BitVec.ofNat 64 i - q).toNat < n := fun h =>
  hd (p + BitVec.ofNat 64 i) (by simp only [Region.Contains]; rw [off_self p (by omega)]; omega)
    (by simp only [Region.Contains]; omega)

/-- An address within `n` bytes of `q` is not within `n'` bytes of an
address `p` whose region is disjoint from `q`'s. -/
theorem not_near' {x p q : Addr} {n n' : Nat} (hd : Region.Disjoint ⟨p, n'⟩ ⟨q, n⟩) (hx : (x - q).toNat < n) :
    ¬ (x - p).toNat < n' := fun h =>
  hd x (by simp only [Region.Contains]; omega) (by simp only [Region.Contains]; omega)

theorem sub_add8_lt {x p : Addr} (h : (x - (p + BitVec.ofNat 64 8)).toNat < 8) :
    (x - p).toNat = 8 + (x - (p + BitVec.ofNat 64 8)).toNat := by
  bv_omega

theorem sub_add8_of {x p : Addr} (h1 : 8 ≤ (x - p).toNat) (h2 : (x - p).toNat < 16) :
    (x - (p + BitVec.ofNat 64 8)).toNat < 8 := by
  bv_omega

/-! ## One word, one block -/

/-- One word of `unchainWord`, in memory: the decrypted word at `a` XORed
with the chaining value's at `h`, to `a`; the ciphertext's at `e` to `h`; the
plaintext's from `a` to `e`. -/
def unchainMem (m : Mem) (a h e : Addr) : Mem :=
  let m₁ := m.writeW a (m.readW a 64 ^^^ m.readW h 64)
  let m₂ := m₁.writeW h (m₁.readW e 64)
  m₂.writeW e (m₂.readW a 64)

theorem unchainMem_apply (m : Mem) {a h e : Addr} (x : Addr) (hah : Region.Disjoint ⟨a, 8⟩ ⟨h, 8⟩)
    (hae : Region.Disjoint ⟨a, 8⟩ ⟨e, 8⟩) :
    unchainMem m a h e x =
      if (x - e).toNat < 8 then
        m (a + BitVec.ofNat 64 (x - e).toNat) ^^^ m (h + BitVec.ofNat 64 (x - e).toNat)
      else if (x - h).toNat < 8 then m (e + BitVec.ofNat 64 (x - h).toNat)
      else if (x - a).toNat < 8 then
        m (a + BitVec.ofNat 64 (x - a).toNat) ^^^ m (h + BitVec.ofNat 64 (x - a).toNat)
      else m x := by
  simp only [unchainMem]
  rw [writeW_readW_apply]
  by_cases he : (x - e).toNat < 8
  · rw [ite_eq_left he, ite_eq_left he, writeW_readW_apply, ite_eq_right (not_near hah he (Nat.le_refl _) (by decide)),
      writeW_xor_apply, ite_eq_left (by rw [off_self a (by omega)]; exact he), off_self a (by omega)]
  · rw [ite_eq_right he, ite_eq_right he, writeW_readW_apply]
    by_cases hh : (x - h).toNat < 8
    · rw [ite_eq_left hh, ite_eq_left hh, writeW_xor_apply,
        ite_eq_right (not_near (fun y h1 h2 => hae y h2 h1) hh (Nat.le_refl _) (by decide))]
    · rw [ite_eq_right hh, ite_eq_right hh, writeW_xor_apply]

theorem disj8_lo {p q : Addr} (h : Region.Disjoint ⟨p, 16⟩ ⟨q, 16⟩) : Region.Disjoint ⟨p, 8⟩ ⟨q, 8⟩ :=
  fun y h1 h2 => h y (by simp only [Region.Contains] at h1 ⊢; omega) (by simp only [Region.Contains] at h2 ⊢; omega)

theorem disj8_hi {p q : Addr} (h : Region.Disjoint ⟨p, 16⟩ ⟨q, 16⟩) :
    Region.Disjoint ⟨p + BitVec.ofNat 64 8, 8⟩ ⟨q + BitVec.ofNat 64 8, 8⟩ := fun y h1 h2 => by
  simp only [Region.Contains] at h1 h2
  exact h y (by simp only [Region.Contains]; rw [sub_add8_lt (by omega)]; omega)
    (by simp only [Region.Contains]; rw [sub_add8_lt (by omega)]; omega)

/-- A byte after both words of a block: `e` gets the decrypted block at `a`
XORed with the chaining value at `h`, `h` the ciphertext block at `e`, and
`a` the same as `e`. -/
theorem unchainBlock_apply (m : Mem) {a h e : Addr} (x : Addr) (hah : Region.Disjoint ⟨a, 16⟩ ⟨h, 16⟩)
    (hae : Region.Disjoint ⟨a, 16⟩ ⟨e, 16⟩) (hhe : Region.Disjoint ⟨h, 16⟩ ⟨e, 16⟩) :
    unchainMem (unchainMem m a h e) (a + BitVec.ofNat 64 8) (h + BitVec.ofNat 64 8) (e + BitVec.ofNat 64 8) x =
      if (x - e).toNat < 16 then
        m (a + BitVec.ofNat 64 (x - e).toNat) ^^^ m (h + BitVec.ofNat 64 (x - e).toNat)
      else if (x - h).toNat < 16 then m (e + BitVec.ofNat 64 (x - h).toNat)
      else if (x - a).toNat < 16 then
        m (a + BitVec.ofNat 64 (x - a).toNat) ^^^ m (h + BitVec.ofNat 64 (x - a).toNat)
      else m x := by
  have hea : Region.Disjoint ⟨e, 16⟩ ⟨a, 16⟩ := fun y h1 h2 => hae y h2 h1
  have heh : Region.Disjoint ⟨e, 16⟩ ⟨h, 16⟩ := fun y h1 h2 => hhe y h2 h1
  have hha : Region.Disjoint ⟨h, 16⟩ ⟨a, 16⟩ := fun y h1 h2 => hah y h2 h1
  -- The inner word at an offset `8 + i` of the block at `p`.
  have inner : ∀ {p : Addr} {i : Nat}, i < 8 → (p = a ∨ p = h ∨ p = e) →
      unchainMem m a h e (p + BitVec.ofNat 64 8 + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 (8 + i)) := by
    intro p i hi hp
    rw [VG.Offset.add_add, unchainMem_apply m _ (disj8_lo hah) (disj8_lo hae)]
    have hs : (p + BitVec.ofNat 64 (8 + i) - p).toNat = 8 + i := off_self p (by omega)
    rcases hp with rfl | rfl | rfl
    · rw [ite_eq_right (not_near hae (by omega) (by decide) (by decide)),
        ite_eq_right (not_near hah (by omega) (by decide) (by decide)), ite_eq_right (by omega)]
    · rw [ite_eq_right (not_near hhe (by omega) (by decide) (by decide)), ite_eq_right (by omega),
        ite_eq_right (not_near hha (by omega) (by decide) (by decide))]
    · rw [ite_eq_right (by omega), ite_eq_right (not_near heh (by omega) (by decide) (by decide)),
        ite_eq_right (not_near hea (by omega) (by decide) (by decide))]
  rw [unchainMem_apply _ _ (disj8_hi hah) (disj8_hi hae)]
  by_cases e1 : (x - (e + BitVec.ofNat 64 8)).toNat < 8
  · rw [ite_eq_left e1, inner e1 (.inl rfl), inner e1 (.inr (.inl rfl)), ← sub_add8_lt e1,
      ite_eq_left (by rw [sub_add8_lt e1]; omega)]
  · rw [ite_eq_right e1]
    by_cases h1 : (x - (h + BitVec.ofNat 64 8)).toNat < 8
    · have hx : (x - h).toNat < 16 := by rw [sub_add8_lt h1]; omega
      rw [ite_eq_left h1, inner h1 (.inr (.inr rfl)), ← sub_add8_lt h1, ite_eq_right (not_near' heh hx), ite_eq_left hx]
    · rw [ite_eq_right h1]
      by_cases a1 : (x - (a + BitVec.ofNat 64 8)).toNat < 8
      · have hx : (x - a).toNat < 16 := by rw [sub_add8_lt a1]; omega
        rw [ite_eq_left a1, inner a1 (.inl rfl), inner a1 (.inr (.inl rfl)), ← sub_add8_lt a1,
          ite_eq_right (not_near' hea hx), ite_eq_right (not_near' hha hx), ite_eq_left hx]
      · rw [ite_eq_right a1, unchainMem_apply m _ (disj8_lo hah) (disj8_lo hae)]
        by_cases e0 : (x - e).toNat < 8
        · rw [ite_eq_left e0, ite_eq_left (by omega)]
        · rw [ite_eq_right e0]
          have e16 : ¬ (x - e).toNat < 16 := fun h => e1 (sub_add8_of (by omega) h)
          rw [ite_eq_right e16]
          by_cases h0 : (x - h).toNat < 8
          · rw [ite_eq_left h0, ite_eq_left (by omega)]
          · rw [ite_eq_right h0]
            have h16 : ¬ (x - h).toNat < 16 := fun h' => h1 (sub_add8_of (by omega) h')
            rw [ite_eq_right h16]
            by_cases a0 : (x - a).toNat < 8
            · rw [ite_eq_left a0, ite_eq_left (by omega)]
            · rw [ite_eq_right a0, ite_eq_right fun h' => a1 (sub_add8_of (by omega) h')]

end VG.Proof.Modes
