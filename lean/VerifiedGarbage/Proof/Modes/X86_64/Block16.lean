import VerifiedGarbage.Proof.Modes.X86_64.Unchain

/-!
# Blocks of 16 bytes, a word at a time, on x86-64

The memory after two 8-byte stores that copy a block (`copy16_in`) or XOR
one into another (`xor16_in`), read a byte at a time, and the bytes outside
the block (`two_out`).
-/

namespace VG.Proof.Modes.X86_64

open VG

/-- A block copied from `c` to `a`, a word at a time. -/
abbrev copy16 (m : Mem) (a c : Addr) : Mem :=
  (m.writeW a (m.readW c 64)).writeW (a + BitVec.ofNat 64 8)
    ((m.writeW a (m.readW c 64)).readW (c + BitVec.ofNat 64 8) 64)

/-- The block at `c` XORed into the one at `a`, a word at a time. -/
abbrev xor16 (m : Mem) (a c : Addr) : Mem :=
  (m.writeW a (m.readW a 64 ^^^ m.readW c 64)).writeW (a + BitVec.ofNat 64 8)
    ((m.writeW a (m.readW a 64 ^^^ m.readW c 64)).readW (a + BitVec.ofNat 64 8) 64 ^^^
      (m.writeW a (m.readW a 64 ^^^ m.readW c 64)).readW (c + BitVec.ofNat 64 8) 64)

theorem two_out {m : Mem} {a : Addr} {v₀ v₁ : BitVec 64} {x : Addr} (hx : ¬ (x - a).toNat < 16) :
    (m.writeW a v₀).writeW (a + BitVec.ofNat 64 8) v₁ x = m x := by
  have h8 : ¬ (x - (a + BitVec.ofNat 64 8)).toNat < 8 := fun h => hx (by rw [sub_add8_lt h]; omega)
  rw [Mem.writeW, Mem.write_apply h8, Mem.writeW, Mem.write_apply (show ¬ (x - a).toNat < 8 by omega)]

/-- A byte of `c`'s block is not in the first word at `a`, nor is the byte
of `a`'s block `8 + i` for `i < 8`. -/
theorem not_word {a c : Addr} (hd : Region.Disjoint ⟨a, 16⟩ ⟨c, 16⟩) {i : Nat} (hi : i < 16) :
    ¬ (c + BitVec.ofNat 64 i - a).toNat < 8 :=
  not_near (n := 8) (fun y h1 h2 => hd y h2 h1) hi (by decide) (by decide)

theorem copy16_in (m : Mem) {a c : Addr} (hd : Region.Disjoint ⟨a, 16⟩ ⟨c, 16⟩) {u : Nat} (hu : u < 16) :
    copy16 m a c (a + BitVec.ofNat 64 u) = m (c + BitVec.ofNat 64 u) := by
  simp only [copy16]
  rw [writeW_readW_apply]
  by_cases h8 : 8 ≤ u
  · rw [ite_eq_left (by rw [off_sub_toNat a h8 (by omega)]; omega), off_sub_toNat a h8 (by omega),
      VG.Offset.add_add, show 8 + (u - 8) = u by omega, writeW_readW_apply, ite_eq_right (not_word hd hu)]
  · rw [ite_eq_right (off_sub_not a (Or.inl (by omega : u < 8)) (by omega) (by decide) (by decide)),
      writeW_readW_apply, ite_eq_left (by rw [off_self a (by omega)]; omega), off_self a (by omega)]

theorem xor16_in (m : Mem) {a c : Addr} (hd : Region.Disjoint ⟨a, 16⟩ ⟨c, 16⟩) {u : Nat} (hu : u < 16) :
    xor16 m a c (a + BitVec.ofNat 64 u) = m (a + BitVec.ofNat 64 u) ^^^ m (c + BitVec.ofNat 64 u) := by
  simp only [xor16]
  rw [writeW_xor_apply]
  by_cases h8 : 8 ≤ u
  · have hn : ¬ (a + BitVec.ofNat 64 u - a).toNat < 8 := by rw [off_self a (by omega)]; omega
    rw [ite_eq_left (by rw [off_sub_toNat a h8 (by omega)]; omega), off_sub_toNat a h8 (by omega),
      VG.Offset.add_add, VG.Offset.add_add, show 8 + (u - 8) = u by omega, writeW_xor_apply, ite_eq_right hn,
      writeW_xor_apply, ite_eq_right (not_word hd hu)]
  · rw [ite_eq_right (off_sub_not a (Or.inl (by omega : u < 8)) (by omega) (by decide) (by decide)),
      writeW_xor_apply, ite_eq_left (by rw [off_self a (by omega)]; omega), off_self a (by omega)]

end VG.Proof.Modes.X86_64
