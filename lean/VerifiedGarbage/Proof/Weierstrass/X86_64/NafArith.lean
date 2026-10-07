/-! Linear facts about the products of the limb count and an index, which
`omega` treats as atoms: the end of entry `j` of a table, and coordinate
offsets. -/
namespace VG.Proof.Weierstrass.X86_64

/-- Entry `j < k` of a table of `m`-byte entries ends within it. -/
theorem entry_end_le (m : Nat) {j k : Nat} (h : j<k) : m*j+m≤m*k := by
  have := Nat.mul_le_mul_left m (Nat.succ_le_of_lt h)
  rwa [Nat.mul_succ] at this

/-- Entry `j ≤ k` of a table of `m`-byte entries starts within it. -/
theorem entry_le (m : Nat) {j k : Nat} (h : j≤k) : m*j≤m*k :=
  Nat.mul_le_mul_left m h

/-- Slot `2 i` of `8 n`-byte slots starts entry `i` of `16 n` bytes. -/
theorem slot_two_mul (n i : Nat) : 8*n*(2*i)=16*n*i := by grind

/-- Slot `2 i + 1` of `8 n`-byte slots is the second half of entry `i` of `16 n` bytes. -/
theorem slot_two_mul_add (n i : Nat) : 8*n*(2*i+1)=16*n*i+8*n := by grind

/-- Slot `3 i + 2` of `8 n`-byte slots is the `Z` of entry `i` of `24 n` bytes. -/
theorem slot_three_mul_two (n i : Nat) : 8*n*(3*i+2)=24*n*i+16*n := by grind

end VG.Proof.Weierstrass.X86_64
