import VerifiedGarbage.Proof.Bignum.X86_64.MontMul

/-!
# Multiword arithmetic on x86-64: workspaces within a working space

`vg_rsa_private_crt` keeps three workspaces in its working space, at
offsets of the first one's base `B`. What code in a workspace at `off B o`
changes is stated at its own base (`Arrays`, `Outside`, `Frm`); these
lemmas restate it at `B`, with the ranges moved by `o` (`Frm.rebase`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64

/-- The offset from `off B o` of an address at offset `d ≥ o` from `B`, or
an offset at least `2^64 - o` for one below `o`. -/
theorem ofs_rebase (B x : Addr) {o : Nat} (ho : o < 2 ^ 64) :
    (o ≤ ofs B x ∧ ofs (off B o) x = ofs B x - o) ∨ (ofs B x < o ∧ 2 ^ 64 - o ≤ ofs (off B o) x) := by
  simp only [ofs, off]
  rw [Offset.toNat_sub_add x B ho]
  have := (x - B).isLt
  by_cases h : o ≤ (x - B).toNat
  · left
    refine ⟨h, ?_⟩
    rw [show 2 ^ 64 - o + (x - B).toNat = (x - B).toNat - o + 2 ^ 64 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · right
    refine ⟨by omega, ?_⟩
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- Ranges at `off B o`, at `B`. -/
def shiftRanges (o : Nat) (rs : List (Nat × Nat)) : List (Nat × Nat) := rs.map fun r => (o + r.1, r.2)

theorem Frm.rebase {B : Addr} {o : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm (off B o) rs m m')
    (ho : o < 2 ^ 64) (hr : ∀ r ∈ rs, o + r.1 + r.2 ≤ 2 ^ 64) : Frm B (shiftRanges o rs) m m' := by
  intro x hx
  apply h x
  intro r hr'
  have hx' := hx (o + r.1, r.2) (List.mem_map.mpr ⟨r, hr', rfl⟩)
  have := hr r hr'
  rcases ofs_rebase B x ho with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only at hx'; omega
  · omega

theorem Frm.of_arrays_off {B : Addr} {o w : Nat} {js : List Nat} {m m' : Mem} (h : Arrays (off B o) w js m m')
    (ho : o < 2 ^ 64) (hw : ∀ j ∈ js, o + slot w j + 8 * (w + 2) ≤ 2 ^ 64) :
    Frm B (shiftRanges o (js.map fun j => (slot w j, 8 * (w + 2)))) m m' :=
  Frm.rebase (Frm.of_arrays h fun j hj => List.mem_map.mpr ⟨j, hj, rfl⟩) ho fun r hr => by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
    exact hw j hj

theorem Frm.of_outside_off {B : Addr} {o d n : Nat} {m m' : Mem} (h : Outside (off B o) d n m m')
    (ho : o < 2 ^ 64) (hd : o + d + n ≤ 2 ^ 64) : Frm B [(o + d, n)] m m' :=
  Frm.rebase (rs := [(d, n)]) (Frm.of_outside h (List.mem_singleton.mpr rfl)) ho fun r hr => by
    rw [List.mem_singleton.mp hr]; exact hd

/-- Two changes, each within ranges of its own, change only within both. -/
theorem Frm.append {B : Addr} {rs rs' : List (Nat × Nat)} {m₁ m₂ m₃ : Mem} (h₁ : Frm B rs m₁ m₂)
    (h₂ : Frm B rs' m₂ m₃) : Frm B (rs ++ rs') m₁ m₃ := fun x hx =>
  (h₂ x fun r hr => hx r (List.mem_append_right _ hr)).trans (h₁ x fun r hr => hx r (List.mem_append_left _ hr))

/-- A word of a workspace at `off B o`, at `B`. -/
theorem word_off (m : Mem) (B : Addr) (o d : Nat) : word m (off B o) d = word m B (o + d) := by
  simp only [word, off_off]

theorem wv_off (m : Mem) (B : Addr) (o d k : Nat) : wv m (off B o) d k = wv m B (o + d) k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [wv, wv, ih, word_off, Nat.add_assoc]

end VG.Proof.Bignum.X86_64
