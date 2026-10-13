module

public import VerifiedGarbage.Proof.Bignum.CrtWindowFiveLayout

/-! Frames for prime workspaces with 32-entry exponentiation tables. -/

@[expose] public section
namespace VG.Proof.Bignum.CrtWindowFive
open VG VG.Impl.Bignum VG.Proof.Bignum

/-- What code in a prime's workspace may change, at `B`: all but its link,
`w_X`, `-X⁻¹` and its arrays' bases. -/
def xRange32 (o wx : Nat) : Nat × Nat := (o + 8 * 17, slot wx 8 + tabBytes32 wx - 8 * 17)

theorem to_x32 {B : Addr} {o wx : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm (off B o) rs m m')
    (hr : ∀ r ∈ rs, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot wx 8) (ho : o + slot wx 8 ≤ 2 ^ 64)
    {rs' : List (Nat × Nat)} (hx : xRange32 o wx ∈ rs') : Frm B rs' m m' := by
  have h256 : 8 * 17 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  refine (Frm.rebase h (by omega) fun r hr' => by have := hr r hr'; omega).widen fun r hr' => ⟨_, hx, ?_⟩
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr'
  have := hr r₀ hr₀
  simp only [xRange32]
  omega

/-- `to_x32` for changes that reach the table. -/
theorem to_xT32 {B : Addr} {o wx : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm (off B o) rs m m')
    (hr : ∀ r ∈ rs, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot wx 8 + tabBytes32 wx) (ho : o + (slot wx 8 + tabBytes32 wx) ≤ 2 ^ 64)
    {rs' : List (Nat × Nat)} (hx : xRange32 o wx ∈ rs') : Frm B rs' m m' := by
  have h256 : 8 * 17 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  refine (Frm.rebase h (by omega) fun r hr' => by have := hr r hr'; omega).widen fun r hr' => ⟨_, hx, ?_⟩
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr'
  have := hr r₀ hr₀
  simp only [xRange32]
  omega

theorem outside_to_x32 {B : Addr} {o wx j : Nat} {m m' : Mem} (h : Outside (off B o) (slot wx j) (8 * (wx + 2)) m m')
    (hj : j < 8) (ho : o + slot wx 8 ≤ 2 ^ 64) {rs' : List (Nat × Nat)} (hx : xRange32 o wx ∈ rs') :
    Frm B rs' m m' :=
  to_x32 (rs := [(slot wx j, 8 * (wx + 2))]) (Frm.of_outside h (by simp)) (fun r hr => by
    rw [List.mem_singleton.mp hr]
    have := slot_le (w := wx) hj
    have := hdr_lt_slot wx j (show 31 < 32 by decide)
    simp only; omega) ho hx

/-- The words of the modulus' header and arrays, below `o`, past code in
the prime's workspace. -/
theorem x_below32 {B : Addr} {o wx : Nat} {m m' : Mem} (h : Frm B [xRange32 o wx] m m') {d : Nat}
    (hd : d + 8 ≤ o) (ho : o < 2 ^ 64) : word m' B d = word m B d :=
  h.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [xRange32]; omega) (by omega)


end VG.Proof.Bignum.CrtWindowFive
