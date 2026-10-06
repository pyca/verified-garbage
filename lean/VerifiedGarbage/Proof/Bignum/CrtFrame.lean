import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Impl.Bignum.CrtLayout

/-!
# Multiword arithmetic: workspaces within a working space

`vg_rsa_private_crt` keeps three workspaces in its working space, at
offsets of the first one's base `B`. What code in a workspace at `off B o`
changes is stated at its own base (`Arrays`, `Outside`, `Frm`); these
lemmas restate it at `B`, with the ranges moved by `o` (`Frm.rebase`).
-/

namespace VG.Proof.Bignum

open VG VG.Impl.Bignum

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

/-- Below `off B o`: a change within `L` bytes of `off B o` keeps the
words at offsets below `o` from `B`. -/
theorem Frm.word_below {B : Addr} {o L : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm (off B o) rs m m')
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ L) (hL : o + L ≤ 2 ^ 64) (ho : o < 2 ^ 64) {d : Nat} (hd : d + 8 ≤ o) :
    word m' B d = word m B d :=
  (Mem.readW_congr fun i hi => (h _ fun r hr' => by
    have := hr r hr'
    rcases ofs_rebase B (off B d + BitVec.ofNat 64 i) ho with ⟨h1, _⟩ | ⟨_, h2⟩
    · rw [ofs_off B (by omega)] at h1; omega
    · omega).symm).symm

theorem Frm.wv_below {B : Addr} {o L : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm (off B o) rs m m')
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ L) (hL : o + L ≤ 2 ^ 64) (ho : o < 2 ^ 64) {d k : Nat} (hd : d + 8 * k ≤ o) :
    wv m' B d k = wv m B d k :=
  wv_congr fun i hi => h.word_below hr hL ho (by omega)

/-! ## A prime's workspace -/

/-- A change within ranges, each within one of `rs'`, is within `rs'`. -/
theorem Frm.widen {B : Addr} {rs rs' : List (Nat × Nat)} {m m' : Mem} (h : Frm B rs m m')
    (hr : ∀ r ∈ rs, ∃ r' ∈ rs', r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2) : Frm B rs' m m' := fun x hx =>
  h x fun r hr' => by
    obtain ⟨r', hr'', h1, h2⟩ := hr r hr'
    have := hx r' hr''
    omega

/-- The size of the window's table after a prime's arrays: 16 entries of
`8 (w_X + 2)` bytes. -/
def tabBytes (wx : Nat) : Nat := 16 * (8 * (wx + 2))

/-- The words of a prime's workspace for a length of `len` bytes. -/
def wsWords (len : Nat) : Nat := max 2 ((len + 7) / 8)

theorem wsWords_le {len w : Nat} (h : len < 8 * w) (hw : 2 ≤ w) : wsWords len ≤ w := by
  unfold wsWords; omega

/-- The workspaces' layout: `p`'s after the modulus', `q`'s after `p`'s. -/
def offP (w : Nat) : Nat := slot w 8
def offQ (w pl : Nat) : Nat := slot w 8 + slot (wsWords pl) 8 + tabBytes (wsWords pl)

/-- A prime's workspace at `off B o`: its header and its link to `B`. -/
structure WsAt (m : Mem) (B : Addr) (o wx : Nat) (minv : BitVec 64) : Prop where
  hdr : Hdr m (off B o) wx minv
  link : word m (off B o) (8 * Crt.sLink) = B

theorem WsAt.of_words {m m' : Mem} {B : Addr} {o wx : Nat} {minv : BitVec 64} (h : WsAt m B o wx minv)
    (hw : ∀ i < 17, word m' (off B o) (8 * i) = word m (off B o) (8 * i)) : WsAt m' B o wx minv :=
  ⟨⟨(hw _ (by decide)).trans h.hdr.hw, (hw _ (by decide)).trans h.hdr.hminv,
    fun j hj => (hw _ (by unfold sArr; omega)).trans (h.hdr.harr j hj)⟩, (hw _ (by decide)).trans h.link⟩

/-- The header of the workspace at `off B o` with whatever `-X⁻¹` it holds. -/
theorem hdr_any {m : Mem} {B : Addr} {o wx : Nat} (hw : word m (off B o) (8 * sW) = BitVec.ofNat 64 wx)
    (ha : ∀ j < 8, word m (off B o) (8 * sArr j) = off (off B o) (slot wx j)) :
    Hdr m (off B o) wx (word m (off B o) (8 * sMinv)) :=
  ⟨hw, rfl, ha⟩

/-- What a load into an array of the workspace at `off B o` changes, at `B`:
within its arrays. -/
theorem Frm.of_load {B : Addr} {o wx j : Nat} {m m' : Mem} {rs : List (Nat × Nat)}
    (h : Outside (off B o) (slot wx j) (8 * (wx + 2)) m m') (hj : j < 8) (ho : o + slot wx 8 ≤ 2 ^ 64)
    (hr : (o + 256, slot wx 8 - 256) ∈ rs) : Frm B rs m m' := by
  have h1 := slot_le (w := wx) hj
  have h2 := hdr_lt_slot wx j (show 31 < 32 by decide)
  have h3 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  refine (Frm.of_outside_off h (by omega) (by omega)).widen fun r hr' => ⟨_, hr, ?_⟩
  rw [List.mem_singleton.mp hr']
  simp only
  omega

/-- What code in a prime's workspace may change, at `B`: all but its link,
`w_X`, `-X⁻¹` and its arrays' bases. -/
def xRange (o wx : Nat) : Nat × Nat := (o + 8 * 17, slot wx 8 + tabBytes wx - 8 * 17)

theorem Frm.to_x {B : Addr} {o wx : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm (off B o) rs m m')
    (hr : ∀ r ∈ rs, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot wx 8) (ho : o + slot wx 8 ≤ 2 ^ 64)
    {rs' : List (Nat × Nat)} (hx : xRange o wx ∈ rs') : Frm B rs' m m' := by
  have h256 : 8 * 17 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  refine (h.rebase (by omega) fun r hr' => by have := hr r hr'; omega).widen fun r hr' => ⟨_, hx, ?_⟩
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr'
  have := hr r₀ hr₀
  simp only [xRange]
  omega

/-- `Frm.to_x` for changes that reach the table. -/
theorem Frm.to_xT {B : Addr} {o wx : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm (off B o) rs m m')
    (hr : ∀ r ∈ rs, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot wx 8 + tabBytes wx) (ho : o + (slot wx 8 + tabBytes wx) ≤ 2 ^ 64)
    {rs' : List (Nat × Nat)} (hx : xRange o wx ∈ rs') : Frm B rs' m m' := by
  have h256 : 8 * 17 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  refine (h.rebase (by omega) fun r hr' => by have := hr r hr'; omega).widen fun r hr' => ⟨_, hx, ?_⟩
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr'
  have := hr r₀ hr₀
  simp only [xRange]
  omega

theorem Outside.to_x {B : Addr} {o wx j : Nat} {m m' : Mem} (h : Outside (off B o) (slot wx j) (8 * (wx + 2)) m m')
    (hj : j < 8) (ho : o + slot wx 8 ≤ 2 ^ 64) {rs' : List (Nat × Nat)} (hx : xRange o wx ∈ rs') :
    Frm B rs' m m' :=
  Frm.to_x (rs := [(slot wx j, 8 * (wx + 2))]) (Frm.of_outside h (by simp)) (fun r hr => by
    rw [List.mem_singleton.mp hr]
    have := slot_le (w := wx) hj
    have := hdr_lt_slot wx j (show 31 < 32 by decide)
    simp only; omega) ho hx

/-- The words of the modulus' header and arrays, below `o`, past code in
the prime's workspace. -/
theorem Frm.x_below {B : Addr} {o wx : Nat} {m m' : Mem} (h : Frm B [xRange o wx] m m') {d : Nat}
    (hd : d + 8 ≤ o) (ho : o < 2 ^ 64) : word m' B d = word m B d :=
  h.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [xRange]; omega) (by omega)

end VG.Proof.Bignum
