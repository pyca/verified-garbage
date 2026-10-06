import VerifiedGarbage.Impl.Bignum.X86_64
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# Multiword arithmetic on x86-64: words in the working space

The working space is `size` bytes at `base` (`Scr`), writable and not
wrapping around. A number of `n` words at byte offset `d` of it is
`wv m base d n` (`Proof/Bignum/Words.lean`). The arrays' words are addressed
as `[b + 8 i + disp]` with a base `b = base + e` and an index `i` in
registers (`ea_ix`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (load64_eq store64_eq)

/-! ## The working space -/

/-- The working space: `size` bytes at `base`, within a writable region,
not wrapping around. -/
structure Scr (s : State) (base : Addr) (size : Nat) : Prop where
  wr : ∃ B₀ : Addr, ∃ o L : Nat, (⟨B₀, L⟩ : Region) ∈ s.wr ∧ base = off B₀ o ∧ o + size ≤ L ∧ L ≤ 2 ^ 64
  nowrap : base.toNat + size ≤ 2 ^ 64

/-- A writable region is a working space. -/
theorem Scr.of_mem {s : State} {base : Addr} {size : Nat} (h : (⟨base, size⟩ : Region) ∈ s.wr)
    (hn : base.toNat + size ≤ 2 ^ 64) : Scr s base size :=
  ⟨⟨base, 0, size, h, by simp [off], by omega, by omega⟩, hn⟩

/-- `size` bytes at offset `o` of a working space. -/
theorem Scr.sub {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {o n : Nat}
    (h : o + n ≤ size) (hn0 : 0 < n) : Scr s (off base o) n := by
  obtain ⟨⟨B₀, o₀, L, hm, hb, hL, hL'⟩, hn⟩ := hs
  refine ⟨⟨B₀, o₀ + o, L, hm, ?_, by omega, hL'⟩, ?_⟩
  · subst hb; simp only [off, BitVec.add_assoc, BitVec.ofNat_add]
  · rw [show (off base o).toNat = base.toNat + o by
      simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]]
    omega

theorem Scr.region {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d n : Nat}
    (h : d + n ≤ size) (hn : 0 < n) : ∃ r ∈ s.wr, r.Contains (off base d) n := by
  obtain ⟨⟨B₀, o, L, hm, hb, hL, hL'⟩, _⟩ := hs
  refine ⟨_, hm, ?_⟩
  rw [hb, show off (off B₀ o) d = off B₀ (o + d) by simp only [off, BitVec.add_assoc, BitVec.ofNat_add]]
  exact Offset.contains_base B₀ (by omega) (by omega)

theorem Scr.ld {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) : InRegions (s.rd ++ s.wr) (off base d) 8 :=
  let ⟨_, hm, hc⟩ := hs.region hd (by decide)
  ⟨_, List.mem_append_right _ hm, hc⟩

theorem Scr.st {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) : InRegions s.wr (off base d) 8 :=
  let ⟨_, hm, hc⟩ := hs.region hd (by decide)
  ⟨_, hm, hc⟩

theorem Scr.st8 {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d + 1 ≤ size) : InRegions s.wr (off base d) 1 :=
  let ⟨_, hm, hc⟩ := hs.region hd (by decide)
  ⟨_, hm, hc⟩

theorem Scr.congr {s s' : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (h : s'.wr = s.wr) : Scr s' base size :=
  ⟨let ⟨B₀, o, L, hm, hb, hL, hL'⟩ := hs.wr; ⟨B₀, o, L, h ▸ hm, hb, hL, hL'⟩, hs.nowrap⟩

/-! ## Addresses -/

/-- `[b + 8 i + d]` for `b = p + e` and `i = j`. -/
theorem ea_ix (s : State) {b i : Reg} {p : Addr} {e j : Nat} (hb : s.gpr b = off p e)
    (hi : s.gpr i = BitVec.ofNat 64 j) (d : Nat) :
    s.ea (ix b i (Int.ofNat d)) = off p (e + 8 * j + d) := by
  simp only [State.ea, ix, hb, hi, off, ofInt_ofNat, ofNat_mul8, BitVec.add_assoc, BitVec.ofNat_add]

theorem ea_ix0 (s : State) {b i : Reg} {p : Addr} {e j : Nat} (hb : s.gpr b = off p e)
    (hi : s.gpr i = BitVec.ofNat 64 j) : s.ea (ix b i) = off p (e + 8 * j) := by
  have := ea_ix s hb hi 0
  rwa [Nat.add_zero] at this

theorem ea_ix8 (s : State) {b i : Reg} {p : Addr} {e j : Nat} (hb : s.gpr b = off p e)
    (hi : s.gpr i = BitVec.ofNat 64 j) : s.ea (ix b i 8) = off p (e + 8 * j + 8) :=
  ea_ix s hb hi 8

/-- `[b + 8 i - 8]` for `b = p + e` and `i = j ≥ 1`. -/
theorem ea_ixm8 (s : State) {b i : Reg} {p : Addr} {e j : Nat} (hb : s.gpr b = off p e)
    (hi : s.gpr i = BitVec.ofNat 64 j) (hj : 1 ≤ j) :
    s.ea (ix b i (-8)) = off p (e + 8 * (j - 1)) := by
  have h8 : BitVec.ofNat 64 (8 * j) + BitVec.ofInt 64 (-8) = BitVec.ofNat 64 (8 * (j - 1)) := by
    rw [show (-8 : Int) = - ((8 : Nat) : Int) by rfl, BitVec.ofInt_neg, BitVec.ofInt_natCast,
      ← BitVec.sub_eq_add_neg, show 8 * j = 8 * (j - 1) + 8 by omega, BitVec.ofNat_add,
      BitVec.add_sub_cancel]
  simp only [State.ea, ix, hb, hi, off, ofNat_mul8, BitVec.add_assoc, h8, BitVec.ofNat_add]

theorem ea_at0 (s : State) {b : Reg} {p : Addr} {e : Nat} (hb : s.gpr b = off p e) :
    s.ea (at0 b) = off p e := by
  simp only [State.ea, at0, hb, BitVec.ofInt_ofNat, BitVec.add_zero]

theorem ea_hdr (s : State) {p : Addr} (hb : s.gpr .rdi = p) (i : Nat) :
    s.ea (hdr i) = off p (8 * i) := by
  simp only [State.ea, hdr, hb, off]
  rw [show (8 * (i : Int)) = ((8 * i : Nat) : Int) by omega, BitVec.ofInt_natCast]

end VG.Proof.Bignum.X86_64
