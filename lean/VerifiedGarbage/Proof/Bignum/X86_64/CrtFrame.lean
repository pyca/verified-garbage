import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Impl.Rsa.X86_64.Crt

/-!
# Multiword arithmetic on x86-64: workspaces within a working space

`vg_rsa_private_crt` keeps three workspaces in its working space, at
offsets of the first one's base `B`. What code in a workspace at `off B o`
changes is stated at its own base (`Arrays`, `Outside`, `Frm`); these
lemmas restate it at `B`, with the ranges moved by `o` (`Frm.rebase`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Crt

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

theorem _root_.VG.Proof.Bignum.Frm.rebase {B : Addr} {o : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm (off B o) rs m m')
    (ho : o < 2 ^ 64) (hr : ∀ r ∈ rs, o + r.1 + r.2 ≤ 2 ^ 64) : Frm B (shiftRanges o rs) m m' := by
  intro x hx
  apply h x
  intro r hr'
  have hx' := hx (o + r.1, r.2) (List.mem_map.mpr ⟨r, hr', rfl⟩)
  have := hr r hr'
  rcases ofs_rebase B x ho with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only at hx'; omega
  · omega

theorem _root_.VG.Proof.Bignum.Frm.of_arrays_off {B : Addr} {o w : Nat} {js : List Nat} {m m' : Mem} (h : Arrays (off B o) w js m m')
    (ho : o < 2 ^ 64) (hw : ∀ j ∈ js, o + slot w j + 8 * (w + 2) ≤ 2 ^ 64) :
    Frm B (shiftRanges o (js.map fun j => (slot w j, 8 * (w + 2)))) m m' :=
  Frm.rebase (Frm.of_arrays h fun j hj => List.mem_map.mpr ⟨j, hj, rfl⟩) ho fun r hr => by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
    exact hw j hj

theorem _root_.VG.Proof.Bignum.Frm.of_outside_off {B : Addr} {o d n : Nat} {m m' : Mem} (h : Outside (off B o) d n m m')
    (ho : o < 2 ^ 64) (hd : o + d + n ≤ 2 ^ 64) : Frm B [(o + d, n)] m m' :=
  Frm.rebase (rs := [(d, n)]) (Frm.of_outside h (List.mem_singleton.mpr rfl)) ho fun r hr => by
    rw [List.mem_singleton.mp hr]; exact hd

/-- Two changes, each within ranges of its own, change only within both. -/
theorem _root_.VG.Proof.Bignum.Frm.append {B : Addr} {rs rs' : List (Nat × Nat)} {m₁ m₂ m₃ : Mem} (h₁ : Frm B rs m₁ m₂)
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
theorem _root_.VG.Proof.Bignum.Frm.word_below {B : Addr} {o L : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm (off B o) rs m m')
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ L) (hL : o + L ≤ 2 ^ 64) (ho : o < 2 ^ 64) {d : Nat} (hd : d + 8 ≤ o) :
    word m' B d = word m B d :=
  (Mem.readW_congr fun i hi => (h _ fun r hr' => by
    have := hr r hr'
    rcases ofs_rebase B (off B d + BitVec.ofNat 64 i) ho with ⟨h1, _⟩ | ⟨_, h2⟩
    · rw [ofs_off B (by omega)] at h1; omega
    · omega).symm).symm

theorem _root_.VG.Proof.Bignum.Frm.wv_below {B : Addr} {o L : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm (off B o) rs m m')
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ L) (hL : o + L ≤ 2 ^ 64) (ho : o < 2 ^ 64) {d k : Nat} (hd : d + 8 * k ≤ o) :
    wv m' B d k = wv m B d k :=
  wv_congr fun i hi => h.word_below hr hL ho (by omega)

/-! ## A prime's workspace -/

/-- The size of the window's table after a prime's arrays: 16 entries of
`8 (w_X + 2)` bytes. -/
def tabBytes (wx : Nat) : Nat := 16 * (8 * (wx + 2))

open VG.Impl.Bignum.X86_64.Public in
/-- A prime's workspace at `off B o` (`wx` words), its base in `rdi`,
after the modulus' at `B` (`w` words) in the working space, its header
linking back to `B`. -/
structure SubCtx (t : State) (B : Addr) (Z o w wx : Nat) (minv : BitVec 64) : Prop where
  scr : Scr t B Z
  rdi : t.gpr .rdi = off B o
  hdr : Hdr t.mem (off B o) wx minv
  link : word t.mem (off B o) (8 * sLink) = B
  nw : word t.mem B (8 * sW) = BitVec.ofNat 64 w
  narr : ∀ j < 8, word t.mem B (8 * sArr j) = off B (slot w j)
  lo : slot w 8 ≤ o
  hi : o + slot wx 8 + tabBytes wx ≤ Z

theorem SubCtx.good {t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} (h : SubCtx t B Z o w wx minv) :
    Good t (off B o) (slot wx 8) wx minv :=
  ⟨h.scr.sub (by have := h.hi; omega) (by unfold slot hdrBytes; omega), h.rdi, h.hdr⟩

/-- The prime's workspace with its table. -/
theorem SubCtx.scrT {t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} (h : SubCtx t B Z o w wx minv) :
    Scr t (off B o) (slot wx 8 + tabBytes wx) :=
  h.scr.sub (by have := h.hi; omega) (by unfold slot hdrBytes; omega)

/-- What changes within the arrays and the functions' own slots of the
prime's workspace (but its link) keeps it. -/
theorem SubCtx.of_frmT {s t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {rs : List (Nat × Nat)}
    (h : SubCtx s B Z o w wx minv) (hf : Frm (off B o) rs s.mem t.mem)
    (hr : ∀ r ∈ rs, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot wx 8 + tabBytes wx) (hwr : t.wr = s.wr)
    (hdi : t.gpr .rdi = s.gpr .rdi) : SubCtx t B Z o w wx minv := by
  have hn := h.scr.nowrap
  have hi := h.hi
  have hL : o + (slot wx 8 + tabBytes wx) ≤ 2 ^ 64 := by omega
  have hr' : ∀ r ∈ rs, r.1 + r.2 ≤ slot wx 8 + tabBytes wx := fun r hr' => (hr r hr').2
  have hh : ∀ i < 17, word t.mem (off B o) (8 * i) = word s.mem (off B o) (8 * i) := fun i hi' =>
    hf.word_eq (fun r hr' => Or.inl (by have := hr r hr'; omega))
      (by have : 8 * 32 ≤ slot wx 8 := by unfold slot hdrBytes; omega
          omega)
  have hb : ∀ i < 32, word t.mem B (8 * i) = word s.mem B (8 * i) := fun i hi' =>
    hf.word_below hr' hL (by unfold slot hdrBytes at hL; omega) (by have := hdr_lt_slot w 8 hi'; have := h.lo; omega)
  exact ⟨h.scr.congr hwr, hdi.trans h.rdi,
    ⟨(hh _ (by decide)).trans h.hdr.hw, (hh _ (by decide)).trans h.hdr.hminv,
      fun j hj => (hh _ (by unfold sArr; omega)).trans (h.hdr.harr j hj)⟩,
    (hh _ (by decide)).trans h.link, (hb _ (by decide)).trans h.nw,
    fun j hj => (hb _ (by unfold sArr; omega)).trans (h.narr j hj), h.lo, h.hi⟩

theorem SubCtx.of_frm {s t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {rs : List (Nat × Nat)}
    (h : SubCtx s B Z o w wx minv) (hf : Frm (off B o) rs s.mem t.mem)
    (hr : ∀ r ∈ rs, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot wx 8) (hwr : t.wr = s.wr)
    (hdi : t.gpr .rdi = s.gpr .rdi) : SubCtx t B Z o w wx minv :=
  h.of_frmT hf (fun r hr' => ⟨(hr r hr').1, by have := (hr r hr').2; omega⟩) hwr hdi

end VG.Proof.Bignum.X86_64
