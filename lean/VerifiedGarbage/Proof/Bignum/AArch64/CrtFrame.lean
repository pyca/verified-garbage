import VerifiedGarbage.Proof.Bignum.AArch64.Mont
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Impl.Rsa.AArch64.Crt

/-!
# Multiword arithmetic on AArch64: a prime's workspace

`vg_rsa_private_crt` keeps three workspaces in its working space
(`Proof/Bignum/CrtFrame.lean`); `SubCtx` is a prime's, with its base in
`x0`.
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Proof.Bignum

/-- A prime's workspace at `off B o` (`wx` words), its base in `x0`, after
the modulus' at `B` (`w` words) in the working space, its header linking
back to `B`. -/
structure SubCtx (t : State) (B : Addr) (Z o w wx : Nat) (minv : BitVec 64) : Prop where
  scr : Scr t B Z
  x0 : t.gpr .x0 = off B o
  hdr : Hdr t.mem (off B o) wx minv
  link : word t.mem (off B o) (8 * sLink) = B
  nw : word t.mem B (8 * sW) = BitVec.ofNat 64 w
  narr : ∀ j < 8, word t.mem B (8 * sArr j) = off B (slot w j)
  lo : slot w 8 ≤ o
  hi : o + slot wx 8 + tabBytes wx ≤ Z

theorem SubCtx.good {t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} (h : SubCtx t B Z o w wx minv) :
    Good t (off B o) (slot wx 8) wx minv :=
  ⟨h.scr.sub (by have := h.hi; omega) (by unfold slot hdrBytes; omega), h.x0, h.hdr⟩

/-- The prime's workspace with its table. -/
theorem SubCtx.scrT {t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} (h : SubCtx t B Z o w wx minv) :
    Scr t (off B o) (slot wx 8 + tabBytes wx) :=
  h.scr.sub (by have := h.hi; omega) (by unfold slot hdrBytes; omega)

/-- What changes within the arrays and the functions' own slots of the
prime's workspace (but its link) keeps it. -/
theorem SubCtx.of_frmT {s t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {rs : List (Nat × Nat)}
    (h : SubCtx s B Z o w wx minv) (hf : Frm (off B o) rs s.mem t.mem)
    (hr : ∀ r ∈ rs, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot wx 8 + tabBytes wx) (hwr : t.wr = s.wr)
    (h0 : t.gpr .x0 = s.gpr .x0) : SubCtx t B Z o w wx minv := by
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
  exact ⟨h.scr.congr hwr, h0.trans h.x0,
    ⟨(hh _ (by decide)).trans h.hdr.hw, (hh _ (by decide)).trans h.hdr.hminv,
      fun j hj => (hh _ (by unfold sArr; omega)).trans (h.hdr.harr j hj)⟩,
    (hh _ (by decide)).trans h.link, (hb _ (by decide)).trans h.nw,
    fun j hj => (hb _ (by unfold sArr; omega)).trans (h.narr j hj), h.lo, h.hi⟩

theorem SubCtx.of_frm {s t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {rs : List (Nat × Nat)}
    (h : SubCtx s B Z o w wx minv) (hf : Frm (off B o) rs s.mem t.mem)
    (hr : ∀ r ∈ rs, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot wx 8) (hwr : t.wr = s.wr)
    (h0 : t.gpr .x0 = s.gpr .x0) : SubCtx t B Z o w wx minv :=
  h.of_frmT hf (fun r hr' => ⟨(hr r hr').1, by have := (hr r hr').2; omega⟩) hwr h0


/-! ## The prime's header, at offsets of `B`

Code in a prime's workspace addresses it from `x0 = off B o`, which `brun`
writes `off B (o + d)`. -/

namespace SubCtx
variable {t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} (hc : SubCtx t B Z o w wx minv)
include hc

theorem ld' {i : Nat} (hi : i < 32) : InRegions (t.rd ++ t.wr) (off B (o + 8 * i)) 8 :=
  hc.scr.ld (by have := hdr_lt_slot wx 8 hi; have := hc.hi; omega)

theorem st' {i : Nat} (hi : i < 32) : InRegions t.wr (off B (o + 8 * i)) 8 :=
  hc.scr.st (by have := hdr_lt_slot wx 8 hi; have := hc.hi; omega)

theorem ldn {i : Nat} (hi : i < 32) : InRegions (t.rd ++ t.wr) (off B (8 * i)) 8 :=
  hc.scr.ld (by have := hdr_lt_slot w 8 hi; have := hc.lo; have := hc.hi; omega)

theorem stn {i : Nat} (hi : i < 32) : InRegions t.wr (off B (8 * i)) 8 :=
  hc.scr.st (by have := hdr_lt_slot w 8 hi; have := hc.lo; have := hc.hi; omega)

theorem link' : word t.mem B (o + 8 * sLink) = B := by rw [← word_off]; exact hc.link

theorem hw' : word t.mem B (o + 8 * sW) = BitVec.ofNat 64 wx := by rw [← word_off]; exact hc.hdr.hw

theorem harr' {j : Nat} (hj : j < 8) : word t.mem B (o + 8 * sArr j) = off B (o + slot wx j) := by
  rw [← word_off, hc.hdr.harr j hj, off_off]

end SubCtx

end VG.Proof.Bignum.AArch64
