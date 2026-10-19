module
public import Mathlib.Data.Int.GCD
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtFrame
public import VerifiedGarbage.Proof.Bignum.CrtWindowFiveLayout
public import VerifiedGarbage.Proof.Framework.Contract

import Mathlib.Data.Int.ModEq

/-! The wider table leaves the modulus and prime workspace headers unchanged. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Proof.Bignum

theorem subCtx_of_wide {s t : State} {B : Addr} {Z o w wx : Nat} {minv : BitVec 64} {rs : List (Nat × Nat)}
    (h : SubCtx s B Z o w wx minv)
    (hwide : o + slot wx 8 + CrtWindowFive.tabBytes32 wx ≤ Z) (hf : Frm (off B o) rs s.mem t.mem)
    (hr : ∀ r ∈ rs, 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot wx 8 + CrtWindowFive.tabBytes32 wx) (hwr : t.wr = s.wr)
    (h0 : t.gpr .x0 = s.gpr .x0) : SubCtx t B Z o w wx minv := by
  have hn := h.scr.nowrap
  have hi := hwide
  have hL : o + (slot wx 8 + CrtWindowFive.tabBytes32 wx) ≤ 2 ^ 64 := by omega
  have hr' : ∀ r ∈ rs, r.1 + r.2 ≤ slot wx 8 + CrtWindowFive.tabBytes32 wx := fun r hr' => (hr r hr').2
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

end VG.Proof.Bignum.AArch64.WindowFive
