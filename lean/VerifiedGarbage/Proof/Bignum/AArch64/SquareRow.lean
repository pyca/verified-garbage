module

import VerifiedGarbage.Proof.Bignum.AArch64.SquarePrefix
public import VerifiedGarbage.Proof.Bignum.AArch64.Row
public import VerifiedGarbage.Impl.Bignum.AArch64.Square
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Block

/-! Four-word steps preserve the existing row invariant. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.Square
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem rowStep4_ok {s₀ : State} {B : Addr} {Z w eA eb j : Nat}
    (h7 : s₀.gpr .x7 = 0) (hA : eA + 8*w ≤ Z) (hb : eb + 8*w ≤ Z)
    (hsep : eA + 8*w ≤ eb ∨ eb + 8*w ≤ eA) (hj : j + 4 ≤ w)
    {t : State} (hI : RowInv s₀ B Z eA eb j t) :
    WP isa (.block (VG.Impl.Bignum.AArch64.Square.mac4 ++
      ([.subImm .x .x14 .x14 1] : List Instr))) t fun t' =>
        RowInv s₀ B Z eA eb (j+4) t' ∧
        t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have t7 := (hI.keep.gpr .x7 (by decide)).trans h7
  have t1 := hI.keep.gpr .x1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mac4_ok hI.scr hI.x16 hI.x17 t7 (by omega) (by omega)
    (by omega) hI.carry_lt) fun u ⟨hv, ho, hc, h16, h17, k⟩ => ?_
  refine WP.mono (dec_ok u .x14) fun t' ⟨⟨h14, hm, hcf⟩, kd⟩ => ?_
  have hcarry : carry t' = carry u := by
    unfold carry
    rw [kd.gpr .x2 (by decide), hcf]
  have hl : wv u.mem B eA j = wv t.mem B eA j :=
    ho.wv (by omega) (by omega)
  have hx : wv t.mem B (eA + 8*j) 4 = wv s₀.mem B (eA + 8*j) 4 :=
    hI.out.wv (by omega) (by omega)
  have hy : wv t.mem B (eb + 8*j) 4 = wv s₀.mem B (eb + 8*j) 4 :=
    hI.out.wv (by omega) (by omega)
  refine ⟨⟨hI.scr.congr (kd.wr.trans k.wr),
    (hI.keep.trans (k.trans kd)).mono (by decide), ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [kd.gpr .x16 (by decide), h16]
    congr 1
  · rw [kd.gpr .x17 (by decide), h17]
    congr 1
  · rw [hm]
    intro x hx'
    exact (ho x (by omega)).trans (hI.out x (by omega))
  · rw [hm, wv_add, hl, wv_add s₀.mem B eA, wv_add s₀.mem B eb]
    rw [hx, hy, t1] at hv
    rw [hcarry, Nat.mul_add, Nat.pow_add]
    have hi := hI.val
    grind
  · rw [hcarry]; exact hc
  · rw [h14, k.gpr .x14 (by decide)]

/-- Complete four-word blocks with the unchanged scalar row invariant. -/
theorem blocks4_ok {s₀ t : State} {B : Addr} {Z w eA eb q : Nat}
    (h7 : s₀.gpr .x7 = 0) (hA : eA + 8*w ≤ Z) (hb : eb + 8*w ≤ Z)
    (hsep : eA + 8*w ≤ eb ∨ eb + 8*w ≤ eA)
    (hq : 0 < q) (hq64 : q < 2 ^ 64) (hqn : 4*q ≤ w)
    (h0 : RowInv s₀ B Z eA eb 0 t) (h14 : t.gpr .x14 = BitVec.ofNat 64 q) :
    WP isa (countLoop .x14 VG.Impl.Bignum.AArch64.Square.mac4) t
      (RowInv s₀ B Z eA eb (4*q)) := by
  refine wp_countdown (N := q) hq64 hq
    (fun i => RowInv s₀ B Z eA eb (4*i)) ?_ h0 h14
  intro i hi u hI _
  simpa only [Nat.mul_succ] using (rowStep4_ok h7 hA hb hsep
    (show 4*i + 4 ≤ w by omega) hI)

/-- The scalar remainder may start after any completed four-word prefix. -/
theorem remainder_ok {s₀ t : State} {B : Addr} {Z w eA eb j r : Nat}
    (h7 : s₀.gpr .x7 = 0) (hA : eA + 8*w ≤ Z) (hb : eb + 8*w ≤ Z)
    (hsep : eA + 8*w ≤ eb ∨ eb + 8*w ≤ eA)
    (hr : 0 < r) (hr64 : r < 2 ^ 64) (hjr : j+r ≤ w)
    (h0 : RowInv s₀ B Z eA eb j t) (h14 : t.gpr .x14 = BitVec.ofNat 64 r) :
    WP isa (countLoop .x14 (mac false)) t
      (RowInv s₀ B Z eA eb (j+r)) := by
  refine wp_countdown (N := r) hr64 hr
    (fun i => RowInv s₀ B Z eA eb (j+i)) ?_ ?_ h14
  · intro i hi u hI _
    simpa only [Nat.add_assoc] using (rowStep_ok h7 hA hb hsep
      (show j+i < w by omega) hI)
  · simpa only [Nat.add_zero] using h0

/-- Counter setup preserves the numerical invariant and its carry flag. -/
theorem rowInv_counter {s₀ t u : State} {B : Addr} {Z eA eb j : Nat}
    (hI : RowInv s₀ B Z eA eb j t) (hm : u.mem = t.mem)
    (hc : carry u = carry t) (k : Keep [.x3, .x14] t u) :
    RowInv s₀ B Z eA eb j u := by
  refine ⟨hI.scr.congr k.wr, (hI.keep.trans k).mono (by decide),
    (k.gpr .x16 (by decide)).trans hI.x16,
    (k.gpr .x17 (by decide)).trans hI.x17, ?_, ?_, ?_⟩
  · rw [hm]; exact hI.out
  · rw [hm, hc]; exact hI.val
  · rw [hc]; exact hI.carry_lt

end VG.Proof.Bignum.AArch64.Square
