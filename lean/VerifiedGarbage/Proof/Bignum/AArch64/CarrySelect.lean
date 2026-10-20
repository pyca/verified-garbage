module

import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
public import VerifiedGarbage.Impl.Rsa.AArch64.CarrySelect
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Carry-based multiword selection with the same memory and register frame. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Crt VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- `selLoop`: `[x17] := mask ? [x16] : [x17]` over `w` words. -/
theorem carrySelect_ok {s : State} {B : Addr} {Z w eA eo : Nat} (hs : Scr s B Z)
    (h16 : s.gpr .x16 = off B eA) (h17 : s.gpr .x17 = off B eo) (h14 : s.gpr .x14 = BitVec.ofNat 64 w)
    {lt : Bool} (h15 : s.gpr .x15 = mask lt)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hA : eA + 8 * w ≤ Z) (ho : eo + 8 * w ≤ Z)
    (sA : eo + 8 * w ≤ eA ∨ eA + 8 * w ≤ eo) :
    WP isa VG.Impl.Rsa.AArch64.CarrySelect.code s fun t =>
      wv t.mem B eo w = (if lt then wv s.mem B eA w else wv s.mem B eo w) ∧
      Outside B eo (8 * w) s.mem t.mem ∧ Keep [.x3, .x4, .x14, .x16, .x17] s t := by
  have hn := hs.nowrap
  unfold VG.Impl.Rsa.AArch64.CarrySelect.code
  refine WP.seq (WP.mono (WP.keep [.x3] (Q := fun u => u.mem = s.mem ∧ u.c = lt)
    (by cases lt <;> brun [h15, mask]) rfl rfl rfl) fun u ⟨⟨hm, hc⟩, ku⟩ => ?_)
  refine WP.mono (wp_countdown (N := w) (by omega) (by omega)
    (fun j t => SelLInv s B Z eA eo lt j t ∧ t.c = lt) ?_
    ⟨⟨hs.congr ku.wr, ku.mono (by decide), by rw [ku.gpr .x16 (by decide), h16]; rfl,
      by rw [ku.gpr .x17 (by decide), h17]; rfl,
      by rw [hm]; exact Outside.refl _ _ _ _, by cases lt <;> rfl⟩, hc⟩
    ((ku.gpr .x14 (by decide)).trans h14))
    fun t ⟨hI, _⟩ => ⟨hI.val, hI.out, hI.keep⟩
  intro j hj t ⟨hI, hc⟩ _
  have hx : word t.mem B (eA + 8 * j) = word s.mem B (eA + 8 * j) := hI.out.word (by omega) (by omega)
  have hy : word t.mem B (eo + 8 * j) = word s.mem B (eo + 8 * j) := hI.out.word (by omega) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4, .x16, .x17] (Q := fun t₁ => t₁.mem = t.mem.writeW (off B (eo + 8 * j))
      (if lt then word t.mem B (eA + 8 * j) else word t.mem B (eo + 8 * j)) ∧
      t₁.gpr .x16 = off B (eA + 8 * j + 8) ∧ t₁.gpr .x17 = off B (eo + 8 * j + 8) ∧ t₁.c = lt) (by
      brun [hI.x16, hI.x17, hc, hI.scr.ld (show eA + 8 * j + 8 ≤ Z by omega),
        hI.scr.ld (show eo + 8 * j + 8 ≤ Z by omega), hI.scr.st (show eo + 8 * j + 8 ≤ Z by omega)])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨hm, h16', h17', hc₁⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14', hm', hc'⟩, k'⟩ => ⟨⟨?_, hc'.trans hc₁⟩, by rw [h14', k₁.gpr .x14 (by decide)]⟩
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16', Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x17 (by decide), h17', Nat.mul_succ, Nat.add_assoc], ?_, ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega), hI.val, hx, hy]
    cases lt <;> simp [wv]

end VG.Proof.Bignum.AArch64
