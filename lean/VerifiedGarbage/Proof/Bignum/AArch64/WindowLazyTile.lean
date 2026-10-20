module

public import VerifiedGarbage.Proof.Bignum.AArch64.WindowLazyWord
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowLazy
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.AArch64.WindowLazy

structure Inv (s₀ : State) (B : Addr) (Z eA eN eT j : Nat) (bit : Bool) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x4, .x5, .x14, .x16, .x17] s₀ t
  x16 : t.gpr .x16 = off B (eA + 8*j)
  x17 : t.gpr .x17 = off B (eN + 8*j)
  x5 : t.gpr .x5 = off B (eT + 8*j)
  mask : t.gpr .x15 = if bit then -1 else 0
  out : Outside B eT (8*j) s₀.mem t.mem
  val : wv t.mem B eT j + bit.toNat * wv s₀.mem B eN j =
    wv s₀.mem B eA j + 2 ^ (64*j) * (!t.c).toNat

theorem words_ok {s₀ : State} {B : Addr} {Z w eA eN eT j : Nat}
    (hA : eA+8*w ≤ Z) (hN : eN+8*w ≤ Z) (hT : eT+8*w ≤ Z)
    (sA : eT+8*w ≤ eA ∨ eA+8*w ≤ eT) (sN : eT+8*w ≤ eN ∨ eN+8*w ≤ eT)
    (hj : j+4 ≤ w) {bit : Bool} {t : State} (hI : TileInv s₀ B Z eA eN eT j 0 bit t) :
    WP isa (.block words) t fun t' => TileInv s₀ B Z eA eN eT j 4 bit t' ∧ Keep [.x3, .x4] t t' := by
  have each (k : Nat) (hk : k ≤ 4) {u : State} (hu : TileInv s₀ B Z eA eN eT j 0 bit u) :
      WP isa (.block ((List.range k).flatMap WindowLazy.word)) u fun v => TileInv s₀ B Z eA eN eT j k bit v := by
    induction k with
    | zero => exact WP.block_nil hu
    | succ k ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        WP.block_append_iff]
      exact WP.mono (ih (by omega)) fun v hv => word_ok hA hN hT sA sN (by omega) (by omega) hv
  exact WP.keep [.x3, .x4] (each 4 (by omega) hI) rfl rfl rfl

theorem tile_ok {s₀ : State} {B : Addr} {Z n eA eN eT j : Nat}
    (hA : eA+8*(4*n) ≤ Z) (hN : eN+8*(4*n) ≤ Z) (hT : eT+8*(4*n) ≤ Z)
    (sA : eT+8*(4*n) ≤ eA ∨ eA+8*(4*n) ≤ eT)
    (sN : eT+8*(4*n) ≤ eN ∨ eN+8*(4*n) ≤ eT)
    (hj : j < n) {bit : Bool} {t : State} (hI : Inv s₀ B Z eA eN eT (4*j) bit t) :
    WP isa (.block ((words ++ ([.addImm .x .x16 .x16 32,
      .addImm .x .x17 .x17 32, .addImm .x .x5 .x5 32] : List Instr)) ++
      ([.subImm .x .x14 .x14 1] : List Instr))) t fun u =>
      Inv s₀ B Z eA eN eT (4*(j+1)) bit u ∧ u.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  rw [WP.block_append_iff, WP.block_append_iff]
  have hi : TileInv s₀ B Z eA eN eT (4*j) 0 bit t :=
    ⟨hI.scr, hI.keep, hI.x16, hI.x17, hI.x5, hI.mask, hI.out, hI.val⟩
  refine WP.mono (words_ok hA hN hT sA sN (by omega) hi) fun u ⟨hu, ku⟩ => ?_
  refine WP.mono (WP.keep [.x16, .x17, .x5] (Q := fun v =>
    v.gpr .x16 = off B (eA+8*(4*(j+1))) ∧
    v.gpr .x17 = off B (eN+8*(4*(j+1))) ∧
    v.gpr .x5 = off B (eT+8*(4*(j+1))) ∧ v.mem = u.mem ∧ v.c = u.c)
    (by
      brun [hu.x16, hu.x17, hu.x5,
        show eA+8*(4*j)+32 = eA+8*(4*(j+1)) by omega,
        show eN+8*(4*j)+32 = eN+8*(4*(j+1)) by omega,
        show eT+8*(4*j)+32 = eT+8*(4*(j+1)) by omega]) rfl rfl rfl) fun v ⟨⟨h16, h17, h13, hm, hc⟩, kv⟩ => ?_
  refine WP.mono (dec_ok v .x14) fun z ⟨⟨h14, hzm, hzc⟩, kz⟩ => ⟨?_, ?_⟩
  · refine ⟨hu.scr.congr (kz.wr.trans kv.wr), (hu.keep.trans (kv.trans kz)).mono (by decide),
      (kz.gpr .x16 (by decide)).trans h16, (kz.gpr .x17 (by decide)).trans h17,
      (kz.gpr .x5 (by decide)).trans h13,
      ((kv.trans kz).gpr .x15 (by decide)).trans hu.mask, ?_, ?_⟩
    · rw [hzm, hm, show 4*(j+1) = 4*j+4 by omega]; exact hu.out
    · rw [hzm, hm, hzc, hc, show 4*(j+1) = 4*j+4 by omega]; exact hu.val
  · rw [h14, kv.gpr .x14 (by decide)]
    rw [ku.gpr .x14 (by decide)]

end VG.Proof.Bignum.AArch64.WindowLazy
