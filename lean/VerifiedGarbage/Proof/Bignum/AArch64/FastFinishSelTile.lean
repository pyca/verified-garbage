module

public import VerifiedGarbage.Proof.Bignum.AArch64.FastFinishSelWord
public import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section
namespace VG.Proof.Bignum.AArch64.FastFinish
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.AArch64.FastFinish

theorem selWords_ok {s₀ : State} {B : Addr} {Z w eA eT eo j : Nat} {lt : Bool}
    (hA : eA+8*w ≤ Z) (hT : eT+8*w ≤ Z) (ho : eo+8*w ≤ Z)
    (sA : eo+8*w ≤ eA ∨ eA+8*w ≤ eo) (sT : eo+8*w ≤ eT ∨ eT+8*w ≤ eo)
    (hj : j+4 ≤ w) {t : State} (hI : SelTileInv s₀ B Z eA eT eo lt j 0 t) :
    WP isa (.block sel4) t fun t' => SelTileInv s₀ B Z eA eT eo lt j 4 t' ∧ Keep [.x3, .x4] t t' := by
  have each (k : Nat) (hk : k ≤ 4) {u : State} (hu : SelTileInv s₀ B Z eA eT eo lt j 0 u) :
      WP isa (.block ((List.range k).flatMap selWord)) u fun v => SelTileInv s₀ B Z eA eT eo lt j k v := by
    induction k with
    | zero => exact WP.block_nil hu
    | succ k ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        WP.block_append_iff]
      exact WP.mono (ih (by omega)) fun v hv => selWord_ok hA hT ho sA sT (by omega) (by omega) hv
  exact WP.keep [.x3, .x4] (each 4 (by omega) hI) rfl rfl rfl

theorem selTile_ok {s₀ : State} {B : Addr} {Z n eA eT eo j : Nat} {lt : Bool}
    (hA : eA+8*(4*n) ≤ Z) (hT : eT+8*(4*n) ≤ Z) (ho : eo+8*(4*n) ≤ Z)
    (sA : eo+8*(4*n) ≤ eA ∨ eA+8*(4*n) ≤ eo)
    (sT : eo+8*(4*n) ≤ eT ∨ eT+8*(4*n) ≤ eo)
    (hj : j < n) {t : State} (hI : SelInv s₀ B Z eA eT eo lt (4*j) t) :
    WP isa (.block ((sel4 ++ ([.addImm .x .x16 .x16 32,
      .addImm .x .x6 .x6 32, .addImm .x .x5 .x5 32] : List Instr)) ++
      ([.subImm .x .x14 .x14 1] : List Instr))) t fun u =>
      SelInv s₀ B Z eA eT eo lt (4*(j+1)) u ∧ u.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  rw [WP.block_append_iff, WP.block_append_iff]
  have hi : SelTileInv s₀ B Z eA eT eo lt (4*j) 0 t :=
    ⟨hI.scr, hI.keep, hI.x16, hI.x6, hI.x5, hI.c, hI.out, hI.val⟩
  refine WP.mono (selWords_ok hA hT ho sA sT (by omega) hi) fun u ⟨hu, ku⟩ => ?_
  refine WP.mono (WP.keep [.x16, .x6, .x5] (Q := fun v =>
    v.gpr .x16 = off B (eA+8*(4*(j+1))) ∧
    v.gpr .x6 = off B (eT+8*(4*(j+1))) ∧
    v.gpr .x5 = off B (eo+8*(4*(j+1))) ∧ v.mem = u.mem ∧ v.c = u.c)
    (by
      brun [hu.x16, hu.x6, hu.x5,
        show eA+8*(4*j)+32 = eA+8*(4*(j+1)) by omega,
        show eT+8*(4*j)+32 = eT+8*(4*(j+1)) by omega,
        show eo+8*(4*j)+32 = eo+8*(4*(j+1)) by omega]) rfl rfl rfl) fun v ⟨⟨h16, h6, h5, hm, hc⟩, kv⟩ => ?_
  refine WP.mono (dec_ok v .x14) fun z ⟨⟨h14, hzm, hzc⟩, kz⟩ => ⟨?_, ?_⟩
  · refine ⟨hu.scr.congr (kz.wr.trans kv.wr), (hu.keep.trans (kv.trans kz)).mono (by decide),
      (kz.gpr .x16 (by decide)).trans h16, (kz.gpr .x6 (by decide)).trans h6,
      (kz.gpr .x5 (by decide)).trans h5, hzc.trans (hc.trans hu.c), ?_, ?_⟩
    · rw [hzm, hm, show 4*(j+1) = 4*j+4 by omega]; exact hu.out
    · rw [hzm, hm, show 4*(j+1) = 4*j+4 by omega]; exact hu.val
  · rw [h14, kv.gpr .x14 (by decide)]
    rw [ku.gpr .x14 (by decide)]

end VG.Proof.Bignum.AArch64.FastFinish
