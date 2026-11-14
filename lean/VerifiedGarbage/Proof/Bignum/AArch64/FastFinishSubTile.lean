module

public import VerifiedGarbage.Proof.Bignum.AArch64.Csub
public import VerifiedGarbage.Impl.Bignum.AArch64.FastFinish
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.Row

/-! ### `Bignum.AArch64.FastFinishSubWord`, which only this module used -/

section

@[expose] public section
namespace VG.Proof.Bignum.AArch64.FastFinish
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The pointers stay at the tile's start while its four words are processed. -/
structure SubTileInv (s₀ : State) (B : Addr) (Z eA eN eT j k : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x4, .x13, .x14, .x16, .x17] s₀ t
  x16 : t.gpr .x16 = off B (eA + 8*j)
  x17 : t.gpr .x17 = off B (eN + 8*j)
  x13 : t.gpr .x13 = off B (eT + 8*j)
  out : Outside B eT (8*(j+k)) s₀.mem t.mem
  val : wv t.mem B eT (j+k) + wv s₀.mem B eN (j+k) =
    wv s₀.mem B eA (j+k) + 2 ^ (64*(j+k)) * (!t.c).toNat

theorem subWord_ok {s₀ : State} {B : Addr} {Z w eA eN eT j k : Nat}
    (hA : eA+8*w ≤ Z) (hN : eN+8*w ≤ Z) (hT : eT+8*w ≤ Z)
    (sA : eT+8*w ≤ eA ∨ eA+8*w ≤ eT) (sN : eT+8*w ≤ eN ∨ eN+8*w ≤ eT)
    (hk : k < 4) (hj : j+k < w) {t : State} (hI : SubTileInv s₀ B Z eA eN eT j k t) :
    WP isa (.block (VG.Impl.Bignum.AArch64.FastFinish.subWord k)) t fun t' =>
      SubTileInv s₀ B Z eA eN eT j (k+1) t' := by
  have hn := hI.scr.nowrap
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun u =>
    u.mem = t.mem.writeW (off B (eT+8*(j+k)))
      (word t.mem B (eA+8*(j+k)) + ~~~word t.mem B (eN+8*(j+k)) + BitVec.ofNat 64 t.c.toNat) ∧
    u.c = decide (2 ^ 64 ≤ (word t.mem B (eA+8*(j+k))).toNat +
      (~~~word t.mem B (eN+8*(j+k))).toNat + t.c.toNat)) ?_ rfl rfl rfl)
    fun u ⟨⟨hm, hc⟩, ku⟩ => ?_
  · unfold VG.Impl.Bignum.AArch64.FastFinish.subWord
    have enc : (8*k) % 8 = 0 ∧ 8*k < 32768 := by omega_using [hk]
    have eAEq : eA+8*j+8*k = eA+8*(j+k) := by omega_using []
    have eNEq : eN+8*j+8*k = eN+8*(j+k) := by omega_using []
    have eTEq : eT+8*j+8*k = eT+8*(j+k) := by omega_using []
    brun [hI.x16, hI.x17, hI.x13, enc,
      hI.scr.ld (show eA+8*j+8*k+8 ≤ Z by omega_using [hA, hj]),
      hI.scr.ld (show eN+8*j+8*k+8 ≤ Z by omega_using [hN, hj]),
      hI.scr.st (show eT+8*j+8*k+8 ≤ Z by omega_using [hT, hj])]
    all_goals simp only [eAEq, eNEq, eTEq, and_self]
  have hx : word t.mem B (eA+8*(j+k)) = word s₀.mem B (eA+8*(j+k)) :=
    hI.out.word (by omega_using [sA, hj]) (by omega_using [hA, hj, hn])
  have hy : word t.mem B (eN+8*(j+k)) = word s₀.mem B (eN+8*(j+k)) :=
    hI.out.word (by omega_using [sN, hj]) (by omega_using [hN, hj, hn])
  refine ⟨hI.scr.congr ku.wr, (hI.keep.trans ku).mono (by decide),
    (ku.gpr .x16 (by decide)).trans hI.x16, (ku.gpr .x17 (by decide)).trans hI.x17,
    (ku.gpr .x13 (by decide)).trans hI.x13, ?_, ?_⟩
  · rw [hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega_using [hT, hj, hn]) x (by omega_using [hx'])]
    exact hI.out x (by omega_using [hx'])
  · rw [show j+(k+1) = (j+k)+1 by omega_using [], hm, wv_writeW_top _ _ _ _ _ (by omega_using [hT, hj, hn]), hc]
    have hs := sbcs_toNat (word t.mem B (eA+8*(j+k))) (word t.mem B (eN+8*(j+k))) t.c
    rw [hx, hy] at hs
    have hv := hI.val
    simp only [wv]
    rw [pow64_succ, hx, hy]
    grind

end VG.Proof.Bignum.AArch64.FastFinish

end

end


@[expose] public section
namespace VG.Proof.Bignum.AArch64.FastFinish
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.AArch64.FastFinish

theorem subWords_ok {s₀ : State} {B : Addr} {Z w eA eN eT j : Nat}
    (hA : eA+8*w ≤ Z) (hN : eN+8*w ≤ Z) (hT : eT+8*w ≤ Z)
    (sA : eT+8*w ≤ eA ∨ eA+8*w ≤ eT) (sN : eT+8*w ≤ eN ∨ eN+8*w ≤ eT)
    (hj : j+4 ≤ w) {t : State} (hI : SubTileInv s₀ B Z eA eN eT j 0 t) :
    WP isa (.block sub4) t fun t' => SubTileInv s₀ B Z eA eN eT j 4 t' ∧ Keep [.x3, .x4] t t' := by
  have each (k : Nat) (hk : k ≤ 4) {u : State} (hu : SubTileInv s₀ B Z eA eN eT j 0 u) :
      WP isa (.block ((List.range k).flatMap subWord)) u fun v => SubTileInv s₀ B Z eA eN eT j k v := by
    induction k with
    | zero => exact WP.block_nil hu
    | succ k ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        WP.block_append_iff]
      exact WP.mono (ih (by omega_using [hk])) fun v hv => subWord_ok hA hN hT sA sN (by omega_using [hk]) (by omega_using [hj, hk]) hv
  exact WP.keep [.x3, .x4] (each 4 (by omega_using []) hI) rfl rfl rfl

theorem subTile_ok {s₀ : State} {B : Addr} {Z n eA eN eT j : Nat}
    (hA : eA+8*(4*n) ≤ Z) (hN : eN+8*(4*n) ≤ Z) (hT : eT+8*(4*n) ≤ Z)
    (sA : eT+8*(4*n) ≤ eA ∨ eA+8*(4*n) ≤ eT)
    (sN : eT+8*(4*n) ≤ eN ∨ eN+8*(4*n) ≤ eT)
    (hj : j < n) {t : State} (hI : SubInv s₀ B Z eA eN eT (4*j) t) :
    WP isa (.block ((sub4 ++ ([.addImm .x .x16 .x16 32,
      .addImm .x .x17 .x17 32, .addImm .x .x13 .x13 32] : List Instr)) ++
      ([.subImm .x .x14 .x14 1] : List Instr))) t fun u =>
      SubInv s₀ B Z eA eN eT (4*(j+1)) u ∧ u.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  rw [WP.block_append_iff, WP.block_append_iff]
  have hi : SubTileInv s₀ B Z eA eN eT (4*j) 0 t :=
    ⟨hI.scr, hI.keep, hI.x16, hI.x17, hI.x13, hI.out, hI.val⟩
  refine WP.mono (subWords_ok hA hN hT sA sN (by omega_using [hj]) hi) fun u ⟨hu, ku⟩ => ?_
  refine WP.mono (WP.keep [.x16, .x17, .x13] (Q := fun v =>
    v.gpr .x16 = off B (eA+8*(4*(j+1))) ∧
    v.gpr .x17 = off B (eN+8*(4*(j+1))) ∧
    v.gpr .x13 = off B (eT+8*(4*(j+1))) ∧ v.mem = u.mem ∧ v.c = u.c)
    (by
      brun [hu.x16, hu.x17, hu.x13,
        show eA+8*(4*j)+32 = eA+8*(4*(j+1)) by omega_using [],
        show eN+8*(4*j)+32 = eN+8*(4*(j+1)) by omega_using [],
        show eT+8*(4*j)+32 = eT+8*(4*(j+1)) by omega_using []]) rfl rfl rfl) fun v ⟨⟨h16, h17, h13, hm, hc⟩, kv⟩ => ?_
  refine WP.mono (dec_ok v .x14) fun z ⟨⟨h14, hzm, hzc⟩, kz⟩ => ⟨?_, ?_⟩
  · refine ⟨hu.scr.congr (kz.wr.trans kv.wr), (hu.keep.trans (kv.trans kz)).mono (by decide),
      (kz.gpr .x16 (by decide)).trans h16, (kz.gpr .x17 (by decide)).trans h17,
      (kz.gpr .x13 (by decide)).trans h13, ?_, ?_⟩
    · rw [hzm, hm, show 4*(j+1) = 4*j+4 by omega_using []]; exact hu.out
    · rw [hzm, hm, hzc, hc, show 4*(j+1) = 4*j+4 by omega_using []]; exact hu.val
  · rw [h14, kv.gpr .x14 (by decide)]
    rw [ku.gpr .x14 (by decide)]

end VG.Proof.Bignum.AArch64.FastFinish
