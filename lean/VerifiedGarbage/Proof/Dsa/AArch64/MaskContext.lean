module

import VerifiedGarbage.Proof.Dsa.AArch64.Masks
public import VerifiedGarbage.Proof.Dsa.AArch64.Return
public import VerifiedGarbage.Impl.Dsa.AArch64.Checks

/-! # Acceptance-mask writes preserve reusable arithmetic state -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem maskWrite_good {s t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hf : Outside B Field.mask.offset 8 s.mem t.mem)
    (hk : Keep [.x3, .x4] s t) : Good t B Z w minv := by
  have he : ∀ i < 32, word t.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    hf.word (Or.inl (by change 8 * i + 8 ≤ 360; omega)) (by omega)
  exact ⟨hg.scr.congr hk.wr, (hk.gpr .x0 (by decide)).trans hg.x0,
    ⟨(he _ (by decide)).trans hg.hdr.hw, (he _ (by decide)).trans hg.hdr.hminv,
      fun j hj => (he _ (by unfold sArr; omega)).trans (hg.hdr.harr j hj)⟩⟩

theorem maskWrite_child {mem mem' : Mem} {B : Addr} {o wx m : Nat} {minv : BitVec 64}
    (child : ChildReady mem B o wx m minv) (hf : Outside B Field.mask.offset 8 mem mem')
    (ho : 368 ≤ o) (hbound : o + slot wx 8 ≤ 2 ^ 64) : ChildReady mem' B o wx m minv := by
  have hslot : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have he : ∀ d, o + d + 8 ≤ 2 ^ 64 → word mem' (off B o) d = word mem (off B o) d := by
    intro d hd
    rw [word_off, word_off]
    exact hf.word (Or.inr (by change 368 ≤ o + d; omega)) hd
  have hN := slot_le (w := wx) (show aN < 8 by decide)
  refine ⟨child.header.of_words (fun i hi => he _ (by omega)), ?_, ?_⟩
  · rw [wv_congr (m := mem) (m' := mem') (fun i hi => he _ (by omega))]
    exact child.modulus
  · rw [he _ (by omega)]
    exact child.inverse

/-- The mask store leaves the parent and selected child ready for another call. -/
theorem accumulate_context {s : State} {B : Addr} {Z o w wx m : Nat} {minv parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B o wx m minv)
    (hZ : pWorkspace ≤ Z) (ho : 368 ≤ o) (hhi : o + slot wx 8 ≤ Z) {a b : Bool}
    (ha : s.gpr .x3 = mask a) (hb : word s.mem B Field.mask.offset = mask b) :
    WP isa (.block Checks.accumulate) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B o wx m minv ∧
      word t.mem B Field.mask.offset = mask (a && b) ∧
      Outside B Field.mask.offset 8 s.mem t.mem ∧ Keep [.x3, .x4] s t := by
  have hn := hg.scr.nowrap
  exact WP.mono (accumulate_ok hg.scr hg.x0 hZ ha hb) fun t ⟨ht, hf, hk⟩ =>
    ⟨maskWrite_good hg hf hk, maskWrite_child child hf ho (by omega), ht, hf, hk⟩

end VG.Proof.Dsa.AArch64
