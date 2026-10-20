module

public import VerifiedGarbage.Proof.Dsa.AArch64.ChildBases
public import VerifiedGarbage.Proof.Dsa.AArch64.ChildCount
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtFrame
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract

/-! # Creating a linked arithmetic child from its public operand length -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem newChild_ok {s : State} {B : Addr} {Z o w len : Nat} {parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (hZ : pWorkspace ≤ Z)
    (ho : o < 2 ^ 16) (hlen : len < 2 ^ 32)
    (hl : word s.mem B (8 * argLen) = BitVec.ofNat 64 len)
    (hlo : slot w 8 ≤ o) (hhi : o + slot ((len + 7) / 8) 8 + tabBytes ((len + 7) / 8) ≤ Z) :
    WP isa (.block (childCount o ++ childBases)) s fun t => ∃ mi : BitVec 64,
      SubCtx t B Z o w ((len + 7) / 8) mi ∧
      Outside (off B o) 48 88 s.mem t.mem ∧ Keep [.x1, .x0, .x12, .x3, .x4] s t := by
  have hslot : 256 ≤ slot ((len + 7) / 8) 8 := by unfold slot hdrBytes; omega
  have hroot : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega
  rw [WP.block_append_iff]
  refine WP.mono (childCount_ok hg.scr hg.x0 hZ ho hlen hl)
    fun u ⟨husi, hudi, hu12, hum, hku⟩ => ?_
  have hus : Scr u (off B o) (slot ((len + 7) / 8) 8) :=
    (hg.scr.congr hku.wr).sub (by omega) (by omega)
  refine WP.mono (childBases_ok hus hudi husi hu12 (by omega)) fun t ⟨hgt, hlink, hft, hkt⟩ => ?_
  have hf : Outside (off B o) 48 88 s.mem t.mem := by rw [← hum]; exact hft
  have hff : Frm (off B o) [(48, 88)] s.mem t.mem := Frm.of_outside hf (by simp)
  have hb : ∀ i < 32, word t.mem B (8 * i) = word s.mem B (8 * i) := by
    intro i hi
    exact hff.word_below (L := 136) (by intro r hr; rw [List.mem_singleton.mp hr]; decide)
      (by have := hg.scr.nowrap; omega) (by omega) (by omega)
  have hk := hku.trans hkt
  exact ⟨_, ⟨hg.scr.congr hk.wr, hgt.x0, hgt.hdr, hlink,
    (hb _ (by decide)).trans hg.hdr.hw,
    fun j hj => (hb _ (by unfold sArr; omega)).trans (hg.hdr.harr j hj), hlo, hhi⟩,
    hf, hk.mono (by decide)⟩

end VG.Proof.Dsa.AArch64
