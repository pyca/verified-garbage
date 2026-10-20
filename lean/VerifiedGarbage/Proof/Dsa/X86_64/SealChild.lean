module

public import VerifiedGarbage.Proof.Dsa.X86_64.InitInverse
public import VerifiedGarbage.Proof.Dsa.X86_64.Return
import VerifiedGarbage.Proof.Dsa.X86_64.EnterLeave
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core

/-! # Finishing a child modulus and returning a reusable workspace -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem sealChild_ok {s : State} {B : Addr} {Z o w wx m : Nat} {oldMinv parentMinv : BitVec 64}
    (hc : SubCtx s B Z o w wx oldMinv)
    (hn : wv s.mem (off B o) (slot wx aN) wx = m) (hw : 1 ≤ wx) (hodd : m % 2 = 1)
    (hpm : word s.mem B (8 * sMinv) = parentMinv) :
    WP isa (.block (initInverse ++ [Crt.leave])) s fun t => ∃ mi : BitVec 64,
      Good t B Z w parentMinv ∧ ChildReady t.mem B o wx m mi ∧
      Outside (off B o) (8 * sMinv) 8 s.mem t.mem ∧ Keep coreRegs s t := by
  have hi := hc.hi
  have hlo := hc.lo
  have hroot : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega
  have hslot : 256 ≤ slot wx aN := by unfold slot hdrBytes; omega
  have hN := slot_le (w := wx) (show aN < 8 by decide)
  have hodd' : (word s.mem (off B o) (slot wx aN)).toNat % 2 = 1 := by
    rw [← wv_mod64 _ _ _ hw, hn, Nat.mod_mod_of_dvd _ (by decide)]
    exact hodd
  rw [WP.block_append_iff]
  refine WP.mono (initInverse_ok hc.good (Nat.le_refl _) hodd')
    fun u ⟨mi, hgu, hinv, hfu, hku⟩ => ?_
  have hff : Frm (off B o) [(8 * sMinv, 8)] s.mem u.mem := Frm.of_outside hfu (by simp)
  have hb : ∀ i < 32, word u.mem B (8 * i) = word s.mem B (8 * i) := by
    intro i hi'
    exact hff.word_below (L := 64) (by intro r hr; rw [List.mem_singleton.mp hr]; decide)
      (by have := hc.scr.nowrap; omega) (by have := hc.scr.nowrap; omega) (by omega)
  have hcu : SubCtx u B Z o w wx mi :=
    ⟨hc.scr.congr hku.2.2, hgu.rdi, hgu.hdr,
      (hfu.word (Or.inr (by decide)) (by decide)).trans hc.link,
      (hb _ (by decide)).trans hc.nw,
      fun j hj => (hb _ (by unfold sArr; omega)).trans (hc.narr j hj), hlo, hi⟩
  have hun : wv u.mem (off B o) (slot wx aN) wx = m := by
    rw [hfu.wv (Or.inr (by change 64 ≤ slot wx aN; omega)) (by have := hc.good.scr.nowrap; omega)]
    exact hn
  have hui : ((word u.mem (off B o) (slot wx aN)).toNat * mi.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hfu.word (Or.inr (by change 64 ≤ slot wx aN; omega)) (by have := hc.good.scr.nowrap; omega)]
    exact hinv
  refine WP.mono (leave_ok hcu ((hb _ (by decide)).trans hpm)) fun t ⟨hgt, htm, hkt⟩ => ?_
  exact ⟨mi, hgt, ⟨by rw [htm]; exact ⟨hcu.hdr, hcu.link⟩,
    by rw [htm]; exact hun, by rw [htm]; exact hui⟩,
    by rw [htm]; exact hfu, (hku.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64
