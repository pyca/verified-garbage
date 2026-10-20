module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPrefixInv
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowLoop
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAppliedBatch
import VerifiedGarbage.Proof.Bignum.CrtWindowPrefix
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAdvance
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowLoopControl
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Framework.Block

/-! One five-byte group advances the public index and the exact exponent prefix. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep count_loop)
open VG.Impl.Rsa.AArch64.WindowFive (groupBody)

theorem groupBody_ok (W : Window) {s t : State} {P ep : Addr} {w i : Nat}
    {mi : BitVec 64} {X Xc x : Nat} {Q : Prop} {bs : List Byte}
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) X)
    (hL : bs.length < 2 ^ 64) (hi : i+5 ≤ bs.length)
    (hread : ∀ j < bs.length, InRegions (s.rd ++ s.wr) (ep + BitVec.ofNat 64 j) 1)
    (hbytes : ∀ j (hj : j < bs.length), s.mem (ep + BitVec.ofNat 64 j) = bs[j])
    (hout : ∀ j < bs.length, slot w 8 + CrtWindowFive.tabBytes32 w ≤ ofs P (ep + BitVec.ofNat 64 j))
    (h : PrefixInv s P w mi X Xc Q x ep bs i 0 t) :
    WP isa (groupBody W.code) t fun u =>
      PrefixInv s P w mi X Xc Q x ep bs (i+5) 0 u ∧
      u.gpr .x9 = if i+10 ≤ bs.length then 1 else 0 := by
  obtain ⟨E,v,_,hv,hK,hy,hyv,hn,bc⟩ := h.pending
  have vv : v = 0 := by simpa using hv
  have ek : E = pre bs i := by simpa [vv] using hK
  have hld : ∀ j < 5, InRegions (t.rd ++ t.wr) ((ep + BitVec.ofNat 64 i) + BitVec.ofNat 64 j) 1 := by
    intro j hj
    rw [h.keep.rd,h.keep.wr,BitVec.add_assoc,ofNat_add_ofNat]
    exact hread (i+j) (by omega)
  have hby : ∀ j (hj : j < 5), t.mem ((ep + BitVec.ofNat 64 i) + BitVec.ofNat 64 j) =
      (bs.drop i)[j]'(by simp only [List.length_drop]; omega) := by
    intro j hj
    rw [BitVec.add_assoc,ofNat_add_ofNat,List.getElem_drop]
    exact h.source hbytes hout (by omega)
  unfold groupBody
  refine WP.seq (WP.mono (appliedBatch_ok W (E := pre bs i) h.ctx h.tab hw hw' hR hy
    (by simpa only [ek] using hyv) (by simpa using bc) (by simpa [vv] using hn)
    (bs := bs.drop i) (by simp only [List.length_drop]; omega) h.exp h.idx hld hby)
    fun a ⟨ca,ta,ya,va,ba,na,fa,ka⟩ => ?_)
  have pa : Pending a P w X Q x 0 (pre bs (i+5)) := by
    refine ⟨pre bs (i+5),0,by decide,by decide,by simp,ya,?_,na,ba⟩
    simpa only [CrtWindowFive.pre_append_drop bs i 5 hi] using va
  have headers := fun {k : Nat} => win_header (k := k) fa
  rw [WP.block_append_iff]
  refine WP.mono (advance_pending 5 (by decide) ca ta pa
    ((headers (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.idx))
    fun b ⟨cb,tb,pb,ib,fb,kb,hb⟩ => ?_
  have eb := (hb _ (by decide) (by decide)).trans
    ((headers (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.exp)
  have lb := (hb _ (by decide) (by decide)).trans
    ((headers (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.len)
  refine WP.mono (haveFive_ok cb hi hL ib lb) fun u ⟨⟨hm,h9⟩,ku⟩ => ?_
  have fu : Frm P (crtWinRanges w) b.mem u.mem := hm.symm ▸ Frm.refl _ _ _
  refine ⟨⟨cb.of_win fu ku.wr (ku.gpr .x0 (by decide)),hm.symm ▸ tb,
    by simpa only [Pending,hm] using pb,hm.symm ▸ ib,hm.symm ▸ eb,hm.symm ▸ lb,?_,?_⟩,?_⟩
  · rw [hm]
    exact (h.frm.trans (fa.mono (CrtWindowFive.crtWinRanges_sub w))).trans fb
  · exact (((h.keep.trans ka).trans kb).trans ku).mono (by decide)
  · simpa only [show i+5+5 = i+10 by omega] using h9

end VG.Proof.Bignum.AArch64.WindowFive
