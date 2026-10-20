module
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowLoop
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPrefixInv

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowLoadTail
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTailByte
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowAdvance
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowLoopControl
import VerifiedGarbage.Proof.Framework.Block

/-! Trailing bytes extend the exact exponent prefix, carrying partial windows. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep count_loop)
open VG.Impl.Rsa.AArch64.WindowFive (tailBody)

theorem tailBody_ok (W : Window) {s t : State} {P ep : Addr} {w i b : Nat}
    {mi : BitVec 64} {X Xc x : Nat} {Q : Prop} {bs : List Byte}
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) X)
    (hi : i < bs.length)
    (hread : ∀ j < bs.length, InRegions (s.rd ++ s.wr) (ep + BitVec.ofNat 64 j) 1)
    (hbytes : ∀ j (hj : j < bs.length), s.mem (ep + BitVec.ofNat 64 j) = bs[j])
    (hout : ∀ j < bs.length, slot w 8 + CrtWindowFive.tabBytes32 w ≤ ofs P (ep + BitVec.ofNat 64 j))
    (h : PrefixInv s P w mi X Xc Q x ep bs i b t) :
    WP isa (tailBody W.code) t fun u =>
      PrefixInv s P w mi X Xc Q x ep bs (i+1) ((b+8)%5) u ∧
      u.gpr .x3 = BitVec.ofNat 64 (bs.length-(i+1)) := by
  unfold tailBody
  refine WP.seq (WP.mono (loadTailByte_ok h.ctx h.tab h.pending h.idx h.exp
    (by rw [h.keep.rd,h.keep.wr]; exact hread i hi) (h.source hbytes hout hi))
    fun a ⟨ca,ta,pa,va,fa,ka,ha⟩ => ?_)
  refine WP.seq (WP.mono (tailByte_ok W ca ta hw hw' hR pa (bs[i].isLt) va)
    fun c ⟨cc,tc,pc,fc,kc,_⟩ => ?_)
  have pc' : Pending c P w X Q x ((b+8)%5) (pre bs (i+1)) := by
    have he : pre bs i * 256 + bs[i].toNat = pre bs (i+1) := by
      rw [pre_succ bs hi,Nat.mul_comm (pre bs i) 256]
    simpa only [he] using pc
  have headers := fun {k : Nat} => win_header (k := k) fc
  have ic := (headers (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    ((ha _ (by decide) (by decide)).trans h.idx)
  have ec := (headers (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    ((ha _ (by decide) (by decide)).trans h.exp)
  have lc := (headers (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    ((ha _ (by decide) (by decide)).trans h.len)
  rw [WP.block_append_iff]
  refine WP.mono (advance_pending 1 (by decide) cc tc pc' ic)
    fun d ⟨cd,td,pd,id,fd,kd,hd⟩ => ?_
  have ed := (hd _ (by decide) (by decide)).trans ec
  have ld := (hd _ (by decide) (by decide)).trans lc
  refine WP.mono (remaining_ok cd (by omega) id ld) fun u ⟨⟨hm,h3⟩,ku⟩ => ?_
  have fu : Frm P (crtWinRanges w) d.mem u.mem := hm.symm ▸ Frm.refl _ _ _
  refine ⟨⟨cd.of_win fu ku.wr (ku.gpr .x0 (by decide)),hm.symm ▸ td,
    by simpa only [Pending,hm] using pd,hm.symm ▸ id,hm.symm ▸ ed,hm.symm ▸ ld,?_,?_⟩,h3⟩
  · rw [hm]
    exact (h.frm.trans ((fa.trans fc).mono (CrtWindowFive.crtWinRanges_sub w))).trans fd
  · exact ((((h.keep.trans ka).trans kc).trans kd).trans ku).mono (by decide)

end VG.Proof.Bignum.AArch64.WindowFive
