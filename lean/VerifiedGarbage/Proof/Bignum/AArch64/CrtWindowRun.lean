module
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowLoop
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPrefixInv

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowGroups
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTails
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFinish

/-! Complete exponentiation through shared five-bit windows and exact tails. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowFive (expRun)

theorem expRun_ok (W : Window) (M : Mont) (S : Selector) {s t : State} {P ep : Addr} {w : Nat}
    {mi : BitVec 64} {X Xc x : Nat} {Q : Prop} {bs : List Byte}
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) X)
    (hL : bs.length < 2 ^ 64)
    (hread : ∀ j < bs.length, InRegions (s.rd ++ s.wr) (ep + BitVec.ofNat 64 j) 1)
    (hbytes : ∀ j (hj : j < bs.length), s.mem (ep + BitVec.ofNat 64 j) = bs[j])
    (hout : ∀ j < bs.length, slot w 8 + CrtWindowFive.tabBytes32 w ≤ ofs P (ep + BitVec.ofNat 64 j))
    (h : PrefixInv s P w mi X Xc Q x ep bs 0 0 t) :
    WP isa (expRun W.code M.mm S.code) t fun u =>
      TableCtx u P w mi X Xc ∧ CrtWindowFive.CTab u.mem P w X Q x ∧
      wv u.mem P (slot w aY) w < X ∧
      (Q → wv u.mem P (slot w aY) w % X = x ^ Spec.Rsa.os2ip bs * 2 ^ (64 * w) % X) ∧
      Frm P (CrtWindowFive.crtExpRanges w) s.mem u.mem ∧ Keep mmRegs s u := by
  unfold expRun
  refine WP.seq (WP.mono (expGroups_ok W hw hw' hR hL hread hbytes hout h) fun a ha => ?_)
  refine WP.seq (WP.mono (expTail_ok W hw hw' hR hL (by omega) hread hbytes hout ha) fun b hb => ?_)
  refine WP.mono (finish_ok M S hb.ctx hb.tab hw hw' hR hb.pending)
    fun u ⟨cu,tu,yu,vu,fu,ku⟩ => ?_
  exact ⟨cu,tu,yu,by simpa only [pre_len] using vu,
    hb.frm.trans (fu.mono (CrtWindowFive.crtWinRanges_sub w)),(hb.keep.trans ku).mono (by decide)⟩

end VG.Proof.Bignum.AArch64.WindowFive
