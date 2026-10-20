module
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowLoop
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPrefixInv

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTailLoop
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowLoopControl
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBuild

/-! Consume the remaining bytes, preserving the pending count across byte boundaries. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep count_loop)
open VG.Impl.Rsa.AArch64.WindowFive (expTail)

theorem expTail_ok (W : Window) {s t : State} {P ep : Addr} {w i : Nat}
    {mi : BitVec 64} {X Xc x : Nat} {Q : Prop} {bs : List Byte}
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) X)
    (hL : bs.length < 2 ^ 64) (hi : i ≤ bs.length)
    (hread : ∀ j < bs.length, InRegions (s.rd ++ s.wr) (ep + BitVec.ofNat 64 j) 1)
    (hbytes : ∀ j (hj : j < bs.length), s.mem (ep + BitVec.ofNat 64 j) = bs[j])
    (hout : ∀ j < bs.length, slot w 8 + CrtWindowFive.tabBytes32 w ≤ ofs P (ep + BitVec.ofNat 64 j))
    (h : PrefixInv s P w mi X Xc Q x ep bs i 0 t) :
    WP isa (expTail W.code) t
      (PrefixInv s P w mi X Xc Q x ep bs bs.length ((8*(bs.length-i))%5)) := by
  unfold expTail
  refine WP.seq (WP.mono (remaining_ok h.ctx hi h.idx h.len)
    fun a ⟨⟨hm,h3⟩,ka⟩ => ?_)
  have ha := h.keepMem hm ka (by decide) (by decide)
  by_cases hz : i = bs.length
  · refine WP.ite false ?_ (by simp) (fun _ => ?_)
    · change some (!(a.gpr .x3 == 0)) = some false
      rw [h3,hz,Nat.sub_self]; rfl
    · apply WP.block_nil
      simpa only [hz,Nat.sub_self,Nat.mul_zero,Nat.zero_mod] using ha
  · refine WP.ite true ?_ (fun _ => ?_) (by simp)
    · change some (!(a.gpr .x3 == 0)) = some true
      rw [h3]
      have nz : BitVec.ofNat 64 (bs.length-i) ≠ 0 := by
        intro he
        have he' := congrArg BitVec.toNat he
        simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show bs.length-i < 2 ^ 64 by omega)] at he'
        change bs.length-i = 0 at he'
        omega
      rw [beq_eq_false_iff_ne.mpr nz]; rfl
    · refine WP.mono (count_loop (cr := .x3) (n := bs.length-i) (by omega)
        (fun j => PrefixInv s P w mi X Xc Q x ep bs (i+j) ((8*j)%5)) ?_ ?_) fun u hu => ?_
      · intro j hj u hu
        refine WP.mono (tailBody_ok W hw hw' hR (by omega) hread hbytes hout hu)
          fun v ⟨hv,h3v⟩ => ⟨?_,?_⟩
        · have hb : ((8*j)%5+8)%5 = (8*(j+1))%5 := by omega
          simpa only [hb,Nat.add_assoc] using hv
        · rw [h3v,cnt_ne (by omega)]
          omega
      · simpa only [Nat.add_zero,Nat.mul_zero,Nat.zero_mod] using ha
      · simpa only [Nat.add_sub_of_le hi] using hu

end VG.Proof.Bignum.AArch64.WindowFive
