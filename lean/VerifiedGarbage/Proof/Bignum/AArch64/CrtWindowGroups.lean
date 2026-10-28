module
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowLoop
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPrefixInv

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowGroupLoop
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowLoopControl

/-! Consume all complete five-byte groups; the count depends only on length. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep count_loop)
open VG.Impl.Rsa.AArch64.WindowFive (expGroups)

theorem expGroups_ok (W : Window) {s t : State} {P ep : Addr} {w : Nat}
    {mi : BitVec 64} {X Xc x : Nat} {Q : Prop} {bs : List Byte}
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hR : Nat.Coprime (2 ^ (64 * w)) X)
    (hL : bs.length < 2 ^ 64)
    (hread : ∀ j < bs.length, InRegions (s.rd ++ s.wr) (ep + BitVec.ofNat 64 j) 1)
    (hbytes : ∀ j (hj : j < bs.length), s.mem (ep + BitVec.ofNat 64 j) = bs[j])
    (hout : ∀ j < bs.length, slot w 8 + CrtWindowFive.tabBytes32 w ≤ ofs P (ep + BitVec.ofNat 64 j))
    (h : PrefixInv s P w mi X Xc Q x ep bs 0 0 t) :
    WP isa (expGroups W.code) t (PrefixInv s P w mi X Xc Q x ep bs (5*(bs.length/5)) 0) := by
  unfold expGroups
  refine WP.seq (WP.mono (haveFive_ok h.ctx (by omega) hL h.idx h.len)
    fun a ⟨⟨hm,h9⟩,ka⟩ => ?_)
  have ha := h.keepMem hm ka (by decide) (by decide)
  by_cases hz : bs.length / 5 = 0
  · refine WP.ite false ?_ (by simp) (fun _ => ?_)
    · change some (!(a.gpr .x9 == 0)) = some false
      rw [h9]
      simp only [show ¬ 0+5 ≤ bs.length by omega,ite_false]
      rfl
    · apply WP.block_nil
      simpa only [hz,Nat.mul_zero] using ha
  · refine WP.ite true ?_ (fun _ => ?_) (by simp)
    · change some (!(a.gpr .x9 == 0)) = some true
      rw [h9]
      simp only [show 0+5 ≤ bs.length by omega,ite_true]
      rfl
    · apply count_loop (cr := .x9) (n := bs.length/5) (by omega)
        (fun j => PrefixInv s P w mi X Xc Q x ep bs (5*j) 0)
      · intro j hj u hu
        refine WP.mono (groupBody_ok W hw hw' hR hL (by omega) hread hbytes hout hu)
          fun v ⟨hv,h9v⟩ => ⟨?_,?_⟩
        · simpa only [Nat.mul_add,Nat.mul_one] using hv
        · rw [h9v]
          split
          · change (1 ≠ 0 ↔ _)
            omega
          · change (0 ≠ 0 ↔ _)
            omega
      · simpa only [Nat.mul_zero] using ha

end VG.Proof.Bignum.AArch64.WindowFive
