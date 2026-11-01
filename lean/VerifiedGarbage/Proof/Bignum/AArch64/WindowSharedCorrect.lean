module

import VerifiedGarbage.Proof.Bignum.AArch64.WindowHelperContext
public import VerifiedGarbage.Proof.Bignum.AArch64.WindowSharedGuard
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowRawCT
public import VerifiedGarbage.Proof.Bignum.AArch64.WindowHelperContract
import VerifiedGarbage.Proof.Bignum.AArch64.SquareHelper

/-! A shared window verified against its reviewed callable contract. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowShared
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Rsa.Mont (numAt wOf wordAt arrAt aM minvWord)
open SquareHelper (numAt_eq)
open WindowHelper (fnContract fn_context)

theorem fn_correct (s : State)
    (h : fnContract.pre s) :
    ∃ tr t, Exec isa code s tr t ∧
      abiPreserved s t ∧ fnContract.post s t := by
  have hp := fn_context h
  simp only [WindowFive.RawWindowPre, off, BitVec.add_zero] at hp
  obtain ⟨mi,X,Xc,v,hc,ht,hy,hw,hw',hv,hd⟩ := hp
  have hx : X = numAt s.mem (s.gpr .x0) (wOf s.mem (s.gpr .x0)) aM :=
    hc.n.symm.trans (numAt_eq _ _ _ _).symm
  have hd' : Proof.Rsa.MontWindow.digit s.mem (s.gpr .x0) = v := by
    change (word s.mem (s.gpr .x0) (8 * Crt.sNib)).toNat = v
    rw [hd, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨tr,t,he,_,hlt,heq,hnb,hbt,hf,hk⟩ :=
    guarded_ok hc ht hw hw' hy hv hd
  refine ⟨tr,t,he,⟨fun r hr => hk.gpr r (by revert r; decide),hk.sp,hk.vcs⟩,?_,?_,hbt,hnb,?_⟩
  · rw [numAt_eq, ← hx]; exact hlt
  · rw [← hx, hd']
    simp only [numAt_eq]
    exact heq
  · intro i hi ha hh
    apply hf (s.gpr .x0 + BitVec.ofNat 64 i)
    have hn := h.2.2.1
    rw [show ofs (s.gpr .x0) (s.gpr .x0 + BitVec.ofNat 64 i) = i by
      exact Mem.sub_ofNat_toNat _ (by omega)]
    intro r hr
    simp only [rawWindowRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ha 2 (by decide)
    · exact ha 3 (by decide)
    · exact ha 6 (by decide)
    · exact ha 5 (by decide)
    · exact hh 20 (by decide)
    · exact hh 27 (by decide)
    · exact hh 26 (by decide)
    · exact hh 28 (by decide)

end VG.Proof.Bignum.AArch64.WindowShared
