import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSetup

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def middleCode : List Instr := finalSetup ++ tailLoadCode ++ scaleConst

theorem middle_ok {s : State} {p : Addr}
    (ht : InverseTable.Words s.mem p) (hx : s.gpr .x1=p+3840)
    (hr : ∀ off∈[0,16,32,48], InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hq : ∀ e<4, vword (s.v .v31) e=8380417#32) :
    WP isa (.block middleCode) s fun t =>
      Keep [.x0,.x2,.x9,.x12] s t ∧ t.mem=s.mem ∧
      t.gpr .x0=s.gpr .x0-1024 ∧ t.gpr .x2=s.gpr .x0-1024 ∧ t.gpr .x12=8 ∧
      FinalRoots t ∧ ScaleRoots t := by
  simp only [middleCode,List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (finalSetup_ok s) fun a ⟨⟨⟨ha0,ha2,ha12,ham⟩,hak⟩,hav⟩ => ?_
  refine tailLoad_ok (p := p) ?_ ?_ ?_ fun b hload ho => ?_
  · simpa only [ham] using ht
  · rw [hak.get .x1 (by decide)]
    exact hx
  · simpa only [hak.rd,hak.wr,hak.get .x1 (by decide)] using hr
  · refine WP.mono (scaleConst_ok b) fun t hc => ?_
    have hot : Hoisted t := by
      intro j e he
      have hr30 : tailRootReg j.val≠.v30 := (show ∀ j : Fin 2, tailRootReg j.val≠.v30 by decide +kernel) j
      have hb30 : tailRecipReg j.val≠.v30 := (show ∀ j : Fin 2, tailRecipReg j.val≠.v30 by decide +kernel) j
      rw [hc.1.vec _ hr30,hc.1.vec _ hb30]
      exact ho j e he
    have hqt : ∀ e<4, vword (t.v .v31) e=8380417#32 := by
      intro e he
      rw [hc.1.vec .v31 (by decide),hload.get .v31 (by decide),hav]
      exact hq e he
    refine ⟨((hak.trans hload.keep).trans (constKeep_keep hc.1 (by decide))).mono,
      hc.1.mem.trans (hload.mem.trans ham),?_,?_,?_,hot.finalRoots hc.2 hqt,scaleVector_ready hc.2⟩
    · rw [hc.1.gpr .x0 (by decide),hload.gpr,ha0]
    · rw [hc.1.gpr .x2 (by decide),hload.gpr,ha2]
    · rw [hc.1.gpr .x12 (by decide),hload.gpr,ha12]

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
