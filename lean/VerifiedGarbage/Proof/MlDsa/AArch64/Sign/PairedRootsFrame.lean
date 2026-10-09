import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRoots

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64

theorem PairedRoots.frame {S : Nat} {s t : State} {W : List Region} (h : PairedRoots S s)
    (hf : Frame W s.mem t.mem) (hd : ∀r∈W,(⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩ : Region).Disjoint r)
    (hr : t.rd=s.rd) (hw : t.wr=s.wr) (hs : t.sp=s.sp) (hy : t.syms=s.syms) :
    PairedRoots S t := by
  refine ⟨?_,by simpa only [hy] using h.fit,?_,?_,?_⟩
  · intro i hi
    rw [hy,hf.readW (r:=⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩)
      (Offset.contains_base _ (by omega) (by omega)) hd (by decide)]
    exact h.held i hi
  · simpa only [hy,hr,hw] using h.readable
  · simpa only [hy,hw] using h.writable
  · simpa only [hy,hs] using h.stack

end VG.Proof.MlDsa.AArch64.Sign
