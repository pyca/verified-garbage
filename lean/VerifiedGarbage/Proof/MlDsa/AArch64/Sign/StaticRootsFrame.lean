import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRoots

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64

/-- Root preservation also applies to a prologue, which changes the layout's
base registers but preserves permissions, stack pointer, and symbols. -/
theorem StaticTable.frame {S : Nat} {name : String} {words : List (BitVec 64)}
    {s t : State} {W : List Region} (h : StaticTable S name words s)
    (hf : Frame W s.mem t.mem) (hd : ∀ r∈W,(⟨s.syms name,3904⟩ : Region).Disjoint r)
    (hr : t.rd=s.rd) (hw : t.wr=s.wr) (hs : t.sp=s.sp) (hy : t.syms=s.syms) :
    StaticTable S name words t := by
  refine ⟨?_,by simpa only [hy] using h.fit,?_,?_,?_⟩
  · intro i hi
    rw [hy,hf.readW (r := ⟨s.syms name,3904⟩)
      (Offset.contains_base _ (by omega) (by omega)) hd (by decide)]
    exact h.held i hi
  · simpa only [hy,hr,hw] using h.readable
  · simpa only [hy,hw] using h.writable
  · simpa only [hy,hs] using h.stack

end VG.Proof.MlDsa.AArch64.Sign
