module

-- separate module: Isolate the concrete register trace at entry from the two-run payload proof.

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contiguous.Entry
public import VerifiedGarbage.Proof.Gather.PPC64LE.LoopCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.AesGcm.PPC64LE.Contiguous
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-! # Public memory traces at contiguous POWER AES-GCM call boundaries -/

public section
namespace VG.Proof.AesGcm.PPC64LE.Contiguous
open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE.Contiguous
open VG.Proof.Gather.PPC64LE (Eq2 TT rel_taint rel_seq)

theorem entry_rel {s t : State} {w : Addr} (a : Arguments s w) (b : Arguments t w) (sp : s.sp = t.sp) :
    RelCT isa (Eq2 s t) (.block entry) TT := by
  rw [entry,List.append_assoc]
  apply RelCT.block_append
  refine rel_seq (rel_taint [] sp (by simp) (by taint_decide))
    (oneA_at (off := 112) (by decide) (by decide) (a.slot 2 (by decide)) a.scratch)
    (oneA_at (off := 112) (by decide) (by decide) (b.slot 2 (by decide)) b.scratch)
    fun x y ⟨h,_,kx⟩ ⟨k,_,ky⟩ => ?_
  exact rel_taint [.r12] (kx.sp.trans (sp.trans ky.sp.symm)) (by simpa using h.trans k.symm) (by taint_decide)

theorem afterBulk_rel {s t : State} (sp : s.sp = t.sp) :
    RelCT isa (Eq2 s t) (.block afterBulk) TT :=
  rel_taint [] sp (by simp) (by taint_decide)

end VG.Proof.AesGcm.PPC64LE.Contiguous
