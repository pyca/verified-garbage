module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.Correct
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.CTEntry
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.Correct
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.CTEntry
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd

-- separate module: public stack arguments are promoted only after their proved loads.
/-! # Constant time of the source-first argument adapter -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.SealSplit.CTPrelude
open VG VG.PPC64LE
open CTEntry (entryRegs)

structure Initial (base s : State) : Prop where
  pre : scratchContract.pre s
  sp : s.sp=base.sp
  regs : ∀ r ∈ entryRegs, s.gpr r=base.gpr r
  args : ∀ i<4, stackArg s i=stackArg base i


def AllocatedI (base a : State) : Prop := ∃ s, Initial base s ∧ a=allocated 112 s

def PreparedI (base a : State) : Prop := ∃ s, Initial base s ∧ a=prepared s


theorem head_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [])
    (.block Impl.AesGcm.PPC64LE.SealSplit.loadWork) h).isSome=true := ⟨_,by taint_decide⟩


theorem rest_taint : ∃ h, (VG.Taint.check VG.PPC64LE.taint (Taint.ofRegs [.r11,.r12])
    (.block (Impl.AesGcm.PPC64LE.SealSplit.sourceSaved.map (fun (r,o) => Instr.store .d r .r11 o)++
      Impl.AesGcm.PPC64LE.SealSplit.config)) h).isSome=true := ⟨_,by taint_decide⟩


theorem prelude_ct (base : State) :
    CT (AllocatedI base) (.block Impl.AesGcm.PPC64LE.SealSplit.prelude) := by
  rw [Impl.AesGcm.PPC64LE.SealSplit.prelude,List.append_assoc]
  refine RelCT.block_append (CT.seq (J := fun a => ∃ s, Initial base s ∧ a=Prelude.headState (allocated 112 s)) ?_ ?_ ?_)
  · obtain ⟨_,hc⟩ := head_taint
    exact CT.taintEq [] base.gpr (base.sp-112) (fun a ⟨s,hs,ha⟩ => ⟨by rw [ha]; change s.sp-112#64=base.sp-112; rw [hs.sp]; rfl,by simp⟩) hc
  · intro a ⟨s,hs,ha⟩
    subst a
    exact WP.mono (Prelude.head_ok _ ((prelude_config s hs.pre).reads 232 (by decide))) fun t ht => ⟨s,hs,ht⟩
  · obtain ⟨_,hc⟩ := rest_taint
    let v : Reg → BitVec 64 := fun r => if r=.r11 then stackArg base 3 else base.sp-112
    refine CT.taintEq [.r11,.r12] v (base.sp-112) (fun a ⟨s,hs,ha⟩ => ⟨?_,?_⟩) hc
    · rw [ha]
      change s.sp-112#64=base.sp-112
      rw [hs.sp]
      rfl
    · intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · change a.gpr .r11=stackArg base 3
        rw [ha]
        change Prelude.work (allocated 112 s)=stackArg base 3
        rw [allocated_work,hs.args 3 (by decide)]
      · change a.gpr .r12=base.sp-112
        rw [ha]
        change s.sp-112#64=base.sp-112
        rw [hs.sp]
        rfl


theorem prepared_public {base s : State} (hb : scratchContract.pre base) (hs : Initial base s) :
    (prepared s).sp=(prepared base).sp ∧
    (∀ r ∈ entryRegs, (prepared s).gpr r=(prepared base).gpr r) ∧
    stackArg (prepared s) 1=stackArg base 3 ∧ stackArg (prepared s) 0=stackArg base 2 := by
  refine ⟨by change s.sp-112#64=base.sp-112#64; rw [hs.sp],fun r hr => ?_,by rw [prepared_work,hs.args 3 (by decide)],?_⟩
  · simp only [entryRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact (prepared_gpr s _ (by decide)).trans ((hs.regs _ (by decide)).trans (prepared_gpr base _ (by decide)).symm)
      | skip
    · rw [prepared_destination s hs.pre]
      rw [prepared_destination base hb,hs.args 0 (by decide)]
    · rw [prepared_length s hs.pre,prepared_length base hb,hs.args 1 (by decide)]
  · rw [prepared_tag s hs.pre,hs.args 2 (by decide)]

end VG.Proof.AesGcm.PPC64LE.SealSplit.CTPrelude
