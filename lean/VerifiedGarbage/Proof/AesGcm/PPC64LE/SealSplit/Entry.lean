module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.Contract
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Seal
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.Body
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: adapt the source-first signature to the shared seal stages.
/-! # Split-seal entry permissions -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.SealSplit
open VG VG.PPC64LE


def prepared (s : State) : State := Prelude.state (allocated 112 s)


theorem prepared_gpr (s : State) (r : Reg) (hr : r∉[Reg.r0,.r9,.r10,.r11,.r12]) :
    (prepared s).gpr r=s.gpr r := (Prelude.keep (allocated 112 s)).gpr hr


theorem prepared_destination (s : State) (hs : scratchContract.pre s) : (prepared s).gpr .r9=stackArg s 0 :=
  (Prelude.destination (allocated 112 s) (prelude_config s hs)).trans (allocated_arg s 0 (by decide))


theorem prepared_length (s : State) (hs : scratchContract.pre s) : (prepared s).gpr .r10=stackArg s 1 :=
  (Prelude.length (allocated 112 s) (prelude_config s hs)).trans (allocated_arg s 1 (by decide))


theorem prepared_tag (s : State) (hs : scratchContract.pre s) : stackArg (prepared s) 0=stackArg s 2 :=
  (Prelude.tag_argument (allocated 112 s) (prelude_config s hs)).trans (allocated_arg s 2 (by decide))


theorem prepared_work (s : State) : stackArg (prepared s) 1=stackArg s 3 :=
  (Prelude.work_argument (allocated 112 s)).trans (allocated_work s)


theorem prepared_frame (s : State) : Frame [stackR s,workR s] s.mem (prepared s).mem := by
  have ha : Frame [stackR s,workR s] s.mem (allocated 112 s).mem := by
    refine (Frame.refl _ _).writeW (r := stackR s) (by simp) s.sp ?_
    exact Region.contains_self' (by decide : 8≤112)
  apply ha.trans
  apply (Prelude.frame (allocated 112 s)).sub
  intro r hr
  rw [Prelude.writes,allocated_work] at hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨workR s,by simp,Offset.sub_base _ (by decide)⟩
  · exact ⟨stackR s,by simp,Offset.sub_base _ (by decide)⟩
  · exact ⟨stackR s,by simp,Offset.sub_base _ (by decide)⟩


theorem prepared_bytes (s : State) (hs : scratchContract.pre s) (r : Region)
    (hr : r∈[contextR s,nonceR s,aadR s,sourceR s,dataR s,tagR s]) :
    Spec.Aes.bytesAt (prepared s).mem r.base r.len=Spec.Aes.bytesAt s.mem r.base r.len := by
  have lay := layout_pre s hs
  apply bytesAt_frame (prepared_frame s) _ _
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl
    · exact (lay.stackApart r (List.mem_append_left _ hr)).symm
    · exact lay.workApart r hr
  · have hf := lay.fits r (List.mem_append_left _ hr)
    omega


theorem entry_access (s : State) (hs : scratchContract.pre s) : SealAccess (prepared s) := by
  have lay := layout_pre s hs
  have hg := prepared_gpr s
  have h9 := prepared_destination s hs
  have h10 := prepared_length s hs
  have ht := prepared_tag s hs
  have hw := prepared_work s
  have hargs0 : ∀ rd wr, stackArg ((prepared s).withRegions rd wr) 0=stackArg s 2 := fun _ _ => ht
  have hargs1 : ∀ rd wr, stackArg ((prepared s).withRegions rd wr) 1=stackArg s 3 := fun _ _ => hw
  have hargs : ∀ rd wr, args ((prepared s).withRegions rd wr) 2=args (prepared s) 2 := fun _ _ => rfl
  have hreads : sealReads (prepared s)=[contextR s,nonceR s,aadR s,args (prepared s) 2] := by
    simp only [sealReads,hg .r3 (by decide),hg .r5 (by decide),hg .r6 (by decide),hg .r7 (by decide),hg .r8 (by decide)]
    rfl
  have hwrites : sealWrites (prepared s)=[dataR s,tagR s,workR s] := by
    simp only [sealWrites,h9,h10,ht,hw]
    rfl
  have harg : Region.Sub (args (prepared s) 2) (stackR s) := Offset.sub_base _ (by decide)
  have hf : (prepared s).sp.toNat+112≤2^64 := by
    change (s.sp-112#64).toNat+112≤2^64
    rw [toNat_sub_ofNat' lay.spFit.1]
    have := s.sp.isLt
    omega
  refine ⟨?_,?_,?_⟩
  · change sealPre ((prepared s).withRegions (sealReads (prepared s)) (sealWrites (prepared s)))
    simp only [sealPre,State.withRegions_gpr,State.withRegions_rd,State.withRegions_wr,
      hargs0,hargs1,h9,h10,hg .r3 (by decide),hg .r4 (by decide),hg .r5 (by decide),
      hg .r6 (by decide),hg .r7 (by decide),hg .r8 (by decide)]
    rw [hargs]
    change sealReads (prepared s)=[contextR s,nonceR s,aadR s,args (prepared s) 2] ∧
      sealWrites (prepared s)=[dataR s,tagR s,workR s] ∧ _
    refine ⟨hreads,hwrites,lay.dataApart (contextR s) (by simp),lay.workApart (contextR s) (by simp),
      lay.dataApart (nonceR s) (by simp),lay.workApart (nonceR s) (by simp),
      lay.dataApart (aadR s) (by simp),lay.workApart (aadR s) (by simp),
      lay.tagApart (dataR s) (by simp),lay.workApart (dataR s) (by simp),?_,
      lay.workApart (tagR s) (by simp),?_,
      lay.fits (contextR s) (by simp),lay.fits (nonceR s) (by simp),lay.fits (aadR s) (by simp),
      lay.fits (dataR s) (by simp),lay.fits (workR s) (by simp),hf,lay.rounds⟩
    · exact (lay.stackApart (dataR s) (by simp)).symm.sub_right harg
    · exact (lay.stackApart (workR s) (by simp)).symm.sub_right harg
  · have ww : Covers (sealWrites (prepared s)) (prepared s).wr := by
      rw [hwrites]
      change Covers [dataR s,tagR s,workR s] (frameR 112 s::s.wr)
      rw [lay.wr]
      exact Covers.of_mem (by intro r hr; exact List.mem_cons_of_mem _ hr)
    apply Covers.append_left _ (Covers.right ww)
    rw [hreads]
    have ha : Covers [args (prepared s) 2] (prepared s).wr := by
      apply Covers.trans (Covers.of_sub (rs' := [frameR 112 s]) ?_)
      · change Covers [frameR 112 s] (frameR 112 s::s.wr)
        exact Covers.of_mem (by simp)
      · intro r hr
        rw [List.mem_singleton] at hr
        subst r
        refine ⟨frameR 112 s,List.mem_singleton_self _,64,?_,by change 64+16≤80; decide⟩
        change s.sp-112#64+96=(s.sp-112#64+32)+BitVec.ofNat 64 64
        bv_omega
    refine Covers.cons ?_ (Covers.cons ?_ (Covers.cons ?_ (Covers.right ha)))
    all_goals
      change Covers _ (s.rd++(frameR 112 s::s.wr))
      rw [lay.rd]
      exact Covers.of_mem (by simp)
  · rw [hwrites]
    change Covers [dataR s,tagR s,workR s] (frameR 112 s::s.wr)
    rw [lay.wr]
    exact Covers.of_mem (by intro r hr; exact List.mem_cons_of_mem _ hr)

end VG.Proof.AesGcm.PPC64LE.SealSplit
