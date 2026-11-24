module

-- separate module: The functional stack-frame theorem is compiled before the separate timing certificate.

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contiguous.Return
public import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.Omega

/-! # Correctness of the complete contiguous POWER seal including its stack frame -/

public section
namespace VG.Proof.AesGcm.PPC64LE.Contiguous
open VG VG.PPC64LE VG.Impl.StackScratch.PPC64LE
open VG.Impl.AesGcm.PPC64LE.Contiguous (body)
open VG.Spec.Aes (bytesAt)

abbrev framed : Prog isa := .frame (.alloc 1280) (.seq (.block (setArgsAt 1280 2 128)) body) (.free 1280)

theorem body_wp [Proof.Gcm.PPC64LE.GhashLaw] [Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] {s e : State}
    (h : CallLayout s) (p : Args s e) : WP isa body e (fun y => abiPreserved e y ∧ finished s y) := by
  apply WP.seq
  refine WP.mono (entry_wp p.arguments) fun t q => ?_
  have middle := WP.seq (WP.mono (WP.with_rdwr (prepare_wp h p q)) fun u ⟨oa,rd,wr,_⟩ => by
    let g := positions p q oa rd wr
    exact WP.seq (WP.mono (WP.with_rdwr (bound_wp h g oa)) fun v ⟨o,rv,wv,_⟩ => return_wp h p q oa g o rv wv))
  obtain ⟨_,_,ex,result⟩ := middle
  cases ex with
  | seq eab ec => cases eab with
    | seq ea eb => exact ⟨_,_,.seq ea (.seq eb ec),result⟩

theorem release {s e y : State} (h : CallLayout s) (p : Args s e) (abi : abiPreserved e y)
    (post : finished s y) (m : Mem) (us : Nat → BitVec 64) (fl : Frame [stack s] y.mem m) :
    abiPreserved s { freed 1280 y with mem:=m,unknowns:=us } ∧ finished s { freed 1280 y with mem:=m,unknowns:=us } := by
  have keep : ∀ r∈preserved,r≠Reg.r0 ∧ r≠Reg.r12 := by decide
  constructor
  · apply abiPreserved_lost
    simp only [abiPreserved,freed_gpr_eq,freed_sp_eq,freed_lr_eq]
    obtain ⟨gpr,sp,lr⟩ := abi
    refine ⟨fun r hr => (gpr r hr).trans (p.regs r (keep r hr).1 (keep r hr).2),?_,lr.trans p.lr⟩
    rw [sp,p.sp];exact base_old s
  · have same {r : Region} (dis : r.Disjoint (stack s)) :
        bytesAt m r.base r.len=bytesAt y.mem r.base r.len :=
      List.map_congr_left fun i hi => lost_byte fl dis (List.mem_range.mp hi)
    have d := same (stack_disjoint h (r:=dstR s) (by simp [argsRegions])).symm
    have t := same (stack_disjoint h (r:=tagR s) (by simp [argsRegions])).symm
    change (bytesAt m _ _,bytesAt m _ _)=_
    change bytesAt m (s.gpr .r10) (stackArg s 0).toNat=_ at d
    change bytesAt m (stackArg s 1) 16=_ at t
    rw [d,t];exact post

theorem framed_wp [Proof.Gcm.PPC64LE.GhashLaw] [Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] {s : State} (h : CallLayout s) :
    WP isa framed s (fun y => abiPreserved s y ∧ finished s y) := by
  obtain ⟨run,pp⟩ := args_run h
  refine WP.alloc ⟨by decide,by decide,by decide⟩ (by omega_using [h.space]) ?_
  refine WP.seq (WP.mono (show WP isa (.block (setArgsAt 1280 2 128)) (allocated 1280 s) (Args s) from
    ⟨_,_,.block run,pp⟩) fun e p => ?_)
  exact WP.mono (body_wp h p) fun _ ⟨abi,post⟩ => release h p abi post

end VG.Proof.AesGcm.PPC64LE.Contiguous
