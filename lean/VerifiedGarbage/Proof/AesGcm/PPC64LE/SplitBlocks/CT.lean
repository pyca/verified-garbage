module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SplitBlocks.Contract
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTBase
import VerifiedGarbage.Proof.AesGcm.PPC64LE.SplitBlocks.Lit
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.SplitBlocks.Contract
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTBase
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.SplitBlocks.Lit
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd

-- separate module: promote only the signature's public stack argument after the load.
/-! # Constant time for the source-prefix GCM wrapper -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.SplitBlocks
open VG VG.PPC64LE


theorem head_taint : ∃ h, (VG.Taint.check vectorTaint (Taint.ofRegs [])
    Impl.AesGcm.PPC64LE.SplitBlocks.head h).isSome=true := ⟨_,by taint_decide⟩


theorem rest_taint : ∃ h, (VG.Taint.check vectorTaint
    (Taint.ofRegs [.r3,.r4,.r5,.r6,.r7,.r8,.r9,.r10,.r11])
    Impl.AesGcm.PPC64LE.SplitBlocks.rest h).isSome=true := ⟨_,by taint_decide⟩



theorem encrypt_ct : ConstantTime isa (Spec.Gcm.encryptBlocksSplitContract PPC64LE.abi).pre
    (Spec.Gcm.encryptBlocksSplitContract PPC64LE.abi).pub Impl.AesGcm.PPC64LE.SplitBlocks.encrypt := by
  refine ct_of fun a b ha hb hp => ?_
  sig_pub [Spec.Gcm.encryptBlocksSplitContract,Spec.Gcm.encryptBlocksSplitSig,
    PPC64LE.abi,PPC64LE.argRegs,stackArg,stackArgAddr,List.getD,List.range,List.range.loop] at hp
  obtain ⟨hsp,h3,h4,h5,h6,h7,h8,h9,h10,hw⟩ := hp
  let rs : List Reg := [.r3,.r4,.r5,.r6,.r7,.r8,.r9,.r10]
  let I : State → Prop := fun s => (Spec.Gcm.encryptBlocksSplitContract PPC64LE.abi).pre s ∧
    s.sp=a.sp ∧ (∀ r ∈ rs, s.gpr r=a.gpr r) ∧ Contract.scratch s=Contract.scratch a
  have ib : I b := by
    refine ⟨hb,hsp.symm,fun r hr => ?_,hw.symm⟩
    simp only [rs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> symm <;> with_reducible assumption
  refine ⟨I,⟨ha,rfl,fun _ _ => rfl,rfl⟩,ib,?_⟩
  rw [Impl.AesGcm.PPC64LE.SplitBlocks.encrypt]
  refine CT.ite (a.gpr .r10 == 0) (fun s ⟨_,_,hg,_⟩ => by
    simp only [eval,State.read,Size.bits,BitVec.setWidth_eq,hg .r10 (by decide)])
    (fun _ => CT.skip) (fun _ => ?_)
  let restRegs : List Reg := rs++[.r11]
  let v : Reg → BitVec 64 := fun r => if r=.r11 then Contract.scratch a else a.gpr r
  let J : State → Prop := fun s => s.sp=a.sp ∧ ∀ r ∈ restRegs, s.gpr r=v r
  refine CT.seq (J := J) ?_ ?_ ?_
  · obtain ⟨_,hc⟩ := head_taint
    refine RelCT.taint (A := vectorTaint) (Taint.ofRegs []) (fun s t ⟨hs,ht⟩ => ?_) hc
    exact ⟨hs.2.1.trans ht.2.1.symm,fun r hr => False.elim (by simp only [Taint.mem_ofRegs,List.not_mem_nil] at hr)⟩
  · intro s ⟨hs,hsp,hg,hw⟩
    obtain ⟨_,_,hr,_⟩ := Contract.shared_pre s hs
    refine WP.mono (Wrapper.head_ok s hr) fun t ht => ?_
    subst t
    refine ⟨?_,fun r hr => ?_⟩
    · simpa only [Wrapper.headState,RegUpd.sp_write] using hsp
    · simp only [restRegs,rs,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl <;>
        simp only [v,Wrapper.headState,RegUpd.gpr_write,reduceCtorEq,ite_true,ite_false]
      all_goals first | exact hw | exact hg _ (by decide)
  · obtain ⟨_,hc⟩ := rest_taint
    refine RelCT.taint (A := vectorTaint) (Taint.ofRegs restRegs) (fun s t ⟨hs,ht⟩ => ?_) hc
    exact ⟨hs.1.trans ht.1.symm,fun r hr =>
      (hs.2 r (Taint.mem_ofRegs.mp hr)).trans (ht.2 r (Taint.mem_ofRegs.mp hr)).symm⟩

end VG.Proof.AesGcm.PPC64LE.SplitBlocks
