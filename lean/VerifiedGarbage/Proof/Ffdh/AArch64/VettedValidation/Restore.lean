module

public import VerifiedGarbage.Proof.Ffdh.AArch64.VettedValidation.Recognize
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! A recognition miss restores exactly the original general-validator arguments. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.VettedValidation
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure Restored (s t : State) : Prop where
  args : t.gpr .x0=s.gpr .x0 ∧ t.gpr .x1=s.gpr .x1 ∧ t.gpr .x2=s.gpr .x2 ∧
    t.gpr .x3=s.gpr .x3 ∧ t.gpr .x4=s.gpr .x4
  domain : CheckDomain.cdDom t=CheckDomain.cdDom s
  keep : Keep clobbers s t

theorem restore_ok {s t : State} (g : Geometry s) (h : Result s t) :
    WP isa (.block VG.Impl.Ffdh.AArch64.VettedValidation.restore) t (Restored s) := by
  refine WP.mono (WP.keep [.x0,.x1,.x2,.x3,.x4] (Q:=fun u =>
    (u.gpr .x0=s.gpr .x0 ∧ u.gpr .x1=s.gpr .x1 ∧ u.gpr .x2=s.gpr .x2 ∧
     u.gpr .x3=s.gpr .x3 ∧ u.gpr .x4=s.gpr .x4) ∧ u.mem=t.mem) ?_ rfl rfl rfl) ?_
  · unfold VG.Impl.Ffdh.AArch64.VettedValidation.restore
    brun [h.base,hdr_enc (show sDom<32 by decide),hdr_enc (show sDL<32 by decide),
      hdr_enc (show sLen<32 by decide),hdr_enc (show sCtx<32 by decide),
      (g.scratch.congr h.keep.wr).ld (d:=8*sDom) (by unfold sDom;have :=g.room;omega),
      (g.scratch.congr h.keep.wr).ld (d:=8*sDL) (by unfold sDL;have :=g.room;omega),
      (g.scratch.congr h.keep.wr).ld (d:=8*sLen) (by unfold sLen;have :=g.room;omega),
      (g.scratch.congr h.keep.wr).ld (d:=8*sCtx) (by unfold sCtx;have :=g.room;omega),
      h.savedDomain,h.savedLength,h.savedKeyLength,h.savedWords]
  · rintro u ⟨⟨args,mem⟩,rest⟩
    refine ⟨args,?_,(h.keep.trans rest).mono (by
      intro r hr
      rcases List.mem_append.mp hr with hr|hr
      · exact hr
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl|rfl|rfl|rfl <;> decide)⟩
    unfold CheckDomain.cdDom
    rw [args.1,args.2.1,mem]
    unfold Spec.Rsa.bytesAt
    apply List.map_congr_left
    intro i hi
    exact h.frame _ (Or.inr (g.outside i (by simpa only [CheckDomain.cdDom,Spec.Rsa.bytesAt,List.length_map,List.length_range] using List.mem_range.mp hi)))

theorem Restored.pre {s t : State} (h : Restored s t) (hs : pre s) : CheckDomain.cdPre (plain t) := by
  obtain ⟨hp,_⟩:=hs
  simp only [CheckDomain.cdPre,stripConsts_gpr,stripConsts_wr] at hp ⊢
  rw [h.args.1,h.args.2.1,h.args.2.2.1,h.args.2.2.2.1,h.args.2.2.2.2]
  change t.rd.take (t.rd.length-Policy.tableConsts.length)=_ ∧ _
  rw [h.keep.rd,h.keep.wr]
  exact hp

theorem Restored.abi {s t : State} (h : Restored s t) : abiPreserved s t :=
  ⟨fun r hr =>h.keep.gpr r (by revert r;decide),h.keep.sp,h.keep.vcs⟩

end VG.Proof.Ffdh.AArch64.VettedValidation
