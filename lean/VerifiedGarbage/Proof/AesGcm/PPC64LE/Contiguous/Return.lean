module

-- separate module: The common restore sequence transports the ABI separately from framing and scrubbing.

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contiguous.Bind
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamFinish
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Cmac.Spec

/-! # Write the tag and restore the caller's registers after either POWER payload layout -/

public section
namespace VG.Proof.AesGcm.PPC64LE.Contiguous
open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE VG.Spec.Gcm
open VG.Spec.Aes (bytesAt)

abbrev finished (s t : State) :=
  (ctBytes s t,bytesAt t.mem (stackArg s 1) 16)=encryptWith (cipherOf s) (ctxH s.mem (s.gpr .r3)) 16 (ivBytes s) (ptBytes s) (aadBytes s)

private theorem saved_cipher {s u : State} (h : CallLayout s) (g : Positions s u) (L : Lay (u.gpr .r29) (u.gpr .r30) (u.gpr .r31)) :
    ∀ r∈cipherFrame u,(savedR (u.gpr .r31)).Disjoint r := by
  have sep : (savedR (u.gpr .r31)).Disjoint (dat u) := by
    rw [g.work,dat,datLen,g.len,g.dst]
    exact (stack_disjoint h (r:=dstR s) (by simp [argsRegions])).sub_left fun addr ha => work_sub s addr (Offset.sub_base _ (by decide : 128+120≤1152) addr ha)
  intro r hr
  simp only [cipherFrame,prefixAreas,crFrame,taFrame,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact L.saved_st (by decide)
  · exact L.saved_st (by decide)
  · exact sep.sub_right (Region.sub_prefix (DirectGather.prefixLe _))
  · exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
  · exact sep.sub_right (Offset.sub_base _ (Nat.le_of_eq (Nat.add_sub_of_le (DirectGather.prefixLe _))))
  · exact L.saved_st (by decide)
  · exact L.saved_st (by decide)
  · exact L.saved_st (by decide)
  · exact saved_w (by decide) (.inl (by decide))

theorem return_wp {s e t u v : State} (h : CallLayout s) (p : Args s e) (q : Started e (work s) t)
    (oa : ReadyData s e t u) (g : Positions s u)
    (o : Tagged u v (ctxH s.mem (s.gpr .r3)) (ivBytes s) (aadBytes s)) (rv : v.rd=u.rd) (wv : v.wr=u.wr) :
    WP isa (.seq (.block tagOut) (.block restore)) v (fun y => abiPreserved e y ∧ finished s y) := by
  have L := (args_lay h).v g.key g.stream g.work
  have env : Env v.gpr e.sp v := ⟨fun _ _ => rfl,o.sp.trans oa.env.sp,by
    rw [o.regs .r29 (by decide),o.regs .r30 (by decide),o.regs .r31 (by decide)]
    rw [oa.env.r29,oa.env.r30,oa.env.r31]
    exact oa.env.perm.of_eq rv wv⟩
  have wk := (o.regs .r31 (by decide)).trans g.work
  have tag := (o.regs .r20 (by decide)).trans g.tag
  have tw : Covers [⟨v.gpr .r20,16⟩] v.wr := by rw [tag,wv,g.wr,h.wr]; exact covers_mem (by simp [tagR])
  have apart := (stack_disjoint h (r:=tagR s) (by simp [argsRegions])).symm.sub_right (work_sub s)
  have save := q.entered.saved.frame oa.frame (by
    rw [q.scratch,q.stream];exact saved_j0Frame (args_lay h))
  have kept : SavedAt v.mem (u.gpr .r31) e := by
    apply SavedAt.frame (by simpa only [g.work] using save) o.frame
    intro r hr
    rcases List.mem_append.mp hr with hx|hx
    · exact saved_cipher h g L r hx
    · exact saved_tagFrame L (.inl rfl) r hx
  have result := tagged_output h g (ready_frame p q oa) o
  refine WP.seq (WP.mono (tagOut_ok env tw (by rw [wk,tag];exact apart.sub_right (Region.sub_prefix (by decide)))) fun x ⟨copied,fr,reg,k⟩ => ?_)
  rw [tag] at fr
  have ct := bytesAt_frame fr (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact h.dt) (Nat.le_of_lt (stackArg s 0).isLt)
  have saved : SavedAt x.mem (work s) e := (g.work ▸ kept).frame fr (fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact apart.symm.sub_left (Offset.sub_base _ (by decide)))
  have ww : Covers [workR s] (x.rd++x.wr) := by
    apply Covers.right
    rw [k.wr,wv,g.wr,←p.wr];exact p.workWrite
  refine WP.mono (restore_ok ((reg .r31 (by decide)).trans wk) ww saved (k.sp.trans env.sp) (fun r hr => ?_)) fun y ⟨abi,mem,_,_,_⟩ => ?_
  · exact (reg _ (by revert r;decide)).trans ((o.regs r (by revert r;decide)).trans ((oa.env.fr r (by revert r;decide)).trans (q.entered.low r hr)))
  · rw [wk,tag] at copied
    refine ⟨abi,?_⟩
    change (bytesAt y.mem _ _,bytesAt y.mem _ _)=_
    rw [mem,ct,copied,result.tag]
    change (ctBytes s v,_)=_
    rw [result.data]
    unfold encryptWith
    refine Prod.ext rfl ?_
    exact (List.take_of_length_le (by rw [VG.Spec.Gcm.fullTag,Proof.Gcm.length_gctr,Proof.Cmac.toBytes_length])).symm

end VG.Proof.AesGcm.PPC64LE.Contiguous
