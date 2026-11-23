module

public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.LoopState
import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.Semantics
meta import VerifiedGarbage.Impl.AesGcm.X86_64.DirectGather
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! Initialize the gather cursors without touching input or output. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.DirectGather
open VG VG.X86_64 Gather VG.X86_64.RegUpd Short
open VG.Impl.AesGcm.X86_64.DirectGather (setupG load store)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (blockAt)

private def setupMem (s : State) (m : Mem) : Mem :=
  let W := W s
  (((((((m.writeW (W+256#64) (Src s)).writeW (W+224#64) (stackArg s 1)).writeW (W+200#64) (Dst s)).writeW
    (W+192#64) (stackArg s 3)).writeW (W+208#64) (stackArg s 3)).writeW (W+240#64) (0#64)).writeW (W+264#64) (0#64))

private theorem slot_other {m : Mem} {w : Addr} {v : BitVec 64} {i j : Nat}
    (apart : i+8≤j ∨ j+8≤i) (hi : i+8≤272) (hj : j+8≤272) :
    (m.writeW (w+BitVec.ofNat 64 j) v).readW (w+BitVec.ofNat 64 i) 64 =
      m.readW (w+BitVec.ofNat 64 i) 64 :=
  Mem.readW_writeW_sep (Offset.sep w apart (by omega) (by omega)) (by decide)

private theorem setupFrame (s : State) (m : Mem) : Frame [⟨W s+192#64,80⟩] m (setupMem s m) := by
  have step {m' : Mem} (f : Frame [⟨W s+192#64,80⟩] m m') (i : Nat) (v : BitVec 64) (lo : 192≤i) (hi : i+8≤272) :
      Frame [⟨W s+192#64,80⟩] m (m'.writeW (W s+BitVec.ofNat 64 i) v) :=
    f.writeW (List.mem_singleton_self _) v (Offset.contains _ lo hi (by omega))
  unfold setupMem
  repeat' first | apply step _ _ _ (by decide) (by decide) | exact Frame.refl _ _

private theorem slotArg {M : CtxMode} {s : State} (h : Layout M s) {m : Mem} {v : BitVec 64} {i j : Nat}
    (lo : 8≤i) (hi : i+8≤56) (hj : j+8≤2560) :
    (m.writeW (W s+BitVec.ofNat 64 j) v).readW (SP s+BitVec.ofNat 64 i) 64=m.readW (SP s+BitVec.ofNat 64 i) 64 := by
  apply Mem.readW_writeW_sep _ (by decide)
  exact ((h.w_a.symm.sub_left (Offset.sub _ lo hi)).sub_right (Lay.wSub hj)).sep (Region.contains_self _ _) (Region.contains_self _ _)

theorem setup_wp {M : CtxMode} {s u t : State} (h : Layout M s) (a : GeneralAad s u t) :
    WP isa (.block setupG) t fun z => LoopAt M s 0 0 z ∧ z.zf=some (decide (Cnt s=0)) := by
  have env := a.env
  have perm (i : Nat) (bound : i+8≤2560) := env.perm.wW bound
  have read (i : Nat) (bound : i<6) : InRegions (t.rd++t.wr) (SP s+BitVec.ofNat 64 (8*(i+1))) 8 := by
    rw [a.rd,a.wr]; exact (h.oneCtx M.ge).args i bound
  have ar := h.stack_word a.frame
  have loadN := env.perm.wR (show 224+8≤2560 by decide)
  let m := setupMem s t.mem
  have num : m.readW (W s+224#64) 64=stackArg s 1 := by
    simp (disch := decide) only [m,setupMem,slot_other,Mem.readW_writeW_self64]
  have run : ∃ z, runBlock isa setupG t=some z ∧ z.mem=m ∧ z.rd=t.rd ∧ z.wr=t.wr ∧
      (∀ r,r≠.rax → z.gpr r=t.gpr r) ∧ z.zf=some (decide (Cnt s=0)) := by
    have arg (i j : Nat) (lo : 8≤i) (hi : i+8≤56) (hj : j+8≤2560) {v : BitVec 64} {m₀ : Mem} :=
      slotArg h (m:=m₀) (v:=v) lo hi hj
    refine ⟨_, by
      xrun [setupG, load, store, env.r15, env.rsp,
        read 0 (by decide), read 1 (by decide), read 2 (by decide), read 3 (by decide),
        ar 0 (by decide), ar 1 (by decide), ar 2 (by decide), ar 3 (by decide),
        perm 256 (by decide), perm 224 (by decide), perm 200 (by decide), perm 192 (by decide),
        perm 208 (by decide), perm 240 (by decide), perm 264 (by decide), loadN,
        arg 16 256 (by decide) (by decide) (by decide), arg 24 224 (by decide) (by decide) (by decide),
        arg 24 256 (by decide) (by decide) (by decide), arg 32 200 (by decide) (by decide) (by decide),
        arg 32 224 (by decide) (by decide) (by decide), arg 32 256 (by decide) (by decide) (by decide), num], ?_⟩
    refine ⟨rfl,rfl,rfl,fun r hr => ?_,?_⟩
    · simp only [gpr_setReg_of_ne _ _ hr,gpr_arithFlags]
    · have hv := and_self_beq (a:=Cnt s) (BitVec.isLt _)
      simp only [zf_arithFlags,BitVec.and_self]
      change some (m.readW (W s+224#64) 64 == 0)=_
      rw [num]
      exact congrArg some (by simpa only [BitVec.and_self,Cnt,ofNat_toNat] using hv)
  obtain ⟨z,run,mem,rd,wr,regs,flag⟩ := run
  refine WP.of_runBlock ⟨z,run,?_,flag⟩
  have f : Frame [⟨W s+192#64,80⟩] t.mem z.mem := mem ▸ setupFrame s t.mem
  have frm : Frame (changed s) s.mem z.mem := (a.frame.sub (fun r hr => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact ⟨_,List.mem_cons_self ..,fun _ hit => hit⟩
    · exact ⟨below (SP s) 56,by simp [changed],below_sub (by decide) (by decide)⟩)).trans (f.sub (fun r hr => by
      simp only [List.mem_singleton] at hr
      subst r; exact ⟨_,List.mem_cons_self ..,Lay.wSub (by decide)⟩))
  have apart {d n : Nat} (hi : d+n≤192) : ∀ r∈[⟨W s+192#64,80⟩],(⟨W s+BitVec.ofNat 64 d,n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact Offset.disjoint _ (.inl hi) (by omega) (by decide)
  have w (i : Nat) (hi : i+8≤192) := f.readW (Region.contains_self (W s+BitVec.ofNat 64 i) 8) (apart hi) (by decide : 64/8<2^64)
  obtain ⟨hh,hc⟩ := h.ctx_framed frm (R:=R s) (by change (s.gpr .rsi).toNat≤14; omega_using [h.rounds])
  have ez := env.keep (fun r hr => regs r (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> decide)) rd wr
  refine ⟨ez,
    rd.trans a.rd,wr.trans a.wr,a.saved.frame f (apart (by decide)),frm,Nat.zero_le _,fun _ => Nat.zero_le _,
    fun _ => rfl,rfl,?_,?_,?_,?_,?_,?_,?_,(w 184 (by decide)).trans a.alen,⟨(w 176 (by decide)).trans a.rounds.1,a.rounds.2⟩,
    hc,hh,(blockAt_frame f (apart (by decide))).trans a.j0,?_,?_,?_⟩
  · change z.mem.readW (W s+256#64) 64=Src s+0#64
    simp (disch := decide) only [mem,m,setupMem,slot_other,Mem.readW_writeW_self64,BitVec.add_zero]
  · simpa only [mem,Nat.sub_zero,Cnt,ofNat_toNat] using num
  · change z.mem.readW (W s+240#64) 64=0#64
    simp (disch := decide) only [mem,m,setupMem,slot_other,Mem.readW_writeW_self64]
  · exact mem ▸ Mem.readW_writeW_self64 _ _ _
  · simp (disch := decide) only [mem,m,setupMem,slot_other,Mem.readW_writeW_self64,BitVec.add_zero]
  · simp (disch := decide) only [mem,m,setupMem,slot_other,Mem.readW_writeW_self64,Nat.sub_zero,L,ofNat_toNat]
  · simp (disch := decide) only [mem,m,setupMem,slot_other,Mem.readW_writeW_self64,L,ofNat_toNat]
  · simp only [bytesAt,List.range_zero,List.map_nil,List.append_nil]
    apply a.abs.congr
    · simp only [add_ofNat_ofNat]; exact blockAt_frame f (apart (by decide))
    · simp only [add_ofNat_ofNat]
      exact bytesAt_frame f (apart (by omega_using [Nat.mod_lt (ad s ++ Spec.Gcm.zeros (Spec.Gcm.padLen (ad s).length)).length (by decide : 0<16)])) (by omega)
  · apply Proof.Gcm.ctr_zero
    have b := a.cb
    simp only [add_ofNat_ofNat] at b ⊢
    exact (blockAt_frame f (apart (by decide))).trans b
  · rfl

theorem setup_rel {s t u v : State} (pb : Pub s t) :
    RelCT isa (fun x y => GeneralAad s u x ∧ GeneralAad t v y) (.block setupG) fun _ _ => True := by
  apply rel_taint [.rsp,.r15] _ ⟨_,by taint_decide⟩
  intro x y h r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · rw [h.1.env.rsp,h.2.env.rsp]; exact pb.rsp.symm
  · rw [h.1.env.r15,h.2.env.r15]; exact pb.w.symm

end VG.Proof.AesGcm.X86_64.DirectGather
