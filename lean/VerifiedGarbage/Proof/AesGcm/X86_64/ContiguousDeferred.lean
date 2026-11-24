module
public import VerifiedGarbage.Proof.AesGcm.X86_64.ContiguousRunCT
import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Facts
import VerifiedGarbage.Proof.AesGcm.X86_64.OneShot
import VerifiedGarbage.Proof.AesGcm.X86_64.SealBody
import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Body
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.Call
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Impl.AesGcm.X86_64.Contiguous

/-! On the AES-NI/PCLMUL backend, hash the complete output after encryption. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.ContiguousSeal
open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks inc32 zeros padLen toBytes ofBytes)
open VG.Proof.Gcm (Absorbed xorKs lensBlock padded)

abbrev deferredSetup := [Instr.mov .r12 (.mem (at_ .rsp 16)),.mov .rbp (.mem (at_ .r15 tlenO)),.mov32 .rbx (imm 0)]
abbrev tailSetup := Contiguous.regs .rbx ++ [Instr.mov .r12 (.mem (at_ .r15 dataO)),.mov .rbp (.mem (at_ .r15 lenO))]
abbrev deferredFinish (v : GcmImpl) := Code.seq (.block tailSetup) (.seq (cryptTailG v.callees true)
    (.seq (.block deferredSetup) (tagCiphertext v.callees 0)))

theorem deferredSetup_ok {Ctx W SP D : Addr} {n : Nat} {s : State} (e : Env Ctx (W+16#64) W SP s)
    (slot : InRegions (s.rd++s.wr) (SP+16#64) 8) (dst : s.mem.readW (SP+16#64) 64=D)
    (total : s.mem.readW (W+192#64) 64=BitVec.ofNat 64 n) :
    WP isa (.block deferredSetup) s fun t => Env Ctx (W+16#64) W SP t ∧ t.mem=s.mem ∧ t.rd=s.rd ∧ t.wr=s.wr ∧
      t.gpr .r12=D ∧ t.gpr .rbp=BitVec.ofNat 64 n ∧ t.gpr .rbx=0 := by
  have read := e.perm.wR (show 192+8≤2560 by decide)
  apply WP.of_runBlock
  refine ⟨(((s.setReg .r12 D).setReg .rbp (BitVec.ofNat 64 n)).setReg .rbx 0),by xrun [e.rsp,e.r15,read,slot,dst,total],?_,rfl,rfl,rfl,?_,?_,?_⟩
  · apply e.keep (s':=(((s.setReg .r12 D).setReg .rbp (BitVec.ofNat 64 n)).setReg .rbx 0)) _ rfl rfl
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl <;> simp [gpr_setReg]
  all_goals simp [gpr_setReg]

theorem deferredBulk {M : CtxMode} (ctr : Proof.Aes.X86_64.Ctr32ToImpl) : BulkOk M
    (Contiguous.bulk (.seq (.block Contiguous.ctrArgs) (Contiguous.call ⟨ctr.callee.name,ctr.callee.code⟩))) false := by
  intro Ctx W SP S D R n s reg ob src slot apart
  exact bulk_ok (hash:=false) _ (fun h q a b c _ => deferredCtr_ok ctr h q a b c) reg ob src slot apart

theorem deferredFinish_ok (v : GcmImpl) {M : CtxMode} : FinishOk M (deferredFinish v) false := by
  intro Ctx W SP S D R n al s u H icb a reg ob post bulk hH hcb hal habs slot src slotW slotD dst slotDD slotDW
  let off := 16*(n/16)
  let rest := n-off
  let x := a++zeros (padLen a.length)
  have le : off≤n := Nat.mul_div_le _ _
  have hx : x.length%16=0 := by dsimp [x]; simp only [List.length_append,Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  obtain ⟨fr,rnds,hash,key,j,pre,count,abs,rem⟩ := ob_factsFrom reg.lay ob reg.sW reg.ks reg.sD post.frame hH hcb habs hx
    bulk.1 bulk.2.1 (Z:=[]) (by decide) (by change blockAt u.mem (yA W)=blockAt s.mem (yA W); exact bulk.2.2)
  simp only [List.append_nil] at abs
  have lt := reg.data.ok.lt
  have len : u.mem.readW (W+208#64) 64=BitVec.ofNat 64 rest := by rw [post.len]; congr 1; dsimp [rest,off]; omega
  have tail := (reg.data.of_eq post.rd post.wr).drop le
  have cipher := scalarCipher_ok (icb:=icb) v reg post slot src rnds len tail
  apply WP.seq_assoc
  refine WP.seq (cipher.mono fun z ⟨co,rd,wr⟩ => ?_)
  have wf := crFrame_one co.frame
  have keep (i) (lo : 128≤i) (hi : i+8≤216) := wf.readW (w:=64) (r:=⟨W+BitVec.ofNat 64 i,8⟩) (Region.contains_self _ _)
    (kept_oneFrame reg.lay tail.ok.w (.inl ⟨lo,hi⟩)) (by decide)
  have keepSP : z.mem.readW (SP+16#64) 64=D := by
    rw [wf.readW (r:=⟨SP+16#64,8⟩) (Region.contains_self _ _) (fun b hb => by
      simp only [oneFrame,List.mem_cons,List.not_mem_nil,or_false] at hb
      rcases hb with rfl|rfl|rfl|rfl|rfl
      · exact slotDW.sub_right (Region.sub_prefix (by decide))
      · exact slotDW.sub_right (Lay.wSub (by decide))
      · exact slotDW.sub_right (Lay.wSub (by decide))
      · exact slotDD.sub_right (Offset.sub_base _ (by omega_arith))
      · exact Offset.disjoint_below SP (by decide)) (by decide),dst]
  have total := (keep 192 (by decide) (by decide)).trans post.tlen
  have aLen := (keep 184 (by decide) (by decide)).trans ((fr.readW (r:=⟨W+184#64,8⟩) (Region.contains_self _ _)
      (kept_oneFrameB reg.lay reg.data.ok.w ob.t_w (.inl ⟨by decide,by decide⟩)) (by decide)).trans hal)
  have cHash := (blockAt_frame co.frame (fun b hb => (ctx_crFrame reg.lay tail b hb).sub_left (Lay.ctxSub (by decide)))).trans hash
  have cKey := (ciph_frame co.frame (ctx_crFrame reg.lay tail) ob.rounds.2).trans key
  have cJ : blockAt z.mem (W+16#64)=blockAt s.mem (W+16#64) := by
    rw [← j]; simpa using blockAt_frame co.frame (st_crFrame reg.lay tail.ok (d:=0) (k:=16) (by decide))
  have cAbs : Absorbed z.mem (yA W) (W+16#64+32#64) H x := abs.congr
    (blockAt_frame co.frame (st_crFrame reg.lay tail.ok (d:=16) (k:=16) (by decide)))
    (bytesAt_frame co.frame (st_crFrame reg.lay tail.ok (d:=32) (by have := Nat.mod_lt x.length (by decide : 0<16); omega_arith)) (by omega_arith))
  have ct := co.out count
  simp only [Nat.sub_zero,show bytesAt u.mem (D+BitVec.ofNat 64 (16*(n/16))) 0=[] from rfl,List.nil_append] at ct
  have pre' := bytesAt_frame co.frame (pre_crFrame (reg.data.ok.of_eq post.rd post.wr) le) (by dsimp [off]; omega_arith)
  have split (m : Mem) (addr : Addr) : bytesAt m addr n=bytesAt m addr off++bytesAt m (addr+BitVec.ofNat 64 off) rest := by
    rw [← bytesAt_add,Nat.add_sub_cancel' le]
  have ciphertext : bytesAt z.mem D n=xorKs (ciphOf s.mem Ctx R) icb 0 (bytesAt s.mem S n) := by
    rw [split z.mem D,split s.mem S,pre',ct,pre,key,rem,Proof.Gcm.xorKs_append,length_bytesAt,Nat.zero_add]
  refine WP.seq ((deferredSetup_ok co.env (by rw [rd,wr,post.rd,post.wr]; exact slotD) keepSP total).mono fun t ⟨env,mem,tr,tw,di,nb,zero⟩ => ?_)
  refine (tagCiphertext_ok v reg.lay (o:=0) (.inl rfl) hx env (mem ▸ cHash) (mem ▸ co.rounds) di nb
    (by rw [hx]; exact zero) (mem ▸ total) lt (mem ▸ aLen) ((reg.data.ok.of_eq (tr.trans (rd.trans post.rd)) (tw.trans (wr.trans post.wr)))) reg.data.ok.w).mono
    fun f ⟨ef,ff,rf,wf',_,_,tag⟩ => ?_
  rw [mem] at ff tag
  have data : bytesAt f.mem D n=bytesAt z.mem D n := bytesAt_frame ff (fun b hb => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with rfl|rfl|rfl|rfl|rfl
    · exact reg.data.ok.w.sub_right (Lay.wSub (by decide))
    · exact reg.data.ok.w.sub_right (Lay.wSub (by decide))
    · exact reg.data.ok.w.sub_right (Lay.wSub (by decide))
    · exact reg.data.ok.w.sub_right (Lay.wSub (by decide))
    · exact reg.data.ok.stk.symm) (Nat.le_of_lt lt)
  have tg := tag cAbs
  change bytesAt f.mem (W+0#64) 16=_ at tg
  rw [BitVec.add_zero,cKey,cJ,← data] at tg
  exact ⟨ef,rf.trans (tr.trans (rd.trans post.rd)),wf'.trans (tw.trans (wr.trans post.wr)),
    oneB_trans fr (oneB_trans (oneFrame_B le wf)
      (oneFrame_B (k:=0) (Nat.zero_le _) (by simpa using wFrame_one (D:=D) (n:=n) (o:=0) (.inl rfl) ff))),
    data.trans ciphertext,by simpa only [x,padded_eq] using tg⟩

theorem deferred_ok (v : GcmImpl) (ctr : Proof.Aes.X86_64.Ctr32ToImpl) {M : CtxMode} :
    RecordOk M (Contiguous.deferredBody v.callees ⟨ctr.callee.name,ctr.callee.code⟩) := by
  intro o u Ctx W SP Np A S D nl al n C X geo wrap src dst E hp hl ha
  exact body_ok (deferredBulk ctr) (deferredFinish_ok v) C X geo wrap ha src dst (oneMid_ok v C E hp hl ha)

theorem deferredCtr_ct {M : CtxMode} (ctr : Proof.Aes.X86_64.Ctr32ToImpl) :
    KernelCT M (.seq (.block Contiguous.ctrArgs) (Contiguous.call ⟨ctr.callee.name,ctr.callee.code⟩)) := by
  intro Ctx W SP S D R n
  let C (s : State) := CtrToCall s Ctx (cbA W) S D (W+448#64) R (n/16) ∧ s.gpr .rsp=SP
  have w {s : State} (h : KernelIn M Ctx W SP S D R n s) : WP isa (.block Contiguous.ctrArgs) s C :=
    (ctrArgs_ok h.reg (Nat.mul_div_le n 16) h.count h.read h.src h.dst).mono fun _ ⟨g,_,_,_,call⟩ => ⟨call,(g _ (by decide)).trans h.reg.env.rsp⟩
  exact RelCT.seq (Short.rel_next (rel_taint [.r13,.r14,.r15,.rsp] (fun _ _ h => env_agree h.1.reg.env h.2.reg.env)
    ⟨_,by taint_decide⟩) (fun _ => w) (fun _ => w))
    (ctrTo_rel ctr (fun _ _ h => ⟨_,_,_,_,_,_,_,h.1.1,h.2.1,h.1.2.trans h.2.2.symm⟩))

theorem deferredCtr_keeps {M : CtxMode} (ctr : Proof.Aes.X86_64.Ctr32ToImpl) :
    KernelKeeps M (.seq (.block Contiguous.ctrArgs) (Contiguous.call ⟨ctr.callee.name,ctr.callee.code⟩)) := by
  intro Ctx W SP S D R n s h
  exact (deferredCtr_ok ctr h.reg h.count h.read h.src h.dst).mono fun _ ⟨g,rd,wr,_⟩ => h.reg.env.of_saved g rd wr

theorem deferredFinish_ct (v : GcmImpl) {M : CtxMode} : FinishCT M (deferredFinish v) := by
  intro Ctx W SP S D R n al L hR dw
  let tail := D+BitVec.ofNat 64 (16*(n/16))
  let T := OneT Ctx W SP R al tail (n%16) n
  let G (s : State) := T s ∧ DataOk (W+16#64) W SP s D n ∧ InRegions (s.rd++s.wr) (SP+16#64) 8 ∧ s.mem.readW (SP+16#64) 64=D
  have dt : (⟨tail,n%16⟩ : Region).Disjoint ⟨W,2560⟩ :=
    dw.sub_left (Offset.sub_base _ (by omega_arith))
  have wp (u : State) (h : AfterBulk M Ctx W SP S D R n al u) : WP isa (.seq (.block tailSetup) (cryptTailG v.callees true)) u G := by
    obtain ⟨s,a,p⟩ := h.origin
    have re : n-16*(n/16)=n%16 := by omega_arith
    have t := h.scalar.tag
    have sc := scalarCipher_ok (icb:=0) v a.reg p a.read h.scalar.src t.rounds (re ▸ p.len) (re ▸ h.scalar.output)
    refine sc.mono fun z ⟨co,rd,wr⟩ => ?_
    have fr := crFrame_one co.frame
    rw [re] at fr
    have read : InRegions (z.rd++z.wr) (SP+16#64) 8 := by rw [rd,wr,p.rd,p.wr]; exact a.slotRead
    have data := a.reg.data.ok.of_eq (rd.trans p.rd) (wr.trans p.wr)
    refine ⟨t.frame L co.env rd wr dt fr,data,read,?_⟩
    rw [fr.readW (r:=⟨SP+16#64,8⟩) (Region.contains_self _ _) (fun b hb => by
      simp only [oneFrame,List.mem_cons,List.not_mem_nil,or_false] at hb
      rcases hb with rfl|rfl|rfl|rfl|rfl
      · exact a.dstWork.sub_right (Region.sub_prefix (by decide))
      · exact a.dstWork.sub_right (Lay.wSub (by decide))
      · exact a.dstWork.sub_right (Lay.wSub (by decide))
      · exact a.dstOut.sub_right (Offset.sub_base _ (by omega_arith))
      · exact Offset.disjoint_below _ (by decide)) (by decide)]
    exact (bulkSlot p a.dstWork a.dstOut (by decide)).trans a.dst
  let P (s : State) := T s ∧ s.gpr .r12=D ∧ s.gpr .rbp=BitVec.ofNat 64 n ∧ s.gpr .rbx=0 ∧ DataOk (W+16#64) W SP s D n
  have setup (s) (g : G s) : WP isa (.block deferredSetup) s P := by
    refine (deferredSetup_ok g.1.env g.2.2.1 g.2.2.2 g.1.tlen).mono fun t ⟨env,m,rd,wr,ptr,len,z⟩ => ?_
    exact ⟨⟨env,m ▸ g.1.rounds,m ▸ g.1.alen,m ▸ g.1.dat,m ▸ g.1.len,g.1.dD.of_eq rd wr,m ▸ g.1.tlen⟩,ptr,len,z,g.2.1.of_eq rd wr⟩
  apply rel_reassoc2
  refine RelCT.seq (Short.rel_next ((scalarCipher_ct v L (Nat.mod_le _ _) (Nat.mod_lt _ (by decide)) dt).mono
    (fun _ _ h => ⟨h.1.scalar,h.2.scalar⟩) (fun _ _ _ => trivial)) wp wp) ?_
  refine RelCT.seq (Short.rel_next (Short.rel_env_regs [] (fun _ h => h.1.env) (fun _ h => h.1.env)
    (fun _ _ _ _ _ h => by cases h) ⟨_,by taint_decide⟩) setup setup) ?_
  exact tagCiphertext_rel v L (o:=0) (.inl rfl) dt

theorem deferred_ct (v : GcmImpl) (ctr : Proof.Aes.X86_64.Ctr32ToImpl) {M : CtxMode} :
    RecordCT M (Contiguous.deferredBody v.callees ⟨ctr.callee.name,ctr.callee.code⟩) := by
  intro o p Ctx W SP Np A S D nl al n R a b
  exact RelCT.seq (ordinaryAad_ct v a b) (run_ct (deferredBulk ctr) (deferredCtr_ct ctr) (deferredCtr_keeps ctr)
    (deferredFinish_ct v) a.ctx.lay (a.rounds ▸ a.ctx.rounds) a.ctx.dE)

end VG.Proof.AesGcm.X86_64.ContiguousSeal
