module
public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.Call

public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.General

public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.StepGeometry
import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.Semantics
import VerifiedGarbage.Proof.AesGcm.X86_64.Split.PrefixNCT
import VerifiedGarbage.Proof.Gcm.StreamTo
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT
meta import VerifiedGarbage.Impl.AesGcm.X86_64.DirectGather
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-! The generic gather path authenticates all complete 256-byte batches of the first slice
before handing its remainder to the descriptor loop. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.DirectGather
open VG VG.X86_64 VG.X86_64.RegUpd Gather
open VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.DirectGather
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

abbrev preBytes (s : State) := 256 * (sl s 0 / 256)

structure BulkTested (M : CtxMode) (s t : State) : Prop extends LoopAt M s 0 0 t where
  r10 : t.gpr .r10=dp s 0
  rax : t.gpr .rax=BitVec.ofNat 64 (sl s 0) >>> 8
  zero : t.zf=some (decide (sl s 0/256=0))

theorem bulkTest_wp {M : CtxMode} {s u : State} (h : Layout M s) (e : LoopAt M s 0 0 u) (hc : 0<Cnt s) :
    WP isa (.block bulkTest) u (BulkTested M s) := by
  have a := descriptor_input h e hc
  have hr := e.env.perm.wR (show 256+8≤2560 by decide)
  have sh : BitVec.ofNat 64 (sl s 0) >>> 8=BitVec.ofNat 64 (sl s 0/256) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight,toNat_ofNat_of_lt (BitVec.isLt _),Nat.shiftRight_eq_div_pow,
      toNat_ofNat_of_lt (by omega_using [show sl s 0<2^64 from BitVec.isLt _])]
  have zero := and_self_beq (a:=sl s 0/256) (by omega_using [show sl s 0<2^64 from BitVec.isLt _])
  refine WP.of_runBlock ⟨_, by xrun [bulkTest,load,e.env.r15,hr,a.ptr,a.rn,a.size], ?_⟩
  refine ⟨{e with env:=e.env.keep ?_ rfl rfl}, ?_, ?_, ?_⟩
  · intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> simp [gpr_setFlags,gpr_setReg]
  · simp [gpr_setReg,gpr_setFlags]
  · simp [gpr_setReg]
  · simp only [zf_arithFlags,sh,zero]


abbrev bulkMem (s : State) (m : Mem) : Mem :=
  ((slot m (W s) 264 (BitVec.ofNat 64 (preBytes s))).writeW (W s+200#64)
    (Dst s+BitVec.ofNat 64 (preBytes s))).writeW (W s+208#64) (BitVec.ofNat 64 (L s-preBytes s))

abbrev bulkState (s u : State) : State := {u with mem:=bulkMem s u.mem}

theorem bulkMem_frame (s : State) (m : Mem) : Frame [⟨W s+192#64,80⟩] m (bulkMem s m) := by
  have step {m' : Mem} (f : Frame [⟨W s+192#64,80⟩] m m') (i : Nat) (v : Addr) (lo : 192≤i) (hi : i+8≤272) :
      Frame [⟨W s+192#64,80⟩] m (m'.writeW (W s+BitVec.ofNat 64 i) v) :=
    f.writeW (List.mem_singleton_self _) v (Offset.contains _ lo hi (by omega))
  unfold bulkMem slot
  repeat' first | apply step _ _ _ (by decide) (by decide) | exact Frame.refl _ _

theorem pre_le {M : CtxMode} {s : State} (h : Layout M s) (hc : 0<Cnt s) :
    preBytes s≤sl s 0 ∧ sl s 0≤L s := by
  refine ⟨Nat.mul_div_le ..,?_⟩
  have bound := h.glen ▸ gl_mono s (i:=1) hc
  simpa only [gl_succ,gl_zero,Nat.zero_add] using bound

theorem bulk_regs {M : CtxMode} {s u : State} (h : Layout M s) (e : LoopAt M s 0 0 u) (hc : 0<Cnt s) :
    Split.CallRegions M (K s) (W s) (SP s) (Dst s) (sb s 0) (R s) (L s) (preBytes s) (bulkState s u) := by
  have c := h.oneCtx M.ge
  have k : Region.Sub (below (SP s) 56) (below (SP s) 2512) := below_sub (by decide) (by decide)
  have region := slice_mem s (i:=0) hc
  obtain ⟨sd,_,sw⟩ := h.ls _ region
  obtain ⟨pr,ln⟩ := pre_le h hc
  have sub : (⟨sb s 0,preBytes s⟩ : Region).Sub ⟨sb s 0,sl s 0⟩ := Region.sub_prefix pr
  have f := bulkMem_frame s u.mem
  have apart {d n : Nat} (hi : d+n≤192) : ∀ r∈[⟨W s+192#64,80⟩],(⟨W s+BitVec.ofNat 64 d,n⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    exact Offset.disjoint _ (.inl hi) (by omega) (by decide)
  have wrap : (sb s 0).toNat + sl s 0 ≤ 2^64 := h.w_ls _ region
  have ext := h.ext.keep e.rd e.wr e.frame h.ext_apart
  refine ⟨e.env.keep (fun _ _ => rfl) rfl rfl,c.lay,
    ⟨(f.readW (Region.contains_self _ _) (apart (d:=176) (by decide)) (by decide)).trans e.rounds.1,e.rounds.2⟩,
    c.data.of_eq e.rd e.wr,?_,sw.sub_left sub,sd.sub_left sub,by omega,
    Nat.le_trans pr ln,h.b_w.sub_left k,h.b_d.sub_left k,((h.b_ls _ region).sub_left k).sub_right sub,
    h.b_k.sub_left k,Nat.le_trans (by decide) h.w_sp,ext.keep rfl rfl f ?_⟩
  · change Covers [_] (u.rd++u.wr)
    rw [e.rd,e.wr,h.rd]
    exact Split.covers_pre (covers_of_mem (by simp [region])) pr
  · intro r hr; simp only [List.mem_singleton] at hr; subst r
    exact h.k_w.sub_right (Lay.wSub (by decide))



private structure Writes (s u t : State) : Prop where
  env : Env (K s) (W s+16#64) (W s) (SP s) t
  src : t.gpr .r8=sb s 0
  dst : t.gpr .r11=Dst s
  mem : t.mem=bulkMem s u.mem
  rd : t.rd=u.rd
  wr : t.wr=u.wr

private theorem bulkWrites_wp {M : CtxMode} {s u : State} (h : Layout M s) (e : BulkTested M s u) (hc : 0<Cnt s) :
    WP isa (.block bulkWrites) u (Writes s u) := by
  have a := descriptor_input h e.toLoopAt hc
  obtain ⟨pr,ln⟩ := pre_le h hc
  have w (d : Nat) (hd : d+8≤2560) := e.env.perm.wW hd
  have r (d : Nat) (hd : d+8≤2560) := e.env.perm.wR hd
  let p := BitVec.ofNat 64 (preBytes s)
  let m1 := slot u.mem (W s) 264 p
  let m2 := slot m1 (W s) 200 (Dst s+p)
  have m1src : m1.readW (dp s 0) 64=sb s 0 := by
    refine (Mem.readW_writeW_sep ?_ (by decide)).trans a.source
    have ds : (⟨dp s 0,8⟩ : Region).Sub (dsR s) := by
      simpa [dp] using (Region.sub_prefix (base:=Src s) (len:=8) (len':=Cnt s*16) (by omega))
    exact ((h.ds_w.sub_left ds).sub_right (Lay.wSub (d:=264) (n:=8) (by decide))).sep (Region.contains_self _ _) (Region.contains_self _ _)
  have d0 : u.mem.readW (W s+200#64) 64=Dst s := by simpa using e.data
  have l0 : u.mem.readW (W s+208#64) 64=BitVec.ofNat 64 (L s) := by simpa using e.len
  have p1 : m1.readW (W s+264#64) 64=p := Mem.readW_writeW_self64 ..
  have sep (m : Mem) (v : Addr) (i j : Nat) (apart : i+8≤j ∨ j+8≤i) (hi : i+8≤2560) (hj : j+8≤2560) :=
    slot_other m (W s) v i j apart hi hj
  have d1 := (sep u.mem p 200 264 (by decide) (by decide) (by decide)).trans d0
  have l2 := (sep m1 (Dst s+p) 208 200 (by decide) (by decide) (by decide)).trans
    ((sep u.mem p 208 264 (by decide) (by decide) (by decide)).trans l0)
  have p2 := (sep m1 (Dst s+p) 264 200 (by decide) (by decide) (by decide)).trans p1
  have hs := Split.shr8shl8 (a:=sl s 0) (BitVec.isLt _)
  have add : p+Dst s=Dst s+p := BitVec.add_comm ..
  have sub := ofNat_sub (Nat.le_trans pr ln) (show L s<2^64 from BitVec.isLt _)
  dsimp only [m1,m2,slot] at m1src d1 l2 p2
  have r200 := r 200 (by decide)
  have r208 := r 208 (by decide)
  have r264 := r 264 (by decide)
  have w264 := w 264 (by decide)
  have w200 := w 200 (by decide)
  have w208 := w 208 (by decide)
  have facts := e.env
  refine WP.of_runBlock ⟨_,by xrun [bulkWrites,load,store,e.rax,e.r10,facts.r15,
    hs,w264,w200,w208,r200,r208,r264,a.rp,BitVec.add_zero,m1src,d1,l2,p2,add,sub],?_⟩
  refine ⟨facts.keep ?_ rfl rfl,?_,?_,?_,rfl,rfl⟩
  · intro reg hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> simp [gpr_setReg,gpr_setFlags]
  · simpa [gpr_setReg] using m1src
  · simpa [gpr_setReg] using d1
  · change (((u.mem.writeW _ _).writeW _ _).writeW _ _)=_
    dsimp only [p,preBytes] at d1 l2 p2 add sub
    simp only [bulkMem,slot,preBytes,d1,add,l2,p2,sub]

private theorem bulkRegs_wp {M : CtxMode} {s u v : State} (e : BulkTested M s u) (w : Writes s u v) :
    WP isa (.block bulkRegs) v (Split.G₂ (K s) (W s) (SP s) (Dst s) (sb s 0) (R s) (preBytes s) (bulkState s u)) := by
  have cfg := w.env
  have read1 := cfg.perm.wR (show 264+8≤2560 by decide)
  have read2 := cfg.perm.wR (show 176+8≤2560 by decide)
  have same (m : Mem) (d : Nat) (v : Addr) : (slot m (W s) d v).readW (W s+BitVec.ofNat 64 d) 64=v :=
    Mem.readW_writeW_self64 ..
  have p3 : v.mem.readW (W s+264#64) 64=BitVec.ofNat 64 (preBytes s) := by
    rw [w.mem]; change (slot (slot (slot _ _ 264 _) _ 200 _) _ 208 _).readW _ 64=_
    rw [slot_other _ _ _ 264 208 (by decide) (by decide) (by decide),slot_other _ _ _ 264 200 (by decide) (by decide) (by decide)]
    exact same ..
  have rounds : v.mem.readW (W s+176#64) 64=BitVec.ofNat 64 (R s) := by
    rw [w.mem]; change (slot (slot (slot _ _ 264 _) _ 200 _) _ 208 _).readW _ 64=_
    rw [slot_other _ _ _ 176 208 (by decide) (by decide) (by decide),slot_other _ _ _ 176 200 (by decide) (by decide) (by decide),
        slot_other _ _ _ 176 264 (by decide) (by decide) (by decide)]
    exact e.rounds.1
  have sh := shr4 (preBytes s) (Nat.lt_of_le_of_lt (Nat.mul_div_le ..) (show sl s 0<2^64 from BitVec.isLt _))
  refine WP.of_runBlock ⟨_,by xrun [bulkRegs,load,ptr,cfg.r13,cfg.r14,cfg.r15,read1,read2,p3,rounds,sh],?_⟩
  refine ⟨cfg.keep ?_ rfl rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,w.mem,w.rd,w.wr⟩
  · intro reg hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl <;> simp [gpr_setReg,gpr_setFlags]
  all_goals first | rfl | simpa [gpr_setReg,gpr_setFlags] using w.src | simpa [gpr_setReg,gpr_setFlags] using w.dst

theorem bulkArgs_wp {M : CtxMode} {s u : State} (h : Layout M s) (e : BulkTested M s u) (hc : 0<Cnt s) :
    WP isa (.block bulkArgs) u (Split.G₂ (K s) (W s) (SP s) (Dst s) (sb s 0) (R s) (preBytes s) (bulkState s u)) :=
  WP.block_append (WP.mono (bulkWrites_wp h e hc) (fun _ w => bulkRegs_wp e w))


open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (blockAt ctxH ctxCiph ghashFrom zeros padLen)
open VG.Proof.Gcm (Absorbed Ctr)

private theorem bulk_far {M : CtxMode} {s : State} (h : Layout M s) (plen : preBytes s≤L s)
    {d n : Nat} (range : d+n≤32 ∨ (128≤d ∧ d+n≤448)) :
      ∀ r∈Split.callWr (W s) (Dst s) (preBytes s/16)++[below (SP s) 56],
      (⟨W s+BitVec.ofNat 64 d,n⟩ : Region).Disjoint r := by
  intro r hr
  have sub : (⟨W s+BitVec.ofNat 64 d,n⟩ : Region).Sub ⟨W s,2560⟩ := Lay.wSub (by omega)
  simp only [Split.callWr,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,Short.add_ofNat_ofNat] at hr
  rcases hr with (rfl|rfl|rfl|rfl)|rfl
  · exact Offset.disjoint _ (by omega) (by omega) (by decide)
  · exact Offset.disjoint _ (by omega) (by omega) (by decide)
  · exact (h.d_w.symm.sub_left sub).sub_right (Region.sub_prefix (by change preBytes s/16*16≤L s; omega))
  · exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)
  · exact ((h.b_w.sub_left (below_sub (by decide) (by decide))).symm).sub_left sub

private theorem bulk_text {M : CtxMode} {s u t : State} (h : Layout M s) (e : LoopAt M s 0 0 u) (hc : 0<Cnt s)
    (a : Split.Mid2 (K s) (W s) (SP s) (Dst s) (sb s 0) (R s) (preBytes s) (bulkState s u) t)
    (x : Frame (changed s) s.mem (bulkMem s u.mem)) :
    Ctr t.mem (Split.cbA (W s)) (W s+16#64+64#64) (ciph s) (icb s) (preBytes s) ∧
    bytesAt t.mem (Dst s) (preBytes s)=Spec.Gcm.gctr (ciph s) (icb s) (bytesAt s.mem (sb s 0) (preBytes s)) ∧
    Absorbed t.mem (Split.yA (W s)) (W s+16#64+32#64) (hk s)
      (ad s++zeros (padLen (ad s).length)++bytesAt t.mem (Dst s) (preBytes s)) := by
  let f := bulkMem_frame s u.mem
  have within := (pre_le h hc).1
  have mul : 16*(preBytes s/16)=preBytes s := by dsimp [preBytes]; omega
  have rounds : R s≤14 := by change (s.gpr .rsi).toNat≤14; omega_using [h.rounds]
  obtain ⟨hh0,hk0⟩ := h.ctx_framed x rounds
  have apart {d n : Nat} (hi : d+n≤192) : ∀ r∈[⟨W s+192#64,80⟩],(⟨W s+BitVec.ofNat 64 d,n⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    exact Offset.disjoint _ (.inl hi) (by omega) (by decide)
  have keys : Ctr u.mem (Split.cbA (W s)) (W s+16#64+64#64) (ciph s) (icb s) 0 := by
    simpa only [consumed,gl_zero,skip,ite_true,Nat.zero_add] using e.ctr
  have keys' := keys.congr (m':=bulkMem s u.mem)
    (by simp only [Split.cbA,Short.add_ofNat_ofNat]; exact blockAt_frame f (apart (by decide)))
    (by simp only [Short.add_ofNat_ofNat]; exact blockAt_frame f (apart (by decide)))
  have b := a.blocks
  change Spec.Gcm.blocksAt t.mem _ _=Spec.Gcm.ctr32 (ctxCiph (bulkMem s u.mem) _ _) _ _ at b
  rw [hk0] at b
  obtain ⟨out,ctr⟩ := Proof.Gcm.ctr_wholeTo keys' rfl b a.ctr
  rw [mul] at out ctr
  have src := bytesAt_frame (p:=sb s 0) (n:=preBytes s) x
    (fun r hr => (h.slice_apart hc r hr).sub_left (Region.sub_prefix within))
    (Nat.le_of_lt (Nat.lt_of_le_of_lt within (BitVec.isLt _)))
  rw [src] at out
  have auth : Absorbed u.mem (Split.yA (W s)) (W s+16#64+32#64) (hk s)
      (ad s++zeros (padLen (ad s).length)) := by
    simpa only [bytesAt,List.range_zero,List.map_nil,List.append_nil] using e.auth
  have hash := a.y
  change blockAt t.mem _=ghashFrom (ctxH (bulkMem s u.mem) _) (blockAt (bulkMem s u.mem) _) _ at hash
  rw [hh0,Proof.Gcm.blocksAt_eq,mul] at hash
  have y0 : blockAt (bulkMem s u.mem) (Split.yA (W s))=blockAt u.mem (Split.yA (W s)) := by
    simp only [Split.yA,Short.add_ofNat_ofNat]; exact blockAt_frame f (apart (by decide))
  rw [y0] at hash
  have complete := Proof.Gcm.absorb_whole (d:=bytesAt t.mem (Dst s) (preBytes s)) auth (by rw [List.length_append,Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _)
    (by rw [Proof.Cmac.bytesAt_length]; dsimp [preBytes]; omega) hash
  exact ⟨by simpa only [Nat.zero_add] using ctr, by rwa [Proof.Gcm.gctr_eq], complete⟩

theorem bulk_done {M : CtxMode} {s u t : State} (h : Layout M s) (e : LoopAt M s 0 0 u) (hc : 0<Cnt s)
    (a : Split.Mid2 (K s) (W s) (SP s) (Dst s) (sb s 0) (R s) (preBytes s) (bulkState s u) t) :
    LoopAt M s (preBytes s) 0 t := by
  let f := bulkMem_frame s u.mem
  obtain ⟨within,bound⟩ := pre_le h hc
  have plen := Nat.le_trans within bound
  have mul : 16*(preBytes s/16)=preBytes s := by dsimp [preBytes]; omega
  have apart {d n : Nat} (hi : d+n≤192) : ∀ r∈[⟨W s+192#64,80⟩],(⟨W s+BitVec.ofNat 64 d,n⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    exact Offset.disjoint _ (.inl hi) (by omega) (by decide)
  have x : Frame (changed s) s.mem (bulkMem s u.mem) := e.frame.trans (f.sub (fun r hr => by
    simp only [List.mem_singleton] at hr; subst r
    exact ⟨_,List.mem_cons_self ..,Lay.wSub (by decide)⟩))
  have y : Frame (changed s) s.mem t.mem := x.trans (a.frame.sub (fun r hr => by
    have w : (⟨W s,2560⟩ : Region) ∈ changed s := List.mem_cons_self ..
    simp only [Split.callWr,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with (rfl|rfl|rfl|rfl)|rfl
    · exact ⟨_,w,fun a x => Split.st_w a (Split.cb_sub a x)⟩
    · exact ⟨_,w,fun a x => Split.st_w a (Split.y_sub a x)⟩
    · exact ⟨dR s,by simp [changed],Region.sub_prefix (by omega)⟩
    · exact ⟨_,w,Split.sc_w⟩
    · exact ⟨_,by simp [changed],fun _ hit => hit⟩))
  obtain ⟨ctr,out,complete⟩ := bulk_text h e hc a x
  obtain ⟨hh,key⟩ := h.ctx_framed y (R:=R s) (by change (s.gpr .rsi).toNat≤14; omega_using [h.rounds])
  have reg (i : Nat) (lo : 128≤i) (hi : i+8≤448) := a.frame.readW (Region.contains_self (W s+BitVec.ofNat 64 i) 8)
    (bulk_far h plen (.inr ⟨lo,hi⟩)) (by decide : 64/8<2^64)
  have slt (i : Nat) (lo : i+8≤200 ∨ 216≤i) (hi : i+8≤264 ∨ 272≤i) (end' : i+8≤448) :
      (bulkState s u).mem.readW (W s+BitVec.ofNat 64 i) 64=u.mem.readW (W s+BitVec.ofNat 64 i) 64 := by
    change ((slot (slot (slot _ _ 264 _) _ 200 _) _ 208 _).readW _ 64)=_
    rw [slot_other _ _ _ i 208 (by omega) (by omega) (by decide),
        slot_other _ _ _ i 200 (by omega) (by omega) (by decide),slot_other _ _ _ i 264 hi (by omega) (by decide)]
  have pass (i : Nat) (start : 128≤i) (lo : i+8≤200 ∨ 216≤i) (hi : i+8≤264 ∨ 272≤i) (end' : i+8≤448) :=
    (reg i start end').trans (slt i lo hi end')
  have same (m : Mem) (d : Nat) (v : Addr) : (slot m (W s) d v).readW (W s+BitVec.ofNat 64 d) 64=v :=
    Mem.readW_writeW_self64 ..
  refine ⟨a.env,a.rd.trans e.rd,a.wr.trans e.wr,(e.saved.frame f (apart (by decide))).frame a.frame (bulk_far h plen (.inr ⟨by decide,by decide⟩)),
    y,plen,fun _ => within,fun no => by omega,by dsimp [preBytes]; omega,(pass 256 (by decide) (by decide) (by decide) (by decide)).trans e.desc,
    (pass 224 (by decide) (by decide) (by decide) (by decide)).trans e.num,?_,?_,?_,?_,
    (pass 192 (by decide) (by decide) (by decide) (by decide)).trans e.total,
    (pass 184 (by decide) (by decide) (by decide) (by decide)).trans e.aad,
    ⟨(pass 176 (by decide) (by decide) (by decide) (by decide)).trans e.rounds.1,e.rounds.2⟩,key,hh,
    (blockAt_frame a.frame (bulk_far h plen (d:=16) (n:=16) (.inl (by decide)))).trans ((blockAt_frame f (apart (by decide))).trans e.j0),
    complete,?_,?_⟩
  · simpa only [consumed,skip,ite_true,gl_zero,Nat.zero_add,Nat.sub_self] using
      (pass 240 (by decide) (by decide) (by decide) (by decide)).trans e.span
  · rw [reg 264 (by decide) (by decide)]
    change (slot (slot (slot _ _ 264 _) _ 200 _) _ 208 _).readW _ 64=_
    rw [slot_other _ _ _ 264 208 (by decide) (by decide) (by decide),slot_other _ _ _ 264 200 (by decide) (by decide) (by decide)]
    exact same ..
  · rw [reg 200 (by decide) (by decide)]
    change (slot (slot _ _ 200 _) _ 208 _).readW _ 64=_
    rw [slot_other _ _ _ 200 208 (by decide) (by decide) (by decide)]
    exact same ..
  · rw [reg 208 (by decide) (by decide)]
    exact same ..
  · simpa only [consumed,skip,ite_true,gl_zero,Nat.zero_add] using ctr
  · simpa only [consumed,skip,plainPrefix,ite_true,gl_zero,Nat.zero_add] using out



theorem bulk_wp {M : CtxMode} (T : BlocksTo.SealFn M) {s u : State} (h : Layout M s) (e : LoopAt M s 0 0 u) (hc : 0<Cnt s) :
    WP isa (bulk T.fn) u (LoopAt M s (preBytes s) 0) := by
  refine WP.seq (WP.mono (bulkTest_wp h e hc) fun z p => ?_)
  refine WP.ite (decide (sl s 0/256=0)) (by simp only [eval,p.zero]) (fun yes => ?_) (fun _ => ?_)
  · have zero := of_decide_eq_true yes
    exact WP.block_nil (by simpa only [preBytes,zero,Nat.mul_zero] using p.toLoopAt)
  · refine WP.seq (WP.mono (bulkArgs_wp h p hc) fun v g => ?_)
    exact WP.mono (Split.Compact.mid2_call_wp (bulk_regs h p.toLoopAt hc) T g) fun t m => bulk_done h p.toLoopAt hc m

end VG.Proof.AesGcm.X86_64.DirectGather
end

/-! The direct fused prefix touches addresses determined by the public descriptor and length. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.DirectGather
open VG VG.X86_64 VG.X86_64.RegUpd Gather VG.Impl.AesGcm.X86_64
open VG.Impl.AesGcm.X86_64.DirectGather
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

private theorem ld_ptr {u : State} (hr : InRegions (u.rd++u.wr) (u.gpr .r15+256#64) 8) :
    WP isa (.block [load .r10 rO]) u (LdF .r10 .r15 256 u) := by
  refine WP.of_runBlock ⟨u.setReg .r10 (u.mem.readW (u.gpr .r15+256#64) 64),by xrun [load,hr],?_,?_,rfl,rfl,rfl⟩
  · simp [gpr_setReg]
  · intro r ne; simp [gpr_setReg,ne]

private theorem test_rel {M : CtxMode} {s t : State} (pub : Pub s t) :
    RelCT isa (fun u z => LoopAt M s 0 0 u ∧ LoopAt M t 0 0 z) (.block bulkTest) fun _ _ => True := by
  have eq₁ : ∀ u z, LoopAt M s 0 0 u ∧ LoopAt M t 0 0 z → ∀ r∈[Reg.r15],u.gpr r=z.gpr r := by
    rintro u z ⟨a,b⟩ r hr; rw [List.mem_singleton.mp hr,a.env.r15,b.env.r15,pub.w]
  refine Gather.rel_ld (l:=bulkTest.tail) (LdF .r10 .r15 256) ?_ ?_ ?_
  · rintro u z ⟨a,b⟩
    exact ⟨ld_ptr (a.env.r15 ▸ a.env.perm.wR (show 256+8≤2560 by decide)),
      ld_ptr (b.env.r15 ▸ b.env.perm.wR (show 256+8≤2560 by decide))⟩
  · exact rel_taint [.r15] eq₁ ⟨_,by taint_decide⟩
  · refine rel_taint [.r10,.r15] (Gather.ld_agree eq₁ ?_) ⟨_,by taint_decide⟩
    rintro u z ⟨a,b⟩; rw [a.env.r15,b.env.r15,a.desc,b.desc,pub.src]

theorem bulk_rel {M : CtxMode} (T : BlocksTo.SealFn M) {s t : State} (h : Layout M s) (j : Layout M t) (pub : Pub s t)
    (n : 0<Cnt s) : RelCT isa (fun u z => LoopAt M s 0 0 u ∧ LoopAt M t 0 0 z) (bulk T.fn) fun _ _ => True := by
  have nt : 0<Cnt t := pub.cnt ▸ n
  have len := pub.sl n
  refine RelCT.seq ((test_rel pub).wp (F₁:=BulkTested M s) (F₂:=BulkTested M t)
    (fun _ _ g => ⟨bulkTest_wp h g.1 n,bulkTest_wp j g.2 nt⟩)) ?_
  refine RelCT.ite (fun _ _ g => by simp only [eval,g.2.1.zero,g.2.2.zero,len]) ?_ ?_
  · exact StreamTo.skip_rel (fun _ _ _ => trivial)
  · intro u z tr tz u' z' hyp ex ez
    have pu := hyp.1.2.1
    have pz := hyp.1.2.2
    let c := bulkState s u
    let d := bulkState t z
    have args := rel_taint (c:=.block bulkArgs) (P:=fun x y => x=u ∧ y=z) [.r10,.r14,.r15] (by
      rintro x y ⟨rfl,rfl⟩ r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl
      · rw [pu.r10,pz.r10,dp,dp,pub.src]
      · rw [pu.env.r14,pz.env.r14,pub.w]
      · rw [pu.env.r15,pz.env.r15,pub.w]) ⟨_,by taint_decide⟩
    have reg := bulk_regs j pz.toLoopAt nt
    change Split.CallRegions M (K t) (W t) (SP t) (Dst t) (sb t 0) (R t) (L t) (preBytes t) d at reg
    simp only [K,SP,R,preBytes,pub.rdi,pub.rsp,pub.rsi,pub.w,pub.dst,pub.sb n,pub.eL,len] at reg
    have call := Split.Compact.call_rel (bulk_regs h pu.toLoopAt n) reg T
    apply RelCT.seq (args.wp (F₁:=Split.G₂ (K s) (W s) (SP s) (Dst s) (sb s 0) (R s) (preBytes s) c)
      (F₂:=Split.G₂ (K s) (W s) (SP s) (Dst s) (sb s 0) (R s) (preBytes s) d) (by
        rintro x y ⟨rfl,rfl⟩; refine ⟨bulkArgs_wp h pu n,?_⟩
        have g := bulkArgs_wp j pz nt
        simpa only [K,SP,R,preBytes,pub.rdi,pub.rsp,pub.rsi,pub.w,pub.dst,pub.sb n,pub.eL,len] using g))
      (call.mono (fun _ _ g => g.2) (fun _ _ _ => trivial)) u z tr tz u' z' ⟨rfl,rfl⟩ ex ez

/-- The fused call implements the optional prefix of the general gather loop. -/
theorem bulkPrefix_wp {M : CtxMode} (b : BlocksTo.SealFn M) : PrefixWP M (some b.fn) := by
  intro s u h e hn
  simpa [prefixBytes,prefixProgram,Nat.ne_of_gt hn] using bulk_wp b h e hn

theorem bulkPrefix_rel {M : CtxMode} (b : BlocksTo.SealFn M) : PrefixCT M (some b.fn) := by
  intro s t x y h k pub a z hc
  exact (bulk_rel b h k pub hc).mono (by rintro _ _ ⟨rfl,rfl⟩; exact ⟨a,z⟩) (fun _ _ w => w)

end VG.Proof.AesGcm.X86_64.DirectGather
end
