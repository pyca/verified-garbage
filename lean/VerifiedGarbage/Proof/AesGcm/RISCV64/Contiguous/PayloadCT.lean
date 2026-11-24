module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.Payload
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.Timing
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTSeal
import VerifiedGarbage.Proof.AesGcm.RISCV64.CryptOk
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTAbsorb
import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.AesGcm.RISCV64.Contiguous
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.MaskPayload
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTSeal

/-! # Timing of the shared RISC-V seal payload -/

public section
namespace VG.Proof.AesGcm.RISCV64.Contiguous
open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Impl.AesGcm.RISCV64.Contiguous (masks maskTag)
open VG.Proof.Gather.RISCV64 (Eq2 TT rel_taint rel_seq)
open VG.Spec.Gcm (Block blockAt)

private theorem rel_env {V : Reg → BitVec 64} {sp : Addr} {s t : State} {p : Prog isa}
    (a : Env V sp s) (b : Env V sp t) (rs : List Reg) (hr : ∀ r ∈ rs, r ∈ frozen)
    {hint : VG.Taint.Hint taint.T} (cert : (taint.check (Taint.ofRegs rs) p hint).isSome=true) :
    RelCT isa (Eq2 s t) p TT := rel_taint rs (a.sp.trans b.sp.symm) (fun r h => (a.fr r (hr r h)).trans (b.fr r (hr r h)).symm) cert

private theorem lens_env [VG.Proof.Gcm.RISCV64.GhashLaw] {V : Reg → BitVec 64} {sp : Addr} {s : State}
    (L : Lay (V .s2) (V .s1) (V .s0)) (he : Env V sp s) :
    WP isa (.seq (.block [mov .s4 .s10,mov .s6 .s11]) (lens 16)) s (Env V sp) := by
  apply WP.seq
  refine Steps.wp_mv fun v a => Steps.wp_mv fun u b => WP.block_nil ?_
  have eu := he.keep (fun r hr => (b.other r (by revert r;decide)).trans (a.other r (by revert r;decide)))
    (b.sp.trans a.sp) (b.rd.trans a.rd) (b.wr.trans a.wr)
  exact WP.mono (lens_ok L (.inr rfl) eu rfl) fun _ h => h.1

theorem maskTag_rel [VG.Proof.Gcm.RISCV64.GhashLaw] {V : Reg → BitVec 64} {sp : Addr} {s t : State}
    (L : Lay (V .s2) (V .s1) (V .s0)) (a : Env V sp s) (b : Env V sp t) :
    RelCT isa (Eq2 s t) maskTag TT := by
  unfold maskTag
  apply RelCT.assoc
  refine rel_seq (rel_env a b [.s0,.s1,.s2,.s10,.s11] (by decide) (by taint_decide))
    (lens_env L a) (lens_env L b) fun _ _ x y => ?_
  exact rel_env x y [.s0,.s1] (by decide) (by taint_decide)

theorem maskData_rel {V : Reg → BitVec 64} {sp X D : Addr} {R : Nat} {ha hb : Block} {a b : List Byte} {s t : State}
    (L : Lay (V .s2) (V .s1) (V .s0)) (p : PayloadIn V sp X D R ha a s) (q : PayloadIn V sp X D R hb b t)
    (small : (V .s11).toNat≤240) : RelCT isa (Eq2 s t) (.seq masks shortXor) TT := by
  have prep {v : State} {H : Block} {aad : List Byte} (h : PayloadIn V sp X D R H aad v) :=
    masks_wp L h.env (n := (V .s11).toNat) (by simpa using h.len) small h.roundsReg h.rounds h.keys
  obtain ⟨_,cert⟩ : ∃ h, (taint.check (Taint.ofRegs [.s0,.s4,.s5,.s8]) shortXor h).isSome = true := ⟨_,by taint_decide⟩
  refine rel_seq (rel_taint [.s0,.s1,.s3,.s5,.s7] (p.env.sp.trans q.env.sp.symm) ?_ (by taint_decide)) (prep p) (prep q)
    fun u v ⟨eu,gu,_,_,_⟩ ⟨ev,gv,_,_,_⟩ => rel_taint [.s0,.s4,.s5,.s8] (eu.sp.trans ev.sp.symm) ?_ cert
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact p.env.s0.trans q.env.s0.symm
    · exact p.env.s1.trans q.env.s1.symm
    · exact p.env.s3.trans q.env.s3.symm
    · exact p.len.trans q.len.symm
    · exact (p.env.fr _ (by decide)).trans (q.env.fr _ (by decide)).symm
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact eu.s0.trans ev.s0.symm
    · rw [gu _ (by decide),gv _ (by decide),p.src,q.src]
    · rw [gu _ (by decide),gv _ (by decide),p.len,q.len]
    · rw [gu _ (by decide),gv _ (by decide),p.dst,q.dst]

private theorem afterAbsorb [VG.Proof.Gcm.RISCV64.GhashLaw] {V : Reg → BitVec 64} {sp : Addr} {s : State}
    (L : Lay (V .s2) (V .s1) (V .s0)) (he : Env V sp s) :
    WP isa (.seq (.block [.logicImm .and .s6 .s11 15]) (flush 16)) s (Env V sp) := by
  apply WP.seq
  refine Steps.wp_andi (by decide) fun t u => WP.block_nil ?_
  have et := he.keep (fun r hr => u.other r (by revert r;decide)) u.sp u.rd u.wr
  let x : List Byte := List.replicate (V .s11).toNat 0
  have reg : t.gpr .s6=BitVec.ofNat 64 (x.length%16) := by
    rw [u.gpr,he.fr _ (by decide),show BitVec.ofInt 64 15=BitVec.ofNat 64 15 from rfl,and15];simp [x]
  exact WP.mono (flush_ok L (.inr rfl) (H := blockAt t.mem (V .s2+BitVec.ofNat 64 240)) ⟨et,rfl⟩ reg) fun _ o => o.env

theorem authenticate_rel [VG.Proof.Gcm.RISCV64.GhashLaw] {V : Reg → BitVec 64} {sp D : Addr} {s t : State}
    (L : Lay (V .s2) (V .s1) (V .s0)) (a : Env V sp s) (b : Env V sp t)
    (ds : DataOk (V .s1) (V .s0) s D (V .s11).toNat) (dt : DataOk (V .s1) (V .s0) t D (V .s11).toNat)
    (slotS : s.mem.readW (V .s0+BitVec.ofNat 64 dataO) 64=D) (slotT : t.mem.readW (V .s0+BitVec.ofNat 64 dataO) 64=D) :
    RelCT isa (Eq2 s t) (.seq (.block dataArgs) (.seq (absorb 16) (.seq (.block [.logicImm .and .s6 .s11 15])
      (.seq (flush 16) maskTag)))) TT := by
  have args {v : State} (e : Env V sp v) (d : DataOk (V .s1) (V .s0) v D (V .s11).toNat)
      (sl : v.mem.readW (V .s0+BitVec.ofNat 64 dataO) 64=D) :
      WP isa (.block dataArgs) v (fun u => AbsIn V sp 16 (blockAt u.mem (V .s2+BitVec.ofNat 64 240)) [] D (V .s11).toNat u) := by
    refine WP.mono (dataArgs_ok e L.wal sl) fun u ⟨r4,r5,r6,g,k⟩ => ⟨?_,r4,r5,r6,d.of_eq k.rd k.wr k.sp,rfl⟩
    exact e.keep (fun r hr => g r (by revert r;decide) (by revert r;decide) (by revert r;decide)) k.sp k.rd k.wr
  refine rel_seq (rel_env a b [.s0] (by decide) (by taint_decide)) (args a ds slotS) (args b dt slotT) fun u v x y => ?_
  have pub : RelCT isa (Eq2 u v) (absorb 16) TT :=
    RelCT.mono (absorb_ct L (sp := sp) (yo := 16) (.inr rfl) (n := (V .s11).toNat) (q := 0) (D := D) (by decide))
      (fun _ _ e => by obtain ⟨rfl,rfl⟩ := e; exact ⟨⟨V,_,[],rfl,rfl,rfl,rfl,x⟩,⟨V,_,[],rfl,rfl,rfl,rfl,y⟩⟩) fun _ _ _ => trivial
  refine rel_seq pub (absorb_ok L (.inr rfl) x) (absorb_ok L (.inr rfl) y) fun _ _ f g => ?_
  apply RelCT.assoc
  refine rel_seq (rel_env f.env g.env [.s0,.s1,.s2,.s11] (by decide) (by taint_decide))
    (afterAbsorb L f.env) (afterAbsorb L g.env) fun _ _ e₁ e₂ => maskTag_rel L e₁ e₂

theorem shortPayload_rel [VG.Proof.Gcm.RISCV64.GhashLaw] {V : Reg → BitVec 64} {sp X D : Addr} {R : Nat} {ha hb : Block}
    {a b : List Byte} {s t : State} (L : Lay (V .s2) (V .s1) (V .s0))
    (p : PayloadIn V sp X D R ha a s) (q : PayloadIn V sp X D R hb b t) (small : (V .s11).toNat≤240) :
    RelCT isa (Eq2 s t) VG.Impl.AesGcm.RISCV64.Contiguous.shortPayload TT := by
  have run {v : State} {H : Block} {aad : List Byte} (h : PayloadIn V sp X D R H aad v) :=
    maskData_wp h.env L h.src h.dst (n := (V .s11).toNat) (by simpa using h.len) small h.read h.write h.buffers h.roundsReg h.rounds h.keys
  apply RelCT.assoc
  refine rel_seq (maskData_rel L p q small) (run p) (run q)
    fun u v ⟨eu,ku,fu,_,_⟩ ⟨ev,kv,fv,_,_⟩ => authenticate_rel L eu ev
      (p.write.ok.of_eq ku.rd ku.wr ku.sp) (q.write.ok.of_eq kv.rd kv.wr kv.sp)
      ((data_slot L p.write fu).trans p.slot) ((data_slot L q.write fv).trans q.slot)

private theorem longCtr_ct {c st w sp X D kb : Addr} {R n : Nat} (L : Lay c st w) :
    CT (CrMB true true kb c st w sp R X D n 0 0) (.seq (cryptWholeB true true) (cryptTailB true true)) := by
  apply CT.seq (J := CrMB true true kb c st w sp R X D n 0 (16*(n/16))) (cryptWholeB_ct L) ?_ (cryptTailB_ct L)
  intro s h
  obtain ⟨V,icb,P,m0,ctx,s1,s0,hP,mid,bk⟩ := h
  have lv := L.v ctx s1 s0
  refine WP.mono (WP.with_rdwr' (cryptWholeB_ok lv mid (mid.ciph lv) (fun h => (bk h).2))) fun t ⟨⟨j,eq,mt,_⟩,rd,wr⟩ => ?_
  have idx : j=16*(n/16) := by simpa using eq
  rw [idx] at mt
  exact ⟨V,icb,P,m0,ctx,s1,s0,hP,mt,fun h => ⟨(bk h).1,(bk h).2.of_eq rd wr⟩⟩

theorem longPayload_rel [VG.Proof.Gcm.RISCV64.GhashLaw] {V : Reg → BitVec 64} {sp X D A : Addr} {R : Nat}
    {ha hb : Block} {a b : List Byte} {s t : State} (L : Lay (V .s2) (V .s1) (V .s0))
    (p : PayloadIn V sp X D R ha a s) (q : PayloadIn V sp X D R hb b t)
    (st : V .s1=V .s0+BitVec.ofNat 64 16)
    (aS : DataOk (V .s1) (V .s0) s A (V .s10).toNat) (aT : DataOk (V .s1) (V .s0) t A (V .s10).toNat)
    (slotS : s.mem.readW (V .s0+BitVec.ofNat 64 aadO) 64=A) (slotT : t.mem.readW (V .s0+BitVec.ofNat 64 aadO) 64=A) :
    RelCT isa (Eq2 s t) VG.Impl.AesGcm.RISCV64.Contiguous.longPayload TT := by
  have ss {v : State} {H : Block} {aad : List Byte} (h : PayloadIn V sp X D R H aad v) :
      CrMB true true (V .s7) (V .s2) (V .s1) (V .s0) sp R X D (V .s11).toNat 0 0 v :=
    ⟨V,_,0,v.mem,rfl,rfl,rfl,rfl,h.start,fun _ => ⟨rfl,h.keys⟩⟩
  have rr : RelCT isa (Eq2 s t) (.seq (cryptWholeB true true) (cryptTailB true true)) TT :=
    RelCT.mono (longCtr_ct L) (fun _ _ e => by obtain ⟨rfl,rfl⟩ := e; exact ⟨ss p,ss q⟩) fun _ _ _ => trivial
  have lv : Lay (V .s2) (V .s0+BitVec.ofNat 64 16) (V .s0) := st ▸ L
  have state {v u : State} {H : Block} {aad : List Byte} (h : PayloadIn V sp X D R H aad v)
      (input : DataOk (V .s1) (V .s0) v A (V .s10).toNat) (slot : v.mem.readW (V .s0+BitVec.ofNat 64 aadO) 64=A)
      (out : CrOut true V sp R (VG.Spec.Gcm.inc32 (blockAt v.mem (V .s1))) 0 X D (V .s11).toNat v.mem u)
      (rd : u.rd=v.rd) (wr : u.wr=v.wr) :
      OneIK (V .s2) (V .s0) sp R (V .s7) A (V .s10) D (V .s11) u ∧
      (true=true → V .s7=V .s7 ∧ BkIn (V .s7) (V .s2) (V .s0+BitVec.ofNat 64 16) (V .s0) sp R u.mem X D (V .s11).toNat u) := by
    have hs := out.env.sp.trans h.env.sp.symm
    refine ⟨⟨V,rfl,st,rfl,h.roundsReg,rfl,rfl,rfl,out.env,st ▸ input.of_eq rd wr hs,st ▸ h.write.ok.of_eq rd wr hs,?_,?_⟩,fun _ => ⟨rfl,?_⟩⟩
    · exact (slot_keep out.frame (slot_crFrame L h.write (by decide))).trans slot
    · exact (slot_keep out.frame (slot_crFrame L h.write (by decide))).trans h.slot
    · rw [←st]
      exact h.keys.frame h.rounds out.frame h.keys.crFrame (ctx_crFrame L h.write) rd wr
  apply RelCT.assoc
  refine rel_seq rr (p.crypt L) (q.crypt L) fun u v ⟨ou,ru,wu⟩ ⟨ov,rv,wv⟩ => ?_
  exact RelCT.mono (oneTagB_ct lv (bs := true) (kb := V .s7) (S' := X) (D' := D) (n' := (V .s11).toNat)
    (.inl rfl) p.rounds) (fun _ _ e => by obtain ⟨rfl,rfl⟩ := e;exact ⟨state p aS slotS ou ru wu,state q aT slotT ov rv wv⟩)
    fun _ _ _ => trivial

theorem payload_rel [VG.Proof.Gcm.RISCV64.GhashLaw] {V : Reg → BitVec 64} {sp X D A : Addr} {R : Nat}
    {ha hb : Block} {a b : List Byte} {s t : State} (L : Lay (V .s2) (V .s1) (V .s0))
    (p : PayloadIn V sp X D R ha a s) (q : PayloadIn V sp X D R hb b t) (cs : s.gpr .t0=241) (ct : t.gpr .t0=241)
    (st : V .s1=V .s0+BitVec.ofNat 64 16)
    (aS : DataOk (V .s1) (V .s0) s A (V .s10).toNat) (aT : DataOk (V .s1) (V .s0) t A (V .s10).toNat)
    (slotS : s.mem.readW (V .s0+BitVec.ofNat 64 aadO) 64=A) (slotT : t.mem.readW (V .s0+BitVec.ofNat 64 aadO) 64=A) :
    RelCT isa (Eq2 s t) (.ite (.ltu .s5 .t0) VG.Impl.AesGcm.RISCV64.Contiguous.shortPayload
      VG.Impl.AesGcm.RISCV64.Contiguous.longPayload) TT := by
  have ev {v : State} (len : v.gpr .s5=V .s11) (cut : v.gpr .t0=241) :
      isa.eval (.ltu .s5 .t0) v=some (decide ((V .s11).toNat<241)) := by
    change some (decide (v.gpr .s5 < v.gpr .t0))=_
    rw [len,cut];rfl
  exact VG.Proof.Gather.RISCV64.rel_ite (ev p.len cs) (ev q.len ct)
    (fun small => shortPayload_rel L p q (by have := of_decide_eq_true small;omega))
    (fun _ => longPayload_rel L p q st aS aT slotS slotT)

end VG.Proof.AesGcm.RISCV64.Contiguous
