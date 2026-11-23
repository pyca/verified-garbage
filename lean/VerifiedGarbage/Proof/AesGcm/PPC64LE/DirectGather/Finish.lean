module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.DirectGather.Loop
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.FinTag
import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneShot
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamCrypt
public import VerifiedGarbage.Proof.Gcm.SealGather
import VerifiedGarbage.Proof.Gcm.StreamTo
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # Authenticating the remaining ciphertext and producing the full tag -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.DirectGather
open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ctxH fullTag j0 ghashFrom zeros padLen)
open VG.Proof.Gcm (Absorbed padA)

abbrev finishPrep : List Instr := [.load .d .r11 .r31 112,.add .r24 .r27 .r11,.sub .r25 .r23 .r11,.li .r26 0]
abbrev padPrep : List Instr := [.li .r0 15,.logic .and .r26 .r23 .r0]
abbrev tagLengths : List Instr := [mov .r24 .r22,mov .r26 .r23]
abbrev padTag : Prog isa := .seq (.block padPrep) (.seq (flush 16) (.seq (.block tagLengths) (tag 0)))

theorem padded_whole (ad ct : List Byte) :
    padA ad++ct++zeros (padLen (padA ad++ct).length)=Proof.Gcm.padded ad ct := by
  by_cases hc : ct=[]
  · subst ct
    simp only [List.append_nil,Proof.Gcm.padLen_of_mod (Proof.Gcm.length_padA_mod ad)]
    simp only [zeros,List.replicate_zero,List.append_nil]; rfl
  · rw [Proof.Gcm.padded,Proof.Gcm.ghashInput_of_ne hc]

variable {V : Reg → Addr} {sp : Addr} {s : State}

theorem padPrep_wp (env : Env V sp s) : WP isa (.block padPrep) s fun t =>
    t.gpr .r26=BitVec.ofNat 64 ((V .r23).toNat%16) ∧ Env V sp t ∧ Keeps s t := by
  have h23 := env.fr .r23 (by decide)
  crun [padPrep,h23,and15]
  exact ⟨env.keep (fun r hr => by
    have h1 : r≠.r26 := by revert r; decide
    have h2 : r≠.r0 := by revert r; decide
    simp [h1,h2]) rfl rfl rfl,⟨rfl,rfl,rfl,rfl,rfl⟩⟩

theorem tagLengths_wp (env : Env V sp s) : WP isa (.block tagLengths) s fun t =>
    t.gpr .r24=V .r22 ∧ t.gpr .r26=V .r23 ∧ Env V sp t ∧ Keeps s t := by
  have h22 := env.fr .r22 (by decide)
  have h23 := env.fr .r23 (by decide)
  crun [tagLengths,mov,BitVec.or_self,h22,h23]
  exact ⟨env.keep (fun r hr => by
    have h1 : r≠.r24 := by revert r; decide
    have h2 : r≠.r26 := by revert r; decide
    simp [h1,h2]) rfl rfl rfl,⟨rfl,rfl,rfl,rfl,rfl⟩⟩

theorem padTag_wp [Proof.Gcm.PPC64LE.GhashLaw] {R : Nat} {H : Block} {iv ad ct : List Byte}
    (L : Lay (V .r29) (V .r30) (V .r31)) (env : Env V sp s) (h28 : V .r28=BitVec.ofNat 64 R)
    (rounds : R=10 ∨ R=12 ∨ R=14) (ha : (V .r22).toNat=ad.length) (hc : (V .r23).toNat=ct.length)
    (key : blockAt s.mem (V .r29+240)=H) (j : blockAt s.mem (V .r30)=j0 H iv)
    (absorbed : Absorbed s.mem (V .r30+16) (V .r30+32) H (padA ad++ct)) :
    WP isa padTag s fun t => Env V sp t ∧
      bytesAt t.mem (V .r31) 16=fullTag (ciphOf s.mem (V .r29) R) H iv ad ct ∧
      Frame (tagFrame (V .r30) (V .r31) 0) s.mem t.mem := by
  have plen := Proof.Gcm.length_padA_mod ad
  have rem : (padA ad++ct).length%16=(V .r23).toNat%16 := by rw [List.length_append,hc]; omega_using [plen]
  refine WP.seq (WP.mono (padPrep_wp env) fun u ⟨r26,envu,ku⟩ => ?_)
  refine WP.seq (WP.mono (flush_ok L (yo:=16) (.inr rfl) (x:=padA ad++ct) (H:=H)
    ⟨envu,ku.mem ▸ key⟩ (by rwa [rem])) fun v fl => ?_)
  have fr := fl.frame
  rw [ku.mem] at fr
  have auth := fl.abs (ku.mem ▸ absorbed)
  rw [padded_whole] at auth
  have hash := auth.whole_eq (Proof.Gcm.length_padded ad ct)
  refine WP.seq (WP.mono (tagLengths_wp fl.env) fun z ⟨z24,z26,envz,kz⟩ => ?_)
  refine WP.mono (tag_ok L (o:=0) (.inl rfl) envz h28 rounds (H:=H) (kz.mem ▸ fl.hH)
    (J:=j0 H iv) (by rw [kz.mem,blockAt_frame fr (j_tFrame L),j])) fun t tag => ?_
  refine ⟨tag.env,?_,(t_tagFrame fr).trans (kz.mem ▸ tag.frame)⟩
  have out := tag.out
  rw [BitVec.add_zero,z24,z26,ha,hc,kz.mem,hash] at out
  rw [Proof.Gcm.fullTag_eq]
  rw [out,ciph_frame fr (fun r hr => by
    rcases List.mem_cons.mp hr with rfl|hr
    · exact L.cs.sub_right (Lay.stSub (by decide))
    · obtain rfl := List.mem_singleton.mp hr; exact L.cw'.sub_right (Lay.wSub (by decide))) rounds]

abbrev LoopArgs.finalV (a : LoopArgs) (e : State) :=
  cursors (a.regs a.count) (a.O+BitVec.ofNat 64 (a.pos e a.count))

variable {a : LoopArgs} {e : State} {b : Nat}

theorem finishPrep_wp (h : LoopInput a e) (p : LoopAt a e a.count b s)
    (text : (a.V .r23).toNat=a.pos e a.count) : WP isa (.block finishPrep) s fun t =>
    t.gpr .r24=a.O+BitVec.ofNat 64 (16*b) ∧ t.gpr .r25=BitVec.ofNat 64 (a.pos e a.count-16*b) ∧
    t.gpr .r26=0 ∧ Env (a.finalV e) a.sp t ∧ Keeps s t := by
  have ptr := p.env.r31.trans h.work
  have addr : s.gpr .r31+BitVec.ofNat 64 112=a.sp+240 := by rw [ptr,BitVec.add_assoc]; rfl
  have perm := p.env.perm.wR (d:=112) (n:=8) (by decide)
  have perm' : InRegions (s.rd++s.wr) (s.gpr .r31+BitVec.ofNat 64 112) 8 := by
    rw [p.env.r31]; exact perm
  have load := exec_load_d (s:=s) (t:=.r11) (by decide : Reg.r31 ≠ .r0) (by decide : 112<2^15 ∧ 112%4=0) perm'
  rw [addr,p.hashed] at load
  have dst : s.gpr .r27=a.O := p.env.fr _ (by decide)
  have n : s.gpr .r23=BitVec.ofNat 64 (a.pos e a.count) := by
    rw [←text,BitVec.ofNat_toNat,BitVec.setWidth_eq]; exact p.env.fr _ (by decide)
  have sub := Offset.ofNat_sub_ofNat (w:=64) p.hashLe
  refine WP.block_cons_iff.mpr ⟨_,load,?_⟩
  crun [State.write,dst,n,sub]
  exact ⟨p.env.keep (fun r hr => by
    have a : r≠.r11 := by revert r; decide
    have b : r≠.r24 := by revert r; decide
    have c : r≠.r25 := by revert r; decide
    have d : r≠.r26 := by revert r; decide
    simp [a,b,c,d]) rfl rfl rfl,⟨rfl,rfl,rfl,rfl,rfl⟩⟩

abbrev finishFrame (a : LoopArgs) := absFrame (a.V .r30) (a.V .r31) 16 ++ tagFrame (a.V .r30) (a.V .r31) 0

structure Finished (a : LoopArgs) (e s : State) (iv ad : List Byte) (t : State) : Prop where
  env : Env (a.finalV e) a.sp t
  tag : bytesAt t.mem (a.V .r31) 16 = fullTag (ciphOf e.mem a.C a.rounds) (ctxH e.mem a.C) iv ad
    (bytesAt s.mem a.O (a.pos e a.count))
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  frame : Frame (finishFrame a) s.mem t.mem

theorem finishData (h : LoopInput a e) (p : LoopAt a e a.count b s) :
    DataOk (a.V .r30) (a.V .r31) s a.O (a.pos e a.count) :=
  ⟨by rw [p.wr,p.rd]; exact (Covers.right h.dstWrite),h.totalFit,h.dstFit,
    by rw [h.state]; exact h.stackDst.symm.sub_right (Offset.sub_base _ (by decide : 144+80≤1280)),
    by rw [h.work]; exact h.stackDst.symm.sub_right (Offset.sub_base _ (by decide : 128+288≤1280))⟩

theorem loop_j (h : LoopInput a e) (p : LoopAt a e a.count b s) :
    blockAt s.mem (a.sp+144)=blockAt e.mem (a.sp+144) := by
  apply blockAt_frame p.frame
  intro r hr
  simp only [loopFrame,bulkAreas,callAreas,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  case inr.inr.inr.inr.inr.inl => exact h.stackDst.sub_left (Offset.sub_base _ (by decide : 144+16≤1280))
  all_goals exact Offset.disjoint _ (by decide) (by decide) (by decide)

theorem finish_wp [Proof.Gcm.PPC64LE.GhashLaw] {ad iv : List Byte}
    (h : LoopInput a e) (p : LoopAt a e a.count b s) (aad : (a.V .r22).toNat=ad.length)
    (text : (a.V .r23).toNat=a.pos e a.count) (j : blockAt e.mem (a.sp+144)=j0 (ctxH e.mem a.C) iv)
    (auth : Absorbed e.mem (a.sp+160) (a.sp+176) (ctxH e.mem a.C) (padA ad)) :
    WP isa Impl.AesGcm.PPC64LE.DirectGather.finish s (Finished a e s iv ad) := by
  let n := a.pos e a.count
  let k := 16*b
  let V := a.finalV e
  let H := ctxH e.mem a.C
  let ct := bytesAt s.mem a.O n
  let early := bytesAt s.mem a.O k
  let x := padA ad++early
  have pr : early.length%16=0 := by simp only [early,length_bytesAt,k]; omega
  have xmod : x.length%16=0 := by
    change ((padA ad)++early).length%16=0
    rw [List.length_append,Nat.add_mod,Proof.Gcm.length_padA_mod ad,pr]
  have yoff : V .r30+16=a.sp+160 := by change a.V .r30+16=_; rw [h.state,BitVec.add_assoc]; rfl
  have boff : V .r30+32=a.sp+176 := by change a.V .r30+32=_; rw [h.state,BitVec.add_assoc]; rfl
  have entryAbs : Absorbed s.mem (V .r30+16) (V .r30+32) H x := by
    rw [yoff,boff]
    apply Proof.Gcm.absorb_whole auth (Proof.Gcm.length_padA_mod ad) pr
    rw [p.hash,Proof.Gcm.blocksAt_eq]
  have hR : V .r28=BitVec.ofNat 64 a.rounds := by
    rw [←h.roundReg,BitVec.ofNat_toNat,BitVec.setWidth_eq]; rfl
  have hj : blockAt s.mem (V .r30)=j0 H iv := by change blockAt s.mem (a.V .r30)=_; rw [h.state,loop_j h p,j]
  have layout : Lay (V .r29) (V .r30) (V .r31) := h.layout
  refine WP.seq (WP.mono (finishPrep_wp h p text) fun u ⟨r24,r25,r26,env,ku⟩ => ?_)
  have key : blockAt u.mem (V .r29+240)=H := ku.mem ▸ p.keyH h
  have data : DataOk (V .r30) (V .r31) u (a.O+BitVec.ofNat 64 k) (n-k) :=
    ((finishData h p).drop p.hashLe).of_eq ku.rd ku.wr
  have ai : AbsIn V a.sp 16 H x (a.O+BitVec.ofNat 64 k) (n-k) u :=
    ⟨env,r24,r25,by rw [xmod]; exact r26,data,key⟩
  refine WP.seq (WP.mono (WP.with_rdwr (absorb_ok layout (.inr rfl) ai)) fun v ⟨ab,rv,wv,_⟩ => ?_)
  have fr := ab.frame
  rw [ku.mem] at fr
  have av := ab.abs (ku.mem ▸ entryAbs)
  have whole : x++bytesAt u.mem (a.O+BitVec.ofNat 64 k) (n-k)=padA ad++ct := by
    have kn : k+(n-k)=n := Nat.add_sub_of_le p.hashLe
    rw [ku.mem,show x=padA ad++bytesAt s.mem a.O k from rfl,List.append_assoc,←bytesAt_add,kn]
  rw [whole] at av
  have keyv := (blockAt_frame ab.frame (ctx_absFrame layout (.inr rfl))).trans key
  have jv : blockAt v.mem (V .r30)=j0 H iv := by
    rw [blockAt_frame fr (by simpa only [BitVec.add_zero] using stb_abs16 layout (d:=0) (.inl rfl)),hj]
  refine WP.mono (WP.with_rdwr (padTag_wp layout ab.env hR h.rounds aad
    (by exact text.trans (length_bytesAt _ _ _).symm) keyv jv av)) fun z ⟨⟨ez,tg,fz⟩,rz,wz,_⟩ => ?_
  have cipher : ciphOf v.mem (V .r29) a.rounds=ciphOf e.mem a.C a.rounds :=
    (ciph_frame (abs_taFrame fr) (ctx_taFrame layout) h.rounds).trans (p.cipher h)
  rw [cipher] at tg
  exact ⟨ez,tg,rz.trans (rv.trans ku.rd),wz.trans (wv.trans ku.wr),
    (fr.mono (fun _ hr => List.mem_append_left _ hr)).trans (fz.mono (fun _ hr => List.mem_append_right _ hr))⟩
end VG.Proof.AesGcm.PPC64LE.DirectGather
