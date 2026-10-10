import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailSeed
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailInitial
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskBytes
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Unpack
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailOutput
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailHash
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentBytes
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailSaved

/-! ## From `CommitTailSponge.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sign.CommitTail

def spongeRegs : List Reg := [.x5,.x6,.x7,.x8,.x10,.x16]

theorem sponge_ok {s : State} {wlen : Nat} (hc : CoreConfig s wlen (s.gpr .x1) (s.gpr .x19))
    (hmu : ∀j<4,InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16)
    (hseed : ∀j<8,InRegions (s.rd++s.wr) (s.gpr .x4+BitVec.ofNat 64 (8*j)) 8) :
    WP isa (.seq (.block (first++upperInit++([.addImm .x .x5 .x1 72] : List Instr)))
      (coreFor wlen)) s fun t =>
      RegKeep spongeRegs s t ∧ Frame [bufferRegion (s.gpr .x19)] s.mem t.mem ∧
      Pairs t (lowRun wlen s.mem (s.gpr .x1) (firstState s.mem (s.gpr .x0) (s.gpr .x1))
        ((64+wlen)/136+1))
        (Optimized.Resident.permuted (seedNonceState s.mem (s.gpr .x4) (s.gpr .x5)) ((64+wlen)/136+1)) ∧
      Spec.Sha3.bytesAt t.mem (bufferBase (s.gpr .x19)) 640 =
        Spec.MlDsa.H (seedBytes s.mem (s.gpr .x4) (s.gpr .x5)) 640 := by
  have hw : 768≤wlen := by rcases hc.length with rfl|rfl <;> decide
  rw [WP.seq_iff]
  refine WP.mono (initial_ok hmu (fun j hj => hc.readable _ _ (by omega))
    (hc.readable 64 8 (by omega)) hseed) ?_
  intro a ⟨ha,hma,h5,hp⟩
  have hca : CoreConfig a wlen (s.gpr .x1) (s.gpr .x19) := by
    refine ⟨hc.length,ha.gpr .x19 (by decide),?_,?_,hc.separate⟩
    · intro d n hn; rw [ha.rd,ha.wr]; exact hc.readable d n hn
    · intro d n hn; rw [ha.wr]; exact hc.writable d n hn
  have hstart : CoreState a wlen (s.gpr .x1) (s.gpr .x19)
      (firstState s.mem (s.gpr .x0) (s.gpr .x1))
      (seedNonceState s.mem (s.gpr .x4) (s.gpr .x5)) 0 a := by
    refine ⟨⟨RegKeep.refl _ _,Frame.refl _ _,?_,fun _ hi => by omega⟩,hp⟩
    simp only [inputPtr,fullCount,Nat.zero_min,Nat.mul_zero,Nat.add_zero]
    exact h5
  refine WP.mono (core_ok hca hstart) fun t ht => ?_
  refine ⟨(ha.trans ht.keep).mono (by simp [coreRegs,spongeRegs]),?_,?_,?_⟩
  · simpa only [hma] using ht.frame
  · simpa only [hma] using ht.pairs
  · have ho := ht.output
    have hn : min ((64+wlen)/136+1) 5=5 := by rcases hc.length with rfl|rfl <;> decide
    rw [hn,seedNonceState_A0] at ho
    exact Optimized.ResidentMask.stream_mask_bytes (d:=20) (Or.inr rfl)
      (seedBytes_length _ _ _) ho

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailDecode.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Pack
open VG.Proof.MlDsa.AArch64.Pack VG.Proof.MlDsa.Pack
open VG.Proof.MlKem.AArch64 (Only Keep wp_movImm wp_nil)
open VG.Spec.MlDsa

def decodeRegs : List Reg := [.x0,.x4,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15]

theorem decodeWidth_ok {s a : State}
    (ha : Only [.x9,.x13] s a)
    (h13 : a.gpr .x13=BitVec.ofNat 64 q)
    (hin : (Region.mk (s.gpr .x0) 640) ∈ s.rd++s.wr)
    (hout : polyRegion (s.gpr .x4) ∈ s.wr)
    (hsep : (Region.mk (s.gpr .x0) 640).Disjoint (polyRegion (s.gpr .x4))) :
    WP isa (buWidth 524288 20 2 5) a fun t =>
      (∀i<256,coeffAt t.mem (s.gpr .x4) i=buWord 524288 (inNum s.mem (s.gpr .x0) 20 /2^(20*i)%2^20)) ∧
      Frame [polyRegion (s.gpr .x4)] s.mem t.mem ∧ Keep decodeRegs s t := by
  refine WP.seq ?_
  rw [← List.append_nil (Impl.MlKem.AArch64.movImm _ _)]
  refine wp_movImm fun b hb h12 => wp_nil ?_
  refine WP.mono (unpackLoop_ok (buFin_ok 524288 20)
    (show Shape 20 2 5 from ⟨by decide,by decide,rfl,by decide,by decide,rfl,rfl⟩)
    (v:=s.gpr .x0) (p:=s.gpr .x4) (s₀:=s) hin hout hsep
    (by rw [hb.get .x0,ha.get .x0]) (by rw [hb.get .x4,ha.get .x4]) h12
    (by rw [hb.get .x13,h13]) (hb.rd.trans ha.rd) (hb.wr.trans ha.wr) (hb.mem.trans ha.mem))
    fun t ⟨hv,hf,hk⟩ => ⟨hv,hf,((ha.keep.trans hb.keep).trans hk).mono⟩

theorem decode_ok {s : State} (h1 : s.gpr .x1=640)
    (hin : (Region.mk (s.gpr .x0) 640) ∈ s.rd++s.wr)
    (hout : polyRegion (s.gpr .x4) ∈ s.wr)
    (hsep : (Region.mk (s.gpr .x0) 640).Disjoint (polyRegion (s.gpr .x4))) :
    WP isa VG.Impl.MlDsa.AArch64.Pack.bitUnpack s fun t =>
      (∀i<256,coeffAt t.mem (s.gpr .x4) i=buWord 524288 (inNum s.mem (s.gpr .x0) 20 /2^(20*i)%2^20)) ∧
      Frame [polyRegion (s.gpr .x4)] s.mem t.mem ∧ Keep decodeRegs s t := by
  unfold VG.Impl.MlDsa.AArch64.Pack.bitUnpack
  refine WP.seq ?_
  rw [← List.append_nil (Impl.MlKem.AArch64.movImm _ _)]
  refine wp_movImm fun a ha h13 => wp_nil ?_
  refine sel_ok (by decide) (fun b hb h => ?_) (fun b hb _ => ?_)
  · rw [ha.get .x1,h1] at h; contradiction
  refine sel_ok (by decide) (fun c hc h => ?_) (fun c hc _ => ?_)
  · rw [hb.get .x1,ha.get .x1,h1] at h; contradiction
  refine sel_ok (by decide) (fun d hd h => ?_) (fun d hd _ => ?_)
  · rw [hc.get .x1,hb.get .x1,ha.get .x1,h1] at h; contradiction
  refine sel_ok (by decide) (fun e he h => ?_) (fun e he _ => ?_)
  · rw [hd.get .x1,hc.get .x1,hb.get .x1,ha.get .x1,h1] at h; contradiction
  exact decodeWidth_ok (((((ha.trans hb).trans hc).trans hd).trans he).mono (by decide))
    (by rw [he.get .x13,hd.get .x13,hc.get .x13,hb.get .x13,h13]; rfl) hin hout hsep


theorem decode_access_ok {s : State} (h1 : s.gpr .x1=640)
    (hin : InRegions (s.rd++s.wr) (s.gpr .x0) 640)
    (hout : InRegions s.wr (s.gpr .x4) 1024)
    (hsep : (Region.mk (s.gpr .x0) 640).Disjoint (polyRegion (s.gpr .x4))) :
    WP isa VG.Impl.MlDsa.AArch64.Pack.bitUnpack s fun t =>
      (∀i<256,coeffAt t.mem (s.gpr .x4) i=buWord 524288 (inNum s.mem (s.gpr .x0) 20 /2^(20*i)%2^20)) ∧
      Frame [polyRegion (s.gpr .x4)] s.mem t.mem ∧ Keep decodeRegs s t := by
  let a := s.withRegions [⟨s.gpr .x0,640⟩] [polyRegion (s.gpr .x4)]
  obtain ⟨tr,t,he,hv,hf,hk⟩ := decode_ok (s:=a) h1 (by simp [a]) (by simp [a]) hsep
  have hw := VG.AArch64.Exec.widen he (rd:=s.rd) (wr:=s.wr)
    (Covers.append_left (Covers.one hin) (Covers.right (Covers.one hout))) (Covers.one hout)
  change Exec isa _ s tr (t.withRegions s.rd s.wr) at hw
  exact ⟨tr,_,hw,hv,hf,⟨hk.gpr,rfl,rfl,hk.sp,hk.vcs⟩⟩


theorem decode_poly {m n : Mem} {a out : Addr}
    (hc : ∀i<256,coeffAt n out i=buWord 524288 (inNum m a 20 /2^(20*i)%2^20)) :
    PolyIs n out (toRq (bitUnpack (Spec.Sha3.bytesAt m a 640) 524287 524288)) := by
  refine polyIs_of_toNat fun i hi => ?_
  have hq : q=8380417 := rfl
  have hy := field_lt (inNum m a 20) 20 i (by decide)
  have hy' := hy
  unfold inNum at hy'
  rw [hc i hi,buWord,BitVec.toNat_setWidth,subModQ_toNat (by decide) (by omega),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (show 0<q by decide)) (by decide)),
    toRq,Vector.getElem_map,bitUnpack_get _ _ _ hi]
  change _=(ofInt ((524288:Nat) -
    ((VG.Proof.MlKem.digits 8 ((Spec.Sha3.bytesAt m a 640).map BitVec.toNat) /2^(20*i)%2^20 : Nat) : Int))).val
  rw [ofInt_sub (by omega)]

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailOutputBytes.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlDsa.AArch64.Optimized.Resident

theorem ratePairs_word {m : Mem} {a : Addr} {n : Nat} {A : Spec.Sha3.State}
    (h : RatePairs m a n A) {i : Nat} (hi : i<2*n) :
    m.readW (a+BitVec.ofNat 64 (8*i)) 64=A[i]! := by
  have hp := h (i/2) (by omega)
  have hv := congrArg (fun v => vdword v (i%2)) hp
  rw [vdword_read16 _ _ (by omega)] at hv
  rcases (show i%2=0 ∨ i%2=1 by omega) with hm|hm
  · rw [hm,vdword_ofVDwords_0] at hv
    simpa only [BitVec.add_assoc,BitVec.ofNat_add_ofNat,
      show 16*(i/2)+8*0=8*i by omega,show 2*(i/2)=i by omega] using hv
  · rw [hm,vdword_ofVDwords_1] at hv
    simpa only [BitVec.add_assoc,BitVec.ofNat_add_ofNat,
      show 16*(i/2)+8*1=8*i by omega,show 2*(i/2)+1=i by omega] using hv

theorem ratePairs_byte {m : Mem} {a : Addr} {n : Nat} {A : Spec.Sha3.State}
    (h : RatePairs m a n A) {j : Nat} (hj : j<16*n) :
    m (a+BitVec.ofNat 64 j)=Proof.Sha3.byteOf A j := by
  have hw := ratePairs_word h (i:=j/8) (by omega)
  have he := congrArg (fun v : BitVec 64 => v.extractLsb' (8*(j%8)) 8) hw
  change (m.read (a+BitVec.ofNat 64 (8*(j/8))) 8).extractLsb' (8*(j%8)) 8=_ at he
  rw [Mem.extractLsb'_read m _ (by omega)] at he
  rw [BitVec.add_assoc,← BitVec.ofNat_add,show 8*(j/8)+j%8=j by omega] at he
  exact he

theorem ratePairs_bytes {m : Mem} {a : Addr} {n : Nat} {A : Spec.Sha3.State}
    (h : RatePairs m a n A) (hn : n≤12) :
    Spec.Sha3.bytesAt m a (16*n)=(Spec.Sha3.toBytes A).take (16*n) := by
  apply List.ext_getElem
  · rw [Proof.Sha3.bytesAt_length,List.length_take,Proof.Sha3.length_toBytes]
    omega
  · intro j hj hj'
    rw [Proof.Sha3.bytesAt_length] at hj
    rw [Proof.MlKem.bytesAt_getElem,List.getElem_take,Proof.Sha3.toBytes_getElem _ (by omega)]
    exact ratePairs_byte h hj

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailParse.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (wp_movz)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Pack (polyRegion)

def parseRegs : List Reg := .x1::decodeRegs

theorem parse_ok {s : State}
    (hin : InRegions (s.rd++s.wr) (s.gpr .x0) 640)
    (hout : InRegions s.wr (s.gpr .x4) 1024)
    (hsep : (Region.mk (s.gpr .x0) 640).Disjoint (polyRegion (s.gpr .x4))) :
    WP isa (.seq (.block [.movz .x .x1 640 0]) Impl.MlDsa.AArch64.Pack.bitUnpack) s fun t =>
      RegKeep parseRegs s t ∧ Frame [polyRegion (s.gpr .x4)] s.mem t.mem ∧
      PolyIs t.mem (s.gpr .x4) (toRq (bitUnpack (Spec.Sha3.bytesAt s.mem (s.gpr .x0) 640) 524287 524288)) := by
  rw [WP.seq_iff]
  refine wp_movz fun a ha => WP.block_nil_iff.mpr ?_
  refine WP.mono (decode_access_ok (s:=a) ha.gpr
    (by rw [ha.rd,ha.wr,ha.other .x0 (by decide)]; exact hin)
    (by rw [ha.wr,ha.other .x4 (by decide)]; exact hout)
    (by rw [ha.other .x0 (by decide),ha.other .x4 (by decide)]; exact hsep))
    fun t ⟨hc,hf,hk⟩ => ?_
  simp only [ha.mem,ha.other .x0 (by decide),ha.other .x4 (by decide)] at hc hf
  refine ⟨?_,hf,decode_poly hc⟩
  have hb : RegKeep decodeRegs a t := ⟨hk.gpr,hk.rd,hk.wr,hk.sp⟩
  exact ((RegKeep.upd ha).trans hb).mono (by simp [parseRegs])

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailFront.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sign.CommitTail

def frontRegs : List Reg := [.x5,.x6,.x7,.x8,.x10,.x16,.x19,.x20,.x21]

structure FrontPre (wlen : Nat) (s : State) : Prop where
  length : wlen=768 ∨ wlen=1024
  mu : ∀d n,d+n≤64→InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 d) n
  packed : ∀d n,d+n≤wlen→InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 d) n
  seed : ∀d n,d+n≤64→InRegions (s.rd++s.wr) (s.gpr .x4+BitVec.ofNat 64 d) n
  work : ∀d n,d+n≤2048→InRegions s.wr (s.gpr .x3+BitVec.ofNat 64 d) n
  muSep : (Region.mk (s.gpr .x0) 64).Disjoint ⟨s.gpr .x3,2048⟩
  packedSep : (Region.mk (s.gpr .x1) wlen).Disjoint ⟨s.gpr .x3,2048⟩
  seedSep : (Region.mk (s.gpr .x4) 64).Disjoint ⟨s.gpr .x3,2048⟩

def FrontPost (wlen : Nat) (σ s : State) : Prop :=
  RegKeep frontRegs σ s ∧ Saved σ s.mem ∧ Frame [⟨σ.gpr .x3,2048⟩] σ.mem s.mem ∧
  s.gpr .x19=σ.gpr .x3 ∧ s.gpr .x20=σ.gpr .x6 ∧ s.gpr .x21=σ.gpr .x2 ∧
  ∃A B,Pairs s A B ∧
    (∀d,d≤136→(Spec.Sha3.toBytes A).take d=Spec.MlDsa.H
      (Spec.Sha3.bytesAt σ.mem (σ.gpr .x0) 64++Spec.Sha3.bytesAt σ.mem (σ.gpr .x1) wlen) d) ∧
    Spec.Sha3.bytesAt s.mem (bufferBase (σ.gpr .x3)) 640=
      Spec.MlDsa.H (seedBytes σ.mem (σ.gpr .x4) (σ.gpr .x5)) 640

theorem front_ok {s : State} {wlen : Nat} (hp : FrontPre wlen s) :
    WP isa (.seq (.block (pro++first++upperInit++([.addImm .x .x5 .x1 72] : List Instr)))
      (coreFor wlen)) s (FrontPost wlen s) := by
  rw [WP.seq_iff,List.append_assoc,List.append_assoc,WP.block_append_iff]
  refine WP.mono (pro_ok (fun i hi => hp.work _ _ (by omega))
    (fun i hi => hp.work _ _ (by omega))) fun a ⟨ha,hva,hsa,hfa,h19,h20,h21⟩ => ?_
  have hsub : (Region.mk (s.gpr .x3) 160).Sub ⟨s.gpr .x3,2048⟩ := by
    simpa using Offset.sub_base (s.gpr .x3) (d:=0) (n:=160) (k:=2048) (by decide)
  have hconfig : CoreConfig a wlen (a.gpr .x1) (a.gpr .x19) := by
    refine ⟨hp.length,rfl,?_,?_,?_⟩
    · intro d n hn; rw [ha.rd,ha.wr,ha.gpr .x1 (by decide)]; exact hp.packed d n hn
    · intro d n hn; rw [ha.wr,h19]; exact hp.work d n hn
    · rw [ha.gpr .x1 (by decide),h19]
      exact hp.packedSep.sub_right (Offset.sub_base _ (d:=256) (n:=680) (k:=2048) (by decide))
  rw [← WP.seq_iff,← List.append_assoc]
  refine WP.mono (sponge_ok hconfig (fun i hi => by
    rw [ha.rd,ha.wr,ha.gpr .x0 (by decide)]; exact hp.mu _ _ (by omega)) (fun i hi => by
    rw [ha.rd,ha.wr,ha.gpr .x4 (by decide)]; exact hp.seed _ _ (by omega)))
    fun t ⟨ht,hft,hpt,hbytes⟩ => ?_
  rw [h19] at hft hbytes
  have hmu : Spec.Sha3.bytesAt a.mem (s.gpr .x0) 64=Spec.Sha3.bytesAt s.mem (s.gpr .x0) 64 := by
    apply Proof.MlKem.bytesAt_frame hfa ?_ (by decide)
    intro r hr; rcases List.mem_singleton.mp hr with rfl
    exact hp.muSep.sub_right hsub
  have hpw : Spec.Sha3.bytesAt a.mem (s.gpr .x1) wlen=Spec.Sha3.bytesAt s.mem (s.gpr .x1) wlen := by
    apply Proof.MlKem.bytesAt_frame hfa ?_ (by rcases hp.length with rfl|rfl <;> decide)
    intro r hr; rcases List.mem_singleton.mp hr with rfl
    exact hp.packedSep.sub_right hsub
  have hseed : seedBytes a.mem (s.gpr .x4) (s.gpr .x5)=seedBytes s.mem (s.gpr .x4) (s.gpr .x5) := by
    have hb : Spec.Sha3.bytesAt a.mem (s.gpr .x4) 64=Spec.Sha3.bytesAt s.mem (s.gpr .x4) 64 :=
      Proof.MlKem.bytesAt_frame hfa (by
        intro r hr; rcases List.mem_singleton.mp hr with rfl
        exact hp.seedSep.sub_right hsub) (by decide)
    unfold seedBytes
    rw [hb]
  refine ⟨(ha.trans ht).mono (by simp [frontRegs,spongeRegs]),hsa.keep_core hft,?_,
    (ht.gpr .x19 (by decide)).trans h19,(ht.gpr .x20 (by decide)).trans h20,
    (ht.gpr .x21 (by decide)).trans h21,_,_,hpt,?_,?_⟩
  · apply Frame.trans
    · exact hfa.sub (by
        intro r hr
        rcases List.mem_singleton.mp hr with rfl
        exact ⟨_,by simp,hsub⟩)
    · exact hft.sub (by
        intro r hr
        rcases List.mem_singleton.mp hr with rfl
        exact ⟨_,by simp,Offset.sub_base _ (d:=256) (n:=680) (k:=2048) (by decide)⟩)
  · intro d hd
    rw [lowRun_hash a.mem (a.gpr .x0) (a.gpr .x1) hp.length hd,
      ha.gpr .x0 (by decide),ha.gpr .x1 (by decide),hmu,hpw]
  · rw [ha.gpr .x4 (by decide),ha.gpr .x5 (by decide),hseed] at hbytes
    exact hbytes

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailOutputStage.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (wp_mov WP.cons)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail
open VG.Impl.MlKem.AArch64 (mov)

def outputStage (olen : Nat) : List Instr :=
  [mov .x2 .x21]++output olen++[.addImm .x .x0 .x19 256,mov .x4 .x20]

theorem outputStage_ok {s : State} {A B : Spec.Sha3.State} {n : Nat}
    (hn : n≤12) (hp : Pairs s A B)
    (hout : ∀i<n,InRegions s.wr (s.gpr .x21+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block (outputStage (16*n))) s fun t =>
      RegKeep [.x0,.x2,.x4] s t ∧ Frame [⟨s.gpr .x21,16*n⟩] s.mem t.mem ∧
      t.gpr .x0=s.gpr .x19+256 ∧ t.gpr .x4=s.gpr .x20 ∧
      Spec.Sha3.bytesAt t.mem (s.gpr .x21) (16*n)=(Spec.Sha3.toBytes A).take (16*n) := by
  unfold outputStage
  rw [List.append_assoc,WP.block_append_iff]
  refine wp_mov fun a ha => WP.block_nil_iff.mpr ?_
  rw [WP.block_append_iff]
  refine WP.mono (output_ok (s:=a) (A:=A) (B:=B) (p:=s.gpr .x21) n hn (by intro i hi; rw [ha.vec]; exact hp i hi)
    ha.gpr (by intro i hi; rw [ha.wr]; exact hout i hi)) fun b ⟨hb,hpb,hbytes,hf⟩ => ?_
  have hfb : Frame [⟨s.gpr .x21,16*n⟩] s.mem b.mem := by simpa only [ha.mem] using hf
  refine WP.cons rfl (wp_mov fun t ht => WP.block_nil_iff.mpr ?_)
  refine ⟨?_,?_,?_,?_,?_⟩
  · refine ⟨fun r hr => ?_,ht.rd.trans hb.rd |>.trans ha.rd,
      ht.wr.trans hb.wr |>.trans ha.wr,ht.sp.trans hb.sp |>.trans ha.sp⟩
    have h4 : r≠.x4 := fun e => hr (by simp [e])
    have h0 : r≠.x0 := fun e => hr (by simp [e])
    rw [ht.other r h4,RegUpd.gpr_write,ite_eq_right h0,hb.gpr r (by simp),ha.other r (by
      intro e; apply hr; simp [e])]
  · rw [ht.mem]; exact hfb
  · rw [ht.other .x0 (by decide),RegUpd.gpr_write_self]
    change b.gpr .x19+256=s.gpr .x19+256
    rw [hb.gpr .x19 (by simp),ha.other .x19 (by decide)]
  · rw [ht.gpr,RegUpd.gpr_write,ite_eq_right (by decide : ¬ Reg.x20=Reg.x0),
      hb.gpr .x20 (by simp),ha.other .x20 (by decide)]
  · rw [ht.mem]
    exact ratePairs_bytes hbytes hn

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailBody.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlDsa.Pack (polyRegion)
open VG.Spec.MlDsa

structure Pre (wlen olen : Nat) (s : State) : Prop extends FrontPre wlen s where
  outLength : olen=48 ∨ olen=64
  output : ∀d n,d+n≤olen→InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 d) n
  cache : InRegions s.wr (s.gpr .x6) 1024
  readWork : ∀d n,d+n≤2048→InRegions (s.rd++s.wr) (s.gpr .x3+BitVec.ofNat 64 d) n
  outWork : (Region.mk (s.gpr .x2) olen).Disjoint ⟨s.gpr .x3,2048⟩
  cacheWork : (polyRegion (s.gpr .x6)).Disjoint ⟨s.gpr .x3,2048⟩
  outCache : (Region.mk (s.gpr .x2) olen).Disjoint (polyRegion (s.gpr .x6))

def bodyRegs : List Reg := [.x0,.x1,.x2,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x19,.x20,.x21]
def writes (s : State) (olen : Nat) : List Region :=
  [⟨s.gpr .x3,2048⟩,⟨s.gpr .x2,olen⟩,polyRegion (s.gpr .x6)]

def BodyPost (wlen olen : Nat) (σ s : State) : Prop :=
  RegKeep bodyRegs σ s ∧ Saved σ s.mem ∧ Frame (writes σ olen) σ.mem s.mem ∧ s.gpr .x19=σ.gpr .x3 ∧
  Spec.Sha3.bytesAt s.mem (σ.gpr .x2) olen=H
    (Spec.Sha3.bytesAt σ.mem (σ.gpr .x0) 64++Spec.Sha3.bytesAt σ.mem (σ.gpr .x1) wlen) olen ∧
  PolyIs s.mem (σ.gpr .x6) (toRq (bitUnpack (H (seedBytes σ.mem (σ.gpr .x4) (σ.gpr .x5)) 640) 524287 524288))

theorem body_ok {σ s : State} {wlen olen : Nat} (hp : Pre wlen olen σ) (hs : FrontPost wlen σ s) :
    WP isa (.seq (.block (outputStage olen))
      (.seq (.block [.movz .x .x1 640 0]) Impl.MlDsa.AArch64.Pack.bitUnpack)) s (BodyPost wlen olen σ) := by
  obtain ⟨hk,hsv,hf,h19,h20,h21,A,B,hpAB,hhash,hbytes⟩ := hs
  have hmul : 16*(olen/16)=olen := by rcases hp.outLength with rfl|rfl <;> decide
  have hn : olen/16≤12 := by rcases hp.outLength with rfl|rfl <;> decide
  rw [WP.seq_iff,← hmul]
  refine WP.mono (outputStage_ok hn hpAB (fun i hi => by
    rw [hk.wr,h21]; exact hp.output _ _ (by omega))) fun a ⟨ha,hfa,h0,h4,hout⟩ => ?_
  rw [hmul]
  rw [hmul,h21] at hfa hout
  rw [h19] at h0
  rw [h20] at h4
  have hasv : Saved σ a.mem := hsv.keep hfa (by
    intro r hr; rcases List.mem_singleton.mp hr with rfl
    exact hp.outWork.symm.sub_left (by
      simpa using Offset.sub_base (σ.gpr .x3) (d:=0) (n:=160) (k:=2048) (by decide)))
  have habytes : Spec.Sha3.bytesAt a.mem (bufferBase (σ.gpr .x3)) 640=
      H (seedBytes σ.mem (σ.gpr .x4) (σ.gpr .x5)) 640 := by
    rw [Proof.MlKem.bytesAt_frame hfa (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl
      exact hp.outWork.symm.sub_left (Offset.sub_base _ (d:=256) (n:=640) (k:=2048) (by decide))) (by decide)]
    exact hbytes
  have hahash := hhash olen (by rcases hp.outLength with rfl|rfl <;> decide)
  rw [hahash] at hout
  refine WP.mono (parse_ok (s:=a) (by
    rw [ha.rd,ha.wr,hk.rd,hk.wr,h0]; exact hp.readWork 256 640 (by decide)) (by
    rw [ha.wr,hk.wr,h4]; exact hp.cache) (by
    rw [h0,h4]
    exact hp.cacheWork.symm.sub_left (Offset.sub_base _ (d:=256) (n:=640) (k:=2048) (by decide))))
    fun t ⟨ht,hft,hpoly⟩ => ?_
  rw [h4] at hft hpoly
  change Spec.Sha3.bytesAt a.mem (σ.gpr .x3+256) 640=_ at habytes
  rw [h0,habytes] at hpoly
  refine ⟨((hk.trans ha).trans ht).mono (by simp [frontRegs,parseRegs,decodeRegs,bodyRegs]),?_,?_,?_,?_,hpoly⟩
  · exact hasv.keep hft (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl
      exact hp.cacheWork.symm.sub_left (by
        simpa using Offset.sub_base (σ.gpr .x3) (d:=0) (n:=160) (k:=2048) (by decide)))
  · apply Frame.trans (hf.sub (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl
      exact ⟨_,by simp [writes],fun _ hx => hx⟩))
    apply Frame.trans (hfa.sub (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl
      exact ⟨_,by simp [writes],fun _ hx => hx⟩))
    exact hft.sub (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl
      exact ⟨_,by simp [writes],fun _ hx => hx⟩)
  · exact (ht.gpr .x19 (by decide)).trans ((ha.gpr .x19 (by decide)).trans h19)
  · rw [Proof.MlKem.bytesAt_frame hft (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl
      exact hp.outCache) (by rcases hp.outLength with rfl|rfl <;> decide)]
    exact hout

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end
