module

public import VerifiedGarbage.Proof.AesGcm.X86.Open
public import VerifiedGarbage.Proof.AesGcm.X86.Contiguous.Entry
import VerifiedGarbage.Proof.AesGcm.X86.DirectGather.CryptCT
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Impl.AesGcm.X86
meta import VerifiedGarbage.Impl.AesGcm.X86.Contiguous
meta import VerifiedGarbage.TCB.X86.Isa
meta import VerifiedGarbage.TCB.X86.State
import VerifiedGarbage.Proof.AesGcm.X86.Loops
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! Encrypt contiguous IA-32 plaintext into the destination and authenticate that ciphertext. Both payload layouts share the proof and restore the caller’s registers. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86.Contiguous
open VG.Impl.AesGcm.X86.Contiguous (FrameSize privateFrameBytes workBytes scrubBytes)
variable [size : FrameSize]
open VG VG.X86 VG.Impl.AesGcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (blockAt ctxCiph ctxH inc32)
open DirectGather (PiecePost)

def destParams (p : BitVec 32 × (Nat → BitVec 32)) (T : BitVec 32) :
    BitVec 32 × (Nat → BitVec 32) := ⟨p.1,fun i => if i=6 then T else p.2 i⟩

abbrev cipherFrame (p : BitVec 32 × (Nat → BitVec 32)) (T : BitVec 32) :=
  crFrame workBytes (stOf (p.2 8)) (p.2 8) p.1 32 T (p.2 7).toNat

theorem ctrTagState {p} {T : BitVec 32} (G : OL workBytes p) (Q : OL workBytes (destParams p T)) (D : OLD (destParams p T))
    {ref s y : State} (h : OAad workBytes p ref s)
    (o : PiecePost workBytes s (p.2 0) (stOf (p.2 8)) (p.2 8) p.1 (p.2 6) T
      (ctxCiph ref.mem (w64 (p.2 0)) (p.2 1).toNat) (inc32 (jOf p ref)) 0 (p.2 7).toNat y) :
    OTIn workBytes p ref y := by
  have big := workBytes_big
  have f : Frame ((⟨w64 T,(p.2 7).toNat⟩ : Region)::oFF workBytes p) s.mem y.mem :=
    Frame.oDD (p:=destParams p T) (o.frame.sub (crFrame_oF Q))
  have e := h.o.env
  have env : OEnv workBytes p ref y := by
    refine h.o.frameG G (fun h₁ h₂ r hr => ?_) (fun r hr => ?_) (fun r hr => ?_) (fun r hr => ?_) f
      (o.env.ebp.trans e.ebp.symm) (o.env.esi.trans e.esi.symm) (o.env.esp.trans e.esp.symm) o.rd o.wr
    all_goals rcases List.mem_cons.mp hr with rfl|hr
    · exact (Q.d_w.sub_right (Lay.wSub (by simp only [auxO,rO] at h₂; omega_arith))).symm
    · exact slot_oF G h₁ h₂ r hr
    · exact D.c_d
    · exact ctx_oF G r hr
    · exact D.a_d
    · exact aad_oF G r hr
    · exact Q.r_d
    · exact ret_oF G r hr
  have jf := blockAt_frame o.frame (st_crFrameO Q (d:=0) (by decide))
  rw [BitVec.add_zero] at jf
  have hl : (xA p ref).length%16=0 := by
    simp only [xA,List.length_append,length_bytesAt,Proof.Gcm.length_zeros]
    exact Proof.Gcm.length_pad_mod _
  exact ⟨env,jf.trans h.j,h.y.congr (blockAt_frame o.frame (st_crFrameO Q (by decide))) (by rw [hl]; rfl)⟩

abbrev dataSlot (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 dataO,4⟩

theorem destinationTagState {p} {T : BitVec 32} (G : OL workBytes p) {ref y z : State}
    (h : OTIn workBytes p ref y) (write : Frame [dataSlot (p.2 8)] y.mem z.mem)
    (bp : z.gpr .ebp=y.gpr .ebp) (si : z.gpr .esi=y.gpr .esi) (sp : z.gpr .esp=y.gpr .esp)
    (rd : z.rd=y.rd) (wr : z.wr=y.wr) (data : slotv z.mem (p.2 8) dataO=T)
    (read : Covers [⟨w64 T,(p.2 7).toNat⟩] (z.rd++z.wr)) : OTIn workBytes (destParams p T) ref z := by
  have big := workBytes_big
  have sl {i : Nat} (apart : i+4≤dataO ∨ dataO+4≤i) (fit : i+4≤768) :
      slotv z.mem (p.2 8) i=slotv y.mem (p.2 8) i :=
    slot_frame write (fun r hr => List.mem_singleton.mp hr ▸ Lay.w_w apart fit (by decide))
  have wk {R : Region} (dis : R.Disjoint ⟨w64 (p.2 8),workBytes⟩) : ∀ r∈[dataSlot (p.2 8)], R.Disjoint r :=
    fun r hr => List.mem_singleton.mp hr ▸ dis.sub_right (Lay.wSub (by decide))
  have st {d : Nat} (hd : d+16≤48) : ∀ r∈[dataSlot (p.2 8)],
      (⟨w64 (stOf (p.2 8))+BitVec.ofNat 64 d,16⟩ : Region).Disjoint r := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    rw [st_eq G]
    exact Lay.w_w (.inl (by change 16+d+16≤168; omega_using [hd])) (by omega_using [hd]) (by decide)
  have o := h.o
  have en : OEnv workBytes (destParams p T) ref z := by
    refine ⟨o.env.keep bp si sp rd wr (sl (i:=ctxO) (by decide) (by decide)),
      ⟨(sl (by decide) (by decide)).trans o.rounds.1,o.rounds.2⟩,
      (sl (by decide) (by decide)).trans o.aadO,(sl (by decide) (by decide)).trans o.alO,data,
      (sl (by decide) (by decide)).trans o.lenO,(sl (by decide) (by decide)).trans o.zO,
      (sl (by decide) (by decide)).trans o.nlO,(sl (by decide) (by decide)).trans o.tp,
      o.saved.frame write (fun r hr => List.mem_singleton.mp hr ▸ Lay.w_w (.inl (by decide)) (by decide) (by decide)),
      (ret_kept write (wk G.r_w)).trans o.ret, (ciph_frame write (wk G.L.cw) G.rounds).trans o.ciph,?_,
      (bytesAt_frame write (wk G.a_w) (by omega_using [G.fa])).trans o.aad,rd.trans o.rd,wr.trans o.wr,?_,?_,read⟩
    · exact (blockAt_frame write (fun r hr => ((wk G.L.cw) r hr).sub_left (Lay.ctxSub (by decide)))).trans o.hk
    · rw [rd,wr]; exact o.nIn
    · rw [rd,wr]; exact o.aIn
  have jf := blockAt_frame write (st (d:=0) (by decide))
  rw [BitVec.add_zero] at jf
  have hl : (xA p ref).length%16=0 := by
    simp only [xA,List.length_append,length_bytesAt,Proof.Gcm.length_zeros]
    exact Proof.Gcm.length_pad_mod _
  exact ⟨en,jf.trans h.j,h.y.congr (blockAt_frame write (st (by decide))) (by rw [hl]; rfl)⟩

open VG.Impl.AesGcm.X86.Contiguous (callerSlot)

abbrev textWrites (p : BitVec 32 × (Nat → BitVec 32)) (T : BitVec 32) :=
  dataSlot (p.2 8)::cipherFrame p T

structure PayloadPre (p : BitVec 32 × (Nat → BitVec 32)) (caller T : BitVec 32) (b : State × State) (s : State) : Prop where
  aad : OAad workBytes p b.1 s
  access : DirectGather.PieceAccess s p.1 (p.2 6) T (p.2 7).toNat
  ptr : s.mem.readW (argA caller 7) 32=T
  readable : InRegions (s.rd++s.wr) (argA caller 7) 4
  entry : s=b.2

structure PayloadPost (p : BitVec 32 × (Nat → BitVec 32)) (T : BitVec 32) (b : State × State) (s : State) : Prop where
  tag : OTIn workBytes (destParams p T) b.1 s
  ct : bytesAt s.mem (w64 T) (p.2 7).toNat =
    Proof.Gcm.xorKs (ctxCiph b.1.mem (w64 (p.2 0)) (p.2 1).toNat) (inc32 (jOf p b.1)) 0
      (bytesAt b.2.mem (w64 (p.2 6)) (p.2 7).toNat)
  frame : Frame (textWrites p T) b.2.mem s.mem

private theorem destinationSlotTaint :
    ∃ h, (VG.X86.taint.check (τr [.esp,.ebp]) (.block (keep (callerSlot 7) dataO)) h).isSome = true := by
  cases size with | mk b => cases b <;> exact ⟨_, by taint_decide⟩

theorem payload_pc (v : GcmImpl) [WSize workBytes v.ctr.scr] (p : BitVec 32 × (Nat → BitVec 32)) (caller T : BitVec 32)
    (sp : p.1=caller-(BitVec.ofNat 32 privateFrameBytes)) (G : OL workBytes p) (Q : OL workBytes (destParams p T)) (D : OLD (destParams p T))
    (P : DirectGather.PieceRegions workBytes (p.2 0) (p.2 8) p.1 (p.2 6) T (p.2 7).toNat)
    (apart : ∀ r∈cipherFrame p T, (⟨argA caller 7,4⟩ : Region).Disjoint r) :
    Pc (PayloadPre p caller T)
      (.seq (Open.decTo v.callees v.callees.ctr true) (.block (keep (callerSlot 7) dataO))) (PayloadPost p T) := by
  have big := workBytes_big
  let done (b : State × State) (y : State) :=
    PayloadPre p caller T b b.2 ∧
    PiecePost workBytes b.2 (p.2 0) (stOf (p.2 8)) (p.2 8) p.1 (p.2 6) T
      (ctxCiph b.1.mem (w64 (p.2 0)) (p.2 1).toNat) (inc32 (jOf p b.1)) 0 (p.2 7).toNat y
  refine Pc.seq (Q:=done) ⟨?_,?_⟩ ?_
  · intro b s h
    have len := h.aad.o.lenO.trans (ofNat_toNat32 _).symm
    have result := DirectGather.decTo_ok G.L rfl P v h.aad.o.env h.access h.aad.o.rounds h.aad.o.dataO
      len (p.2 7).isLt (fun _ => rfl) h.aad.o.ciph (Proof.Gcm.ctr_zero _ _ _ _ h.aad.cb) true
    refine result.mono fun y hy => ?_
    dsimp only [done]
    rw [←h.entry]
    exact ⟨h,hy⟩
  · apply (DirectGather.decTo_ct v G.L rfl P (p.2 7).isLt (off:=0) (fun _ => rfl) true).mono
    rintro s ⟨b,h⟩
    refine ⟨⟨h.aad.o.env,h.access,h.aad.o.rounds,h.aad.o.dataO,?_⟩,inc32 (jOf p b.1),?_⟩
    · rw [ofNat_toNat32]; exact h.aad.o.lenO
    · rw [h.aad.o.ciph]; exact Proof.Gcm.ctr_zero _ _ _ _ h.aad.cb
  obtain ⟨hint, valid⟩ := destinationSlotTaint (size:=size)
  refine Pc.taint [.esp,.ebp] ?_ (fun _ _ s t ⟨_,hs⟩ ⟨_,ht⟩ r hr => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact hs.env.esp.trans ht.env.esp.symm
    · exact hs.env.ebp.trans ht.env.ebp.symm) valid
  rintro b y ⟨h,hy⟩
  have ar : InRegions (y.rd++y.wr) (argA caller 7) 4 := by rw [hy.rd,hy.wr]; exact h.readable
  have ptr := (hy.frame.readW (r:=⟨argA caller 7,4⟩) (Region.contains_self _ _) apart (by decide)).trans h.ptr
  obtain ⟨z,run,m,regs,rd,wr⟩ := readCaller (hy.env.esp.trans sp) hy.env.ebp G.L.fw hy.env.wW ar (by decide : dataO+4≤768)
  rw [ptr] at m
  have fr : Frame [dataSlot (p.2 8)] y.mem z.mem := by rw [m]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have enc := ctrTagState G Q D h.aad hy
  refine WP.of_runBlock ⟨z,run,⟨destinationTagState G enc fr (regs _ (by decide)) (regs _ (by decide)) (regs _ (by decide))
    rd wr (by rw [slotv_eq,m,Mem.readW_writeW_self32]) ?_,?_,?_⟩⟩
  · rw [rd,wr,hy.rd,hy.wr]; exact covers_left h.access.wr
  · rw [bytesAt_frame fr (fun r hr => List.mem_singleton.mp hr ▸ P.dstWork.sub_right (Lay.wSub (by decide))) (by omega_using [P.fT])]
    exact hy.out
  · exact (hy.frame.mono fun _ hr => List.mem_cons_of_mem _ hr).trans (fr.mono fun r hr => List.mem_singleton.mp hr ▸ List.mem_cons_self ..)

end VG.Proof.AesGcm.X86.Contiguous

namespace VG.Proof.AesGcm.X86.Contiguous
open VG.Impl.AesGcm.X86.Contiguous (FrameSize privateFrameBytes workBytes scrubBytes)
variable [size : FrameSize]
open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH fullTag)
abbrev Params := BitVec 32 × (Nat → BitVec 32)

abbrev ctAt (p : Params) (s : State) := bytesAt s.mem (w64 (p.2 6)) (p.2 7).toNat
abbrev tagAt (p : Params) (s₀ s : State) :=
  fullTag (ctxCiph s₀.mem (w64 (p.2 0)) (p.2 1).toNat) (ctxH s₀.mem (w64 (p.2 0)))
    (bytesAt s₀.mem (w64 (p.2 2)) (p.2 3).toNat) (bytesAt s₀.mem (w64 (p.2 4)) (p.2 5).toNat) (ctAt p s)

abbrev tagFrame (p : Params) (tag : BitVec 32) := (⟨w64 tag,16⟩ : Region)::oT workBytes p 0

structure TagPost (p : Params) (s₀ entry s : State) : Prop where
  env : OEnv workBytes p s₀ s
  ct : ctAt p s = ctAt p entry
  tag : bytesAt s.mem (w64 (p.2 8) + BitVec.ofNat 64 0) 16 = tagAt p s₀ entry
  frame : Frame (oT workBytes p 0) entry.mem s.mem

theorem computeTag (v : GcmImpl) [WSize workBytes v.ctr.scr] (p : Params) (G : OL workBytes p) :
    Pc (fun (b : State × State) s => OTIn workBytes p b.1 s ∧ s = b.2)
      (oneTag v.callees 0) (fun b s => TagPost p b.1 b.2 s) := by
  refine (oneTag_pc (vg:=v) G (o:=0) (.inl rfl)).mono (fun _ _ h => h) ?_
  rintro ⟨ref,entry⟩ y ⟨env,tag,frame⟩
  refine ⟨env,bytesAt_frame (oT_oF frame) (d_woF G (by decide)) (by have h := G.fd; omega),?_,frame⟩
  rw [tag]
  simp only [tagAt,ctAt,Proof.Gcm.fullTag_eq,padded_eq,length_bytesAt,xA,jOf]

/-- The restore block keeps the frame pointer as its current ESP. Its other
four nonvolatile registers come from the caller saved by the entry block. -/
abbrev frameCaller (p : Params) (ref : State) := ref.setReg .esp p.1

structure Finished (p : Params) (tag : BitVec 32) (ref entry s : State) : Prop where
  abi : abiPreserved (frameCaller p ref) s
  rd : s.rd=ref.rd
  wr : s.wr=ref.wr
  ct : ctAt p s=ctAt p entry
  auth : bytesAt s.mem (w64 tag) 16=tagAt p ref entry
  frame : Frame (tagFrame p tag) entry.mem s.mem

theorem finish_pc (v : GcmImpl) [WSize workBytes v.ctr.scr] (p : Params) (G : OL workBytes p) (T : BitVec 32)
    (fits : T.toNat+16≤2^32) (tw : (⟨w64 T,16⟩ : Region).Disjoint ⟨w64 (p.2 8),workBytes⟩)
    (dt : (⟨w64 (p.2 6),(p.2 7).toNat⟩ : Region).Disjoint ⟨w64 T,16⟩)
    (rt : (⟨w64 p.1,4⟩ : Region).Disjoint ⟨w64 T,16⟩) :
    Pc (fun (b : State × State) s => (OTIn workBytes p b.1 s ∧ s=b.2) ∧ arg b.1 8=T ∧ Covers [⟨w64 T,16⟩] b.1.wr)
      (.seq (oneTag v.callees 0) (.seq (tagOut 0) (.block restore))) (fun b s => Finished p T b.1 b.2 s) := by
  have big := workBytes_big
  refine Pc.seq (Pc.lift (computeTag v p G) (fun b _ => b) (fun _ _ h => h.1)) ?_
  refine Pc.seq (Pc.of (I:=fun s => WEnv workBytes (p.2 8) s ∧ slotv s.mem (p.2 8) tpO=T ∧ Covers [⟨w64 T,16⟩] s.wr)
    (R:=fun s t => bytesAt t.mem (w64 T) 16=bytesAt s.mem (w64 (p.2 8)+BitVec.ofNat 64 0) 16 ∧
      Frame [⟨w64 T,16⟩] s.mem t.mem ∧ t.gpr .ebp=s.gpr .ebp ∧ t.gpr .esi=s.gpr .esi ∧
      t.gpr .esp=s.gpr .esp ∧ t.rd=s.rd ∧ t.wr=s.wr)
    (fun _ h => tagOut_ok h.1 (by decide) h.2.1 h.2.2 fits) (tagOut_ct rfl fun _ h => ⟨h.1,h.2.1⟩) _
    (fun _ _ ⟨_,⟨_,ptr,cov⟩,h,_⟩ => ⟨⟨h.env.env.ebp,h.env.env.wW,G.L.fw,workBytes_big⟩,h.env.tp.trans ptr,h.env.wr ▸ cov⟩)) ?_
  refine Pc.taint [.ebp] ?_ (fun _ _ _ _ ⟨_,⟨_,_,h₁,_⟩,_,_,bp₁,_⟩ ⟨_,⟨_,_,h₂,_⟩,_,_,bp₂,_⟩ r hr => by
    obtain rfl := List.mem_singleton.mp hr
    rw [bp₁,bp₂,h₁.env.env.ebp,h₂.env.env.ebp]) (by taint_decide)
  rintro ⟨ref,entry⟩ s ⟨y,⟨_,_,tag,_⟩,auth,f,bp,_,sp,rd,wr⟩
  have saved := tag.env.saved.frame f (fun r hr => List.mem_singleton.mp hr ▸ (tw.sub_right (Lay.wSub (by decide))).symm)
  have pos : (frameCaller p ref).gpr .esp=p.1 := gpr_setReg_self ..
  have ret : s.mem.readW (w64 p.1) 32=ref.mem.readW (w64 p.1) 32 := by
    rw [ret_kept f (fun r hr => List.mem_singleton.mp hr ▸ rt)]; exact tag.env.ret
  refine (exit_ok (s₀:=frameCaller p ref) (bp.trans tag.env.env.ebp) ((sp.trans tag.env.env.esp).trans pos.symm)
    (by rw [rd,wr]; exact covers_left tag.env.env.wW) G.L.fw (show SavedAt _ _ _ from saved)
    (by rw [pos]; exact ret)).mono ?_
  rintro z ⟨abi,mem,_,rd',wr'⟩
  refine ⟨abi,rd'.trans (rd.trans tag.env.rd),wr'.trans (wr.trans tag.env.wr),?_,?_,?_⟩
  · unfold ctAt; rw [mem,bytesAt_frame f (fun r hr => List.mem_singleton.mp hr ▸ dt) (by have h:=G.fd; omega)]; exact tag.ct
  · rw [mem,auth]; exact tag.tag
  · rw [mem]
    exact (tag.frame.mono (fun _ h => List.mem_cons_of_mem _ h)).trans
      (f.mono fun r hr => List.mem_singleton.mp hr ▸ List.mem_cons_self ..)

end VG.Proof.AesGcm.X86.Contiguous

namespace VG.Proof.AesGcm.X86.Contiguous
open VG.Impl.AesGcm.X86.Contiguous (FrameSize privateFrameBytes workBytes scrubBytes)
variable [size : FrameSize]
open VG VG.X86 VG.Impl.AesGcm.X86 VG.Impl.AesGcm.X86.Contiguous
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH encryptWith inc32)

abbrev sealedInput (p : Params) (ref s : State) :=
  encryptWith (ctxCiph ref.mem (w64 (p.2 0)) (p.2 1).toNat) (ctxH ref.mem (w64 (p.2 0))) 16
    (bytesAt ref.mem (w64 (p.2 2)) (p.2 3).toNat) (ctAt p s)
    (bytesAt ref.mem (w64 (p.2 4)) (p.2 5).toNat)

abbrev sealWrites (p : Params) (dst tag : BitVec 32) := textWrites p dst ++ tagFrame (destParams p dst) tag

structure Sealed (p : Params) (dst tag : BitVec 32) (ref entry s : State) : Prop where
  abi : abiPreserved (frameCaller p ref) s
  rd : s.rd=ref.rd
  wr : s.wr=ref.wr
  result : sealedInput p ref entry=(bytesAt s.mem (w64 dst) (p.2 7).toNat, bytesAt s.mem (w64 tag) 16)
  frame : Frame (sealWrites p dst tag) entry.mem s.mem

abbrev sealTail (v : GcmImpl) : Prog isa := .seq (Open.decTo v.callees v.callees.ctr true)
  (.seq (.block (keep (callerSlot 7) dataO)) (.seq (oneTag v.callees 0) (.seq (tagOut 0) (.block restore))))

theorem sealTail_pc (v : GcmImpl) [WSize workBytes v.ctr.scr] (p : Params) (caller dst tag : BitVec 32)
    (sp : p.1=caller-(BitVec.ofNat 32 privateFrameBytes)) (G : OL workBytes p) (Q : OL workBytes (destParams p dst)) (D : OLD (destParams p dst))
    (P : DirectGather.PieceRegions workBytes (p.2 0) (p.2 8) p.1 (p.2 6) dst (p.2 7).toNat)
    (apart : ∀ r∈cipherFrame p dst, (⟨argA caller 7,4⟩ : Region).Disjoint r)
    (fits : tag.toNat+16≤2^32) (tw : (⟨w64 tag,16⟩ : Region).Disjoint ⟨w64 (p.2 8),workBytes⟩)
    (dt : (⟨w64 dst,(p.2 7).toNat⟩ : Region).Disjoint ⟨w64 tag,16⟩)
    (rt : (⟨w64 p.1,4⟩ : Region).Disjoint ⟨w64 tag,16⟩) :
    Pc (fun b s => PayloadPre p caller dst b s ∧ arg b.1 8=tag ∧ Covers [⟨w64 tag,16⟩] b.1.wr)
      (sealTail v) (fun b s => Sealed p dst tag b.1 b.2 s) := by
  let start (b : State × State) (s : State) := PayloadPre p caller dst b s ∧ arg b.1 8=tag ∧ Covers [⟨w64 tag,16⟩] b.1.wr
  let mid (b : State × State) (s : State) := PayloadPost p dst b s ∧ arg b.1 8=tag ∧ Covers [⟨w64 tag,16⟩] b.1.wr
  have crypt := payload_pc v p caller dst sp G Q D P apart
  have a := (Pc.lift (P':=start) crypt (fun b _ => b) fun _ _ h => h.1).mono (fun _ _ h => h)
    (fun b s ⟨_,h,z,_⟩ => (show mid b s from ⟨z,h.2⟩))
  have f := finish_pc v (destParams p dst) Q tag fits tw dt rt
  have last := Pc.lift (P':=mid) f (fun b s => (b.1,s)) (fun _ _ h => ⟨⟨h.1.tag,rfl⟩,h.2⟩)
  have bounded := Pc.seq a (last.mono (fun _ _ h => h) (fun b s ⟨y,h,z,_⟩ => by
    refine (show Sealed p dst tag b.1 b.2 s from ⟨z.abi,z.rd,z.wr,?_,?_⟩)
    · have c : Spec.Gcm.gctr (ctxCiph b.1.mem (w64 (p.2 0)) (p.2 1).toNat) (inc32 (jOf p b.1))
          (ctAt p b.2) = ctAt (destParams p dst) y := by rw [Proof.Gcm.gctr_eq]; exact h.1.ct.symm
      unfold sealedInput encryptWith
      change (_,_) = (ctAt (destParams p dst) s,_)
      rw [show Spec.Gcm.j0 _ _ = jOf p b.1 from rfl,c,z.ct,z.auth]
      congr 1
      exact List.take_of_length_le (by rw [Proof.Gcm.fullTag_eq,Proof.Cmac.toBytes_length])
    · exact (h.1.frame.mono fun r hi => List.mem_append_left _ hi).trans (z.frame.mono fun r hi => List.mem_append_right _ hi)))
  exact ⟨fun b s h => (bounded.wp b s h).assoc,RelCT.assoc bounded.ct⟩

end VG.Proof.AesGcm.X86.Contiguous
