module

public import VerifiedGarbage.Proof.AesGcm.X86.DirectGather.Text
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Gcm.SealGather

/-! One iteration of the direct-gather descriptor loop. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86.DirectGather

open VG VG.X86 VG.Impl.AesGcm.X86
open VG.Proof.Gcm (xorKs)
open VG.Spec.Gcm (Block)
open VG.Spec.Aes (bytesAt)

namespace TextInput
variable {a : Text} {s : State} (p : TextInput a s)
include p

theorem frameSlot {o n : Nat} (od : n ≤ a.len) (lo : 128 ≤ o) (hi : o+4 ≤ 240)
    (d160 : o+4 ≤ 160 ∨ 164 ≤ o) (d168 : o+4 ≤ 168 ∨ 176 ≤ o)
    (d180 : o+4 ≤ 180 ∨ 184 ≤ o) (d196 : o+4 ≤ 196 ∨ 200 ≤ o) :
    ∀ r ∈ a.frame n, (⟨w64 a.W+BitVec.ofNat 64 o,4⟩ : Region).Disjoint r := by
  intro r hr
  simp only [Text.frame,crFrame,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl
  · exact ((p.dstOutside.w.sub_left (Region.sub_prefix od)).sub_right (Lay.wSub (by omega_using [hi]))).symm
  · exact (p.lay.st_w (by decide) (.inr ⟨by omega_using [lo],by omega_using [hi]⟩)).symm
  · exact Lay.w_w (.inl hi) (by omega_using [hi]) (by decide)
  · exact (p.lay.stk_w (by omega_using [hi])).symm
  · exact (p.argW.sub_right (Lay.wSub (by omega_using [hi]))).symm
  · exact Lay.w_w d160 (by omega_using [hi]) (by decide)
  · exact Lay.w_w d168 (by omega_using [hi]) (by decide)
  · exact Lay.w_w d180 (by omega_using [hi]) (by decide)
  · exact Lay.w_w d196 (by omega_using [hi]) (by decide)

theorem setupSlot {o : Nat} (lt : o+4 ≤ 2560)
    (d160 : o+4 ≤ 160 ∨ 164 ≤ o) (d168 : o+4 ≤ 168 ∨ 176 ≤ o)
    (d196 : o+4 ≤ 196 ∨ 200 ≤ o) (d276 : o+4 ≤ 276 ∨ 284 ≤ o) :
    ∀ r ∈ setupFrame a.W a.SP, (⟨w64 a.W+BitVec.ofNat 64 o,4⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact Lay.w_w d160 lt (by decide)
  · exact Lay.w_w d168 lt (by decide)
  · exact Lay.w_w d196 lt (by decide)
  · exact Lay.w_w d276 lt (by decide)
  · exact (p.argW.sub_right (Lay.wSub lt)).symm

theorem pieceSlot {o i : Nat} (hi : i<a.count) (pos : a.size s.mem i ≠ 0)
    (lo : 128 ≤ o) (fit : o+4 ≤ 240) (sep : o+4 ≤ 168 ∨ 176 ≤ o) :
    ∀ r ∈ pieceFrame a.st a.W a.SP (atByte a.O (a.off s.mem i)) (a.size s.mem i),
      (⟨w64 a.W+BitVec.ofNat 64 o,4⟩ : Region).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with h | h
  · simp only [crFrame,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl
    · exact ((p.input i hi pos).dstWork.sub_right (Lay.wSub (by omega_using [fit]))).symm
    · exact (p.lay.st_w (by decide) (.inr ⟨by omega_using [lo],by omega_using [fit]⟩)).symm
    · exact Lay.w_w (.inl fit) (by omega_using [fit]) (by decide)
    · exact (p.lay.stk_w (by omega_using [fit])).symm
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl
    · exact Lay.w_w sep (by omega_using [fit]) (by decide)
    · exact (p.argW.sub_right (Lay.wSub (by omega_using [fit]))).symm

theorem pieceSub {i : Nat} (hi : i<a.count) (pos : a.size s.mem i ≠ 0) {m u : Mem}
    (f : Frame (pieceFrame a.st a.W a.SP (atByte a.O (a.off s.mem i)) (a.size s.mem i)) m u) :
    Frame (a.frame (a.off s.mem (i+1))) m u := by
  refine f.sub ?_
  intro r hr
  have span := p.span hi
  have fit := p.dstFit
  simp only [pieceFrame,crFrame,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with (rfl | rfl | rfl | rfl) | rfl | rfl
  · refine ⟨⟨w64 a.O,a.off s.mem (i+1)⟩,by simp [Text.frame,crFrame],?_⟩
    rw [w64_add (by omega_using [span,fit,pos])]
    have eq : a.off s.mem (i+1) = a.off s.mem i+a.size s.mem i := Gather.gl_succ p.descFit hi
    rw [eq]
    exact Offset.sub_base _ (Nat.le_refl _)
  all_goals exact ⟨_,by simp [Text.frame,crFrame],fun _ h => h⟩

theorem outsideCtx : a.Outside ⟨w64 a.C,256⟩ := ⟨p.lay.cw,p.argCtx,p.lay.kc.symm⟩

theorem setupCtr {d : Nat} (hd : d+16 ≤ 80) : ∀ r ∈ setupFrame a.W a.SP,
    (⟨w64 a.st+BitVec.ofNat 64 d,16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  case inr.inr.inr.inr =>
    exact (p.argW.sub_right (fun _ q => stSub p.lay rfl _ (Lay.stSub hd _ q))).symm
  all_goals exact p.lay.st_w hd (.inr ⟨by decide,by decide⟩)

structure Loaded (a : Text) (s : State) (icb : Block) (i : Nat) (y : State) : Prop where
  args : PieceArgs a.C a.st a.W a.SP (a.source s.mem i) (atByte a.O (a.off s.mem i)) y (a.size s.mem i) (a.off s.mem i)
  rd : y.rd=s.rd
  wr : y.wr=s.wr
  ptr : slotv y.mem a.W rO = a.desc (i+1)
  count : slotv y.mem a.W tglO = BitVec.ofNat 32 (a.count-i)
  off : slotv y.mem a.W xlO = BitVec.ofNat 32 (a.off s.mem (i+1))
  dest : y.mem.readW (w64 a.SP) 32 = atByte a.O (a.off s.mem i)
  frame : Frame (a.frame (a.off s.mem i)) s.mem y.mem
  ctr : CtrS y.mem a.st (ciphOf s.mem a.C a.rounds) icb (a.off s.mem i)
  out : bytesAt y.mem (w64 a.O) (a.off s.mem i) = xorKs (ciphOf s.mem a.C a.rounds) icb 0 (a.buf s.mem i)

theorem load_ok {icb : Block} {i : Nat} {u : State} (hi : i<a.count) (h : TextAt a s icb i u) :
    WP isa (.block Impl.AesGcm.X86.DirectGather.nextPiece) u (Loaded a s icb i) := by
  refine WP.mono (p.descStep hi h) ?_
  rintro y ⟨m,di,zf,bp,si,sp,rd,wr⟩
  have od := p.off_le (Nat.le_of_lt hi)
  have flt := Nat.lt_of_le_of_lt od p.lenLt
  have f : Frame (setupFrame a.W a.SP) u.mem y.mem := by rw [m]; exact setupFrame_ok _ _ _ _ _ _ _ _
  have sl : SetupSlots y.mem a.W a.SP (a.desc i) (a.source s.mem i) a.O (a.off s.mem i) (a.size s.mem i) := by
    rw [m]; exact setupSlots _ _ _ _ _ _ flt p.argW
  have env := h.env.keep (bp.trans h.env.ebp.symm) (si.trans h.env.esi.symm) (sp.trans h.env.esp.symm)
    rd wr (slot_frame f (p.setupSlot (by decide) (by decide) (by decide) (by decide) (by decide)))
  obtain p' : a.desc i + 8#32 = a.desc (i+1) := by
    unfold Text.desc atByte
    rw [BitVec.add_assoc,←BitVec.ofNat_add]; congr 2
  let gl : a.off s.mem (i+1) = a.off s.mem i + a.size s.mem i := Gather.gl_succ p.descFit hi
  have z := p.dstOutside.setup
  exact ⟨⟨env,sl.nO,sl.bO,sl.len,sl.src,di,zf⟩,rd.trans h.rd,wr.trans h.wr,sl.ptr.trans p',
    (slot_frame f (p.setupSlot (by decide) (by decide) (by decide) (by decide) (by decide))).trans h.count,
    sl.total.trans (congrArg _ gl.symm),sl.arg,h.frame.trans (Text.setup_sub a _ f),
    h.ctr.congr (blockAt_frame f (p.setupCtr (by decide))) (blockAt_frame f (p.setupCtr (by decide))),
    (bytesAt_frame f (fun r hr => (z r hr).sub_left (Region.sub_prefix od)) (by omega_using [flt])).trans h.out⟩

structure Advanced (a : Text) (s : State) (icb : Block) (i : Nat) (z : State) : Prop where
  env : Env a.C a.st a.W a.SP z
  rd : z.rd=s.rd
  wr : z.wr=s.wr
  ptr : slotv z.mem a.W rO = a.desc (i+1)
  count : slotv z.mem a.W tglO = BitVec.ofNat 32 (a.count-i)
  off : slotv z.mem a.W xlO = BitVec.ofNat 32 (a.off s.mem (i+1))
  frame : Frame (a.frame (a.off s.mem (i+1))) s.mem z.mem
  ctr : CtrS z.mem a.st (ciphOf s.mem a.C a.rounds) icb (a.off s.mem (i+1))
  out : bytesAt z.mem (w64 a.O) (a.off s.mem (i+1)) = xorKs (ciphOf s.mem a.C a.rounds) icb 0 (a.buf s.mem (i+1))

theorem advance_ok (v : GcmImpl) {icb : Block} {i : Nat} {y : State} (hi : i<a.count) (h : Loaded a s icb i y) :
    WP isa (.seq (.ite .e (.block []) Impl.AesGcm.X86.DirectGather.partialHead) (Open.decTo v.callees v.callees.ctr))
      y (Advanced a s icb i) := by
  have ord := p.off_le (Nat.le_of_lt hi)
  have span := p.span hi
  have fit := p.dstFit
  have gl : a.off s.mem (i+1) = a.off s.mem i+a.size s.mem i := Gather.gl_succ p.descFit hi
  have pt : a.buf s.mem (i+1) = a.buf s.mem i ++ bytesAt s.mem (w64 (a.source s.mem i)) (a.size s.mem i) := Gather.pt_succ p.descFit hi
  by_cases nz : a.size s.mem i=0
  · have eq : a.off s.mem (i+1) = a.off s.mem i := by rw [gl,nz,Nat.add_zero]
    have buf : a.buf s.mem (i+1) = a.buf s.mem i := by rw [pt,nz]; exact List.append_nil _
    have args := h.args
    rw [nz] at args
    refine WP.mono (processPiece_empty v p.lay args) ?_
    rintro z ⟨m,e,rd,wr⟩
    refine ⟨e,rd.trans h.rd,wr.trans h.wr,by rw [m]; exact h.ptr,by rw [m]; exact h.count,by rw [m]; exact h.off,
      by rw [m,eq]; exact h.frame,by rw [m,eq]; exact h.ctr,by rw [m,eq,buf]; exact h.out⟩
  · have pre := p.input i hi nz
    have acc := p.accesses hi nz h.rd h.wr h.dest
    have r : RoundsAt y.mem a.W a.rounds :=
      ⟨(slot_frame h.frame (p.frameSlot ord (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))).trans
        p.rounds.1,p.rounds.2⟩
    have dst : w64 (atByte a.O (a.off s.mem i)) = w64 a.O+BitVec.ofNat 64 (a.off s.mem i) := w64_add (by omega_using [fit,span,nz])
    refine WP.mono (processPiece_ok v p.lay rfl pre acc h.args p.argCtx
      (by rw [h.wr]; exact p.spW _ _ ⟨_,List.mem_singleton_self _,Region.contains_self _ _⟩)
      (p.srcOutside i hi).sp (by have f:=p.lenLt; omega_using [f,span]) r
      (ciph_frame h.frame (p.outsideCtx.frame p.lay (p.ctxDst.sub_right (Region.sub_prefix ord))) r.2) h.ctr) ?_
    intro z done
    have keep {o : Nat} (lo : 128 ≤ o) (fit : o+4 ≤ 240) (sep : o+4 ≤ 168 ∨ 176 ≤ o) :=
      slot_frame done.frame (p.pieceSlot hi nz lo fit sep)
    have keepPrev : bytesAt z.mem (w64 a.O) (a.off s.mem i) = bytesAt y.mem (w64 a.O) (a.off s.mem i) := by
      refine bytesAt_frame done.frame ?_ (by omega_using [fit,ord])
      intro x hx
      simp only [pieceFrame,crFrame,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with (rfl | rfl | rfl | rfl) | rfl | rfl
      · rw [dst]; exact split_disj (by omega_using [span,fit])
      · exact ((p.dstOutside.w.sub_left (Region.sub_prefix ord)).sub_right
          (fun _ q => stSub p.lay rfl _ (Lay.stSub (by decide) _ q)))
      · exact (p.dstOutside.w.sub_left (Region.sub_prefix ord)).sub_right (Lay.wSub (by decide))
      · exact p.dstOutside.stack.sub_left (Region.sub_prefix ord)
      · exact (p.dstOutside.w.sub_left (Region.sub_prefix ord)).sub_right (Lay.wSub (by decide))
      · exact p.dstOutside.sp.sub_left (Region.sub_prefix ord)
    have src := bytesAt_frame h.frame ((p.srcOutside i hi).frame p.lay ((p.srcDst i hi).sub_right (Region.sub_prefix ord)))
      (by have f:=p.lenLt; omega_using [span,f])
    have out := done.out
    rw [src,dst] at out
    refine ⟨done.env,done.rd.trans h.rd,done.wr.trans h.wr,(keep (by decide) (by decide) (by decide)).trans h.ptr,
      (keep (by decide) (by decide) (by decide)).trans h.count,(keep (by decide) (by decide) (by decide)).trans h.off,
      (Text.frame_mono a (by rw [gl]; omega_using []) h.frame).trans (p.pieceSub hi nz done.frame),
      by rw [gl]; exact done.ctr,?_⟩
    rw [gl,bytesAt_add,pt,Proof.Gcm.xorKs_append,Proof.Gcm.length_gathered,Nat.zero_add,keepPrev,h.out,out]

theorem countdown {icb : Block} {i : Nat} {z : State} (hi : i<a.count) (h : Advanced a s icb i z) :
    WP isa (.block [.mov .ecx (slot tglO),.alu .sub .ecx (imm 1),.store (at_ .ebp tglO) .ecx]) z fun t =>
      TextAt a s icb (i+1) t ∧ t.zf=some (decide (i+1=a.count)) := by
  have fin := p.off_le (i:=i+1) (by omega_using [hi])
  refine WP.mono (decrement_ok p.lay h.env (by omega_using [hi]) (by have f:=p.countLt; omega_using [hi,f]) h.count) ?_
  rintro t ⟨m,zf,g,rd,wr⟩
  have f : Frame [⟨w64 a.W+180#64,4⟩] z.mem t.mem := by
    rw [m]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have slot {o : Nat} (d : o+4 ≤ 180 ∨ 184 ≤ o) (lt : o < 2^32) :
      slotv t.mem a.W o = slotv z.mem a.W o := by
    rw [m]; exact readW_writeW_off _ _ _ (b:=180) d lt (by decide)
  have e := h.env.keep (g .ebp (by decide)) (g .esi (by decide)) (g .esp (by decide)) rd wr (slot (by decide) (by decide))
  have stApart (d : Nat) (hd : d+16 ≤ 80) : ∀ r ∈ [⟨w64 a.W+180#64,4⟩],
      (⟨w64 a.st+BitVec.ofNat 64 d,16⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact p.lay.st_w hd (.inr ⟨by decide,by decide⟩)
  have sub : a.count-i-1=a.count-(i+1) := by omega_using []
  have cnt : slotv t.mem a.W tglO=BitVec.ofNat 32 (a.count-(i+1)) := by
    rw [m,slotv,Mem.readW_writeW_self32,sub]
  have curr : a.count-i=1 ↔ i+1=a.count := by constructor <;> intro v <;> omega_using [hi,v]
  exact ⟨⟨e,rd.trans h.rd,wr.trans h.wr,(slot (by decide) (by decide)).trans h.ptr,cnt,
    (slot (by decide) (by decide)).trans h.off,h.frame.trans (f.sub fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact ⟨_,by simp [Text.frame],fun _ v => v⟩),
    h.ctr.congr (blockAt_frame f (stApart 48 (by decide))) (blockAt_frame f (stApart 64 (by decide))),
    (bytesAt_frame f (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx
      exact (p.dstOutside.w.sub_left (Region.sub_prefix fin)).sub_right (Lay.wSub (by decide)))
      (by have lt:=p.lenLt; omega_using [fin,lt])).trans h.out⟩,by simpa only [curr] using zf⟩

theorem pieces_ok (v : GcmImpl) {icb : Block} (ptr : slotv s.mem a.W rO=a.Src)
    (count : slotv s.mem a.W tglO=BitVec.ofNat 32 a.count) (off : slotv s.mem a.W xlO=0)
    (ctr : CtrS s.mem a.st (ciphOf s.mem a.C a.rounds) icb 0) :
    WP isa (Impl.AesGcm.X86.DirectGather.pieces v.callees) s (TextAt a s icb a.count) := by
  refine WP.seq (WP.of_runBlock ⟨_,by xrun [p.env.ebp,p.lay.aW,p.env.wIn',count],?_⟩)
  let u := arithFlags (s.setReg .ecx (BitVec.ofNat 32 a.count))
    (BitVec.ofNat 32 a.count &&& BitVec.ofNat 32 a.count) false false
  have start : TextAt a s icb 0 u :=
    ⟨⟨p.env.ebp,p.env.esi,p.env.esp,p.env.ctxR,p.env.stW,p.env.wW,p.env.ctx⟩,rfl,rfl,
      by change slotv s.mem a.W rO=a.desc 0; simpa [Text.desc,atByte] using ptr,count,off,Frame.refl _ _,ctr,rfl⟩
  refine WP.ite (decide (a.count=0)) (congrArg some (and_self_beq32 p.countLt)) (fun z => ?_) (fun nz => ?_)
  · have zero : a.count=0 := by simpa using z
    apply WP.block_nil
    change TextAt a s icb a.count u
    rw [zero]
    exact start
  · have pos : 0<a.count := Nat.pos_of_ne_zero (by simpa using nz)
    refine WP.loop (M:=isa) (c:=.ne) (fun n t => ∃ i, n=a.count-i ∧ i<a.count ∧ TextAt a s icb i t)
      ?_ (a.count-0) _ ⟨0,rfl,pos,start⟩
    rintro _ t ⟨i,rfl,hi,at_⟩
    refine WP.seq (WP.mono (p.load_ok hi at_) ?_)
    intro y loaded
    refine WP.assoc (WP.seq (WP.mono (p.advance_ok v hi loaded) ?_))
    intro z done
    refine WP.mono (p.countdown hi done) ?_
    rintro q ⟨hq,hz⟩
    have ev : isa.eval .ne q=some (!decide (i+1=a.count)) := by show q.zf.map (!·)=_; rw [hz]; rfl
    by_cases eq : i+1=a.count
    · left; exact ⟨by rw [ev]; simp [eq],eq ▸ hq⟩
    · right; exact ⟨by rw [ev]; simp [eq],a.count-(i+1),by omega_using [hi],i+1,rfl,by omega_using [hi,eq],hq⟩

end TextInput
end VG.Proof.AesGcm.X86.DirectGather
