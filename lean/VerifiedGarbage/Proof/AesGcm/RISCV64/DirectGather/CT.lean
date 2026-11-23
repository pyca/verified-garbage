module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.DirectGather.BindLoop
public import VerifiedGarbage.Proof.AesGcm.RISCV64.DirectGather.LoopCT
import VerifiedGarbage.Proof.Framework.RISCV64.CallWipe
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTSeal
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.DirectGather.Aad
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint

/-! # Public address and branch traces for the whole RISC-V direct gather -/

public section
namespace VG.Proof.AesGcm.RISCV64.DirectGather

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64 VG.Impl.AesGcm.RISCV64.DirectGather
open VG.Proof.AesGcm.RISCV64.GatherBs
open VG.Proof.Gather.RISCV64 (Eq2 TT rel_seq rel_taint)
open VG.Impl.StackScratch.RISCV64

variable {o p s t : State}

/-- The public call arguments used at each composition boundary. -/
structure CallPublic (o p : State) : Prop where
  c : C o = C p
  r : Rn o = Rn p
  n : Nn o = Nn p
  nl : NL o = NL p
  ad : Ad o = Ad p
  al : o.gpr .a5 = p.gpr .a5
  src : Src o = Src p
  count : Cnt o = Cnt p
  sp : frameSp o = frameSp p
  w : work o = work p
  dst : Dst o = Dst p
  length : stackArg o 1 = stackArg p 1
  tag : Tg o = Tg p
  bk : Bk o = Bk p
  desc : ∀ j < Cnt o * 16, o.mem (Src o + BitVec.ofNat 64 j) = p.mem (Src o + BitVec.ofNat 64 j)

theorem CallPublic.of_pub (pub : gatherPub o p) : CallPublic o p := by
  obtain ⟨hc,hr,hn,hnl,ha,hal,hs,hsn,hsp,hd,hl,ht,hb,desc⟩ := pub
  have ss : frameSp o = frameSp p := congrArg (· - BitVec.ofNat 64 2608) hsp
  exact ⟨hc,congrArg BitVec.toNat hr,hn,congrArg BitVec.toNat hnl,ha,hal,hs,congrArg BitVec.toNat hsn,
    ss,congrArg (· + 40) ss,hd,hl,ht,hb,desc⟩

private theorem loadWork_wp (h : Caller o) (ht : Prepared o t) :
    WP isa (.block [.addSp .t1 0,.load .d .t1 .t1 32]) t fun z => z.gpr .t1 = work o ∧ z.sp = frameSp o := by
  refine WP.mono (oneAg_ok (off := 32) (by decide) (by rw [ht.sp]; exact (stackOf h).al)
    (by rw [ht.sp]; exact in_off (d := 32) (areaCover ht) (by decide) (by decide))
    (by rw [ht.sp]; exact ht.workArg)) fun z ⟨val,_,keep⟩ => ⟨val,keep.sp.trans ht.sp⟩

theorem entry_rel (g : CallPublic o p) (h : Caller o) (k : Caller p) (u : Prepared o s) (v : Prepared p t) :
    RelCT isa (Eq2 s t) (.block entry) TT := by
  unfold entry
  rw [oneEntryAt_eq,List.append_assoc]
  apply RelCT.block_append
  refine rel_seq (rel_taint [] (u.sp.trans (g.sp.trans v.sp.symm)) (by simp) (by taint_decide))
    (loadWork_wp h u) (loadWork_wp k v) fun x y ⟨hx,xsp⟩ ⟨hy,ysp⟩ => ?_
  refine rel_taint [.t1] (xsp.trans (g.sp.trans ysp.symm)) ?_ (by taint_decide)
  intro r hr; obtain rfl := List.mem_singleton.mp hr; exact hx.trans (g.w.trans hy.symm)

private abbrev AadInput (o s : State) :=
  OneI (C o) (work o) (frameSp o) (Rn o) (Nn o) (NL o) (Ad o) (o.gpr .a5) (Dst o) (stackArg o 1) s ∧
    s.gpr .s4 = Nn o ∧ s.gpr .s5 = BitVec.ofNat 64 (NL o)

private theorem aadInput (h : Caller o) (v : Started o s) : AadInput o s := by
  have N : nR o ∈ inputs o := by simp [inputs]
  have A : aR o ∈ inputs o := by simp [inputs]
  have D : dR o ∈ inputs o ++ [dR o,tgR o] := List.mem_append_right _ (.head _)
  have dr : Covers [dR o] (s.rd ++ s.wr) := by
    apply covers_left
    rw [v.wr]
    exact covers_mem (List.mem_cons_of_mem _ (by rw [h.layout.pre.2.1]; exact .head _))
  have canon (x : Addr) : x = BitVec.ofNat 64 x.toNat := by simp
  exact ⟨⟨s.gpr,v.s2,v.s1,v.s0,v.s3.trans (canon _),
    v.s7.trans (canon _),v.s10,v.s11,v.environment h,
    dataOf h v.sp (List.mem_append_left _ N) (o.gpr .a3).isLt (inputCover h v.rd _ N),
    dataOf h v.sp (List.mem_append_left _ A) (o.gpr .a5).isLt (inputCover h v.rd _ A),
    dataOf h v.sp D (stackArg o 1).isLt dr,v.aad,v.dst⟩,v.s4,v.s5.trans (canon _)⟩

theorem aad_rel [VG.Proof.Gcm.RISCV64.GhashLaw] (g : CallPublic o p) (h : Caller o) (k : Caller p)
    (u : Started o s) (v : Started p t) : RelCT isa (Eq2 s t) oneAad TT := by
  have a := aadInput h u
  have b := aadInput k v
  unfold AadInput at b
  rw [← g.c,← g.w,← g.sp,← g.r,← g.n,← g.nl,← g.ad,← g.al,← g.dst,← g.length] at b
  have ct : CT (AadInput o) oneAad := oneAad_ct (layoutOf h)
  exact RelCT.mono ct (fun x y ⟨ex,ey⟩ => by rw [ex,ey]; exact ⟨a,b⟩) fun _ _ _ => trivial

/-- Copying public stack arguments has the same trace for every caller with
the same stack pointer. All subsequent work runs inside that frame. -/
theorem sealGather_ct_of (bodyCT : ∀ (o p : State), Caller o → Caller p → CallPublic o p →
      RelCT isa (Eq2 (prepared o) (prepared p)) body TT) :
    ConstantTime isa gatherPre gatherPub sealGather := by
  apply VG.Proof.Gather.RISCV64.ct_of
  intro o p ho hp pub
  have h := caller ho
  have k := caller hp
  have g := CallPublic.of_pub pub
  have eqp : ∀ (x : State) (l : Caller x), WP isa (.block (setArgs 2608 4)) (allocated x) (· = prepared x) :=
    fun x l => ⟨_,_,Exec.block_iff.mpr (prepared_run l.layout).1,rfl⟩
  refine (RelCT.alloc (bytes := 2608) (P := Eq2 o p) (R := TT)
    ((?_ : RelCT isa (Eq2 (allocated o) (allocated p)) _ TT).mono
      (fun s t ⟨x,y,⟨hx,hy⟩,hs,ht⟩ => by subst hx hy; exact ⟨hs,ht⟩) fun _ _ hp => hp)).mono
    (fun _ _ r => r) fun _ _ _ => trivial
  refine rel_seq (c₂ := body) ?_ (eqp o h) (eqp p k) fun x y (ex : x = prepared o) (ey : y = prepared p) => ?_
  swap
  · rw [ex,ey]; exact bodyCT o p h k g
  rintro x y trace₁ trace₂ z w ⟨rfl,rfl⟩ hx hy
  rw [Exec.block_iff,(prepared_run h.layout).1] at hx
  rw [Exec.block_iff,(prepared_run k.layout).1] at hy
  obtain ⟨_,rfl⟩ := Prod.mk.inj (Option.some.inj hx)
  obtain ⟨_,rfl⟩ := Prod.mk.inj (Option.some.inj hy)
  exact ⟨congrArg (fun u => setArgsTrace 2608 u 4) g.sp,trivial⟩

abbrev exitHead : List Instr := [.addSp .t1 0,.load .d .s9 .t1 16]
abbrev exitCode : Prog isa := .block (exitHead ++ tagOut ++ restore)

structure ExitInput (o t : State) : Prop where
  work : t.gpr .s0 = work o
  sp : t.sp = frameSp o
  wr : t.wr = (allocated o).wr
  tag : t.mem.readW (frameSp o+16) 64 = Tg o

private theorem exitHead_wp (h : Caller o) (u : ExitInput o t) :
    WP isa (.block exitHead) t fun z => z.gpr .s9=Tg o ∧ z.gpr .s0=work o ∧ z.sp=frameSp o := by
  refine Steps.wp_addSp (imm := 0) (by decide) fun x ux => ?_
  have al := (stackOf h).al
  refine Steps.wp_ld (a := frameSp o+16) (off := 16) (by decide)
    (by rw [ux.gpr,BitVec.add_zero,u.sp]; rfl)
    (Spill.al8 (d := 16) (by omega) (by decide))
    (by rw [ux.wr]; apply in_left; rw [u.wr]; exact ⟨_,.head _,
      Offset.contains_base _ (by decide : 16+8 ≤ 2608) (by decide)⟩) fun z uz => WP.block_nil ?_
  exact ⟨uz.gpr.trans (ux.mem ▸ u.tag),
    (uz.other .s0 (by decide)).trans ((ux.other .s0 (by decide)).trans u.work),uz.sp.trans (ux.sp.trans u.sp)⟩

theorem exit_rel (g : CallPublic o p) (h : Caller o) (k : Caller p) (u : ExitInput o s) (v : ExitInput p t) :
    RelCT isa (Eq2 s t) exitCode TT := by
  unfold exitCode
  rw [List.append_assoc]
  apply RelCT.block_append
  refine rel_seq (rel_taint [] (u.sp.trans (g.sp.trans v.sp.symm)) (by simp) (by taint_decide))
    (exitHead_wp h u) (exitHead_wp k v) fun x y ⟨tag,work,sp⟩ ⟨tag',work',sp'⟩ => ?_
  refine rel_taint [.s9,.s0] (sp.trans (g.sp.trans sp'.symm)) ?_ (by taint_decide)
  simpa only [List.forall_mem_cons,List.not_mem_nil,false_imp_iff,implies_true,and_true] using
    And.intro (tag.trans (g.tag.trans tag'.symm)) (work.trans (g.w.trans work'.symm))

abbrev textCode : Prog isa := .seq pieces (.seq (oneTagB true 0) exitCode)

theorem body_rel_of [VG.Proof.Gcm.RISCV64.GhashLaw] (g : CallPublic o p) (h : Caller o) (k : Caller p)
    (text : ∀ x y, Ready o x → Ready p y → RelCT isa (Eq2 x y) textCode TT) :
    RelCT isa (Eq2 (prepared o) (prepared p)) body TT := by
  have po := (prepared_run h.layout).2
  have pp := (prepared_run k.layout).2
  refine rel_seq (entry_rel g h k po pp) (start_wp h.layout po) (start_wp k.layout pp) fun x y ux uy => ?_
  refine rel_seq (aad_rel g h k ux uy) (WP.with_rdwr' (aad_wp h ux)) (WP.with_rdwr' (aad_wp k uy))
    fun q r ⟨aq,rd,wr⟩ ⟨ar,rd',wr'⟩ => ?_
  exact rel_seq (rel_taint [] (aq.env.sp.trans (g.sp.trans ar.env.sp.symm)) (by simp) (by taint_decide))
    (ready_wp h ux aq rd wr) (ready_wp k uy ar rd' wr') text

theorem callLoopPublic (g : CallPublic o p) (u : Ready o s) (v : Ready p t) :
    LoopPublic (loopArgs o s) (loopArgs p t) := by
  refine ⟨g.src,g.dst,g.count,g.r,u.s2.trans (g.c.trans v.s2.symm),
    u.s1.trans ((congrArg (· + 16) g.w).trans v.s1.symm),u.s0.trans (g.w.trans v.s0.symm),
    u.s7.trans (g.bk.trans v.s7.symm),g.sp,?_,?_⟩
  · intro i hi
    change VG.Proof.Gather.RISCV64.sb o.mem (Src o) i = VG.Proof.Gather.RISCV64.sb p.mem (Src p) i
    rw [← g.src]
    exact VG.Proof.Gather.RISCV64.sb_agree g.desc hi
  · intro i hi
    change VG.Proof.Gather.RISCV64.sl o.mem (Src o) i = VG.Proof.Gather.RISCV64.sl p.mem (Src p) i
    rw [← g.src]
    exact VG.Proof.Gather.RISCV64.sl_agree g.desc hi

abbrev TagInput (o s : State) :=
  OneIK (C o) (work o) (frameSp o) (Rn o) (Bk o) (Ad o) (o.gpr .a5) (Dst o) (stackArg o 1) s ∧
    BkIn (Bk o) (C o) (statePtr o) (work o) (frameSp o) (Rn o) s.mem (Dst o) (Dst o) (L o) s

theorem tagInput {e : State} (h : Caller o) (v : Ready o e) (u : LoopAt (loopArgs o e) e (Cnt o) s) :
    TagInput o s := by
  let a := loopArgs o e
  obtain ⟨d,env⟩ := u.env
  have H := loopInput h v
  have bk := H.bk.frame H.rounds u.frame H.bkApart H.ctxApart u.rd u.wr
  change BkIn (e.gpr .s7) (e.gpr .s2) (e.gpr .s1) (e.gpr .s0) (frameSp o) (Rn o) s.mem
    (Dst o) (Dst o) (GatherBs.gl o (Cnt o)) s at bk
  rw [v.s7,v.s2,v.s1,v.s0,h.layout.hgl] at bk
  have D := (dataWrite h v).ok.of_eq u.rd u.wr u.sp
  have A : aR o ∈ inputs o := by simp [inputs]
  have da := dataOf h v.sp (List.mem_append_left _ A) (o.gpr .a5).isLt (inputCover h v.rd _ A)
  have ds : s.mem.readW (work o + 240) 64 = Dst o := by
    have eq := u.dest; change s.mem.readW (e.gpr .s0+240) 64 = Dst o at eq; rwa [v.s0] at eq
  have aad : s.mem.readW (work o+232) 64 = Ad o := by
    refine (u.frame.readW (Region.contains_self (work o + 232) 8) ?_ (by decide)).trans v.aad
    intro r hr
    change r ∈ [⟨Dst o,GatherBs.gl o (Cnt o)⟩,⟨e.gpr .s1+48,32⟩,⟨e.gpr .s0+512,2048⟩,
      ⟨e.gpr .s0+248,8⟩,⟨e.gpr .s0+256,8⟩] at hr
    rw [v.s1,v.s0,h.layout.hgl] at hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl
    · exact D.w.symm.sub_left (Lay.wSub (d := 232) (by decide))
    · exact ((layoutOf h).sb.symm.sub_left (Lay.bSub (d := 232) (by decide) (by decide))).sub_right (Lay.stSub (by decide))
    all_goals exact Offset.disjoint (work o) (Or.inl (by decide)) (by decide) (by decide)
  have canon (x : Addr) : x = BitVec.ofNat 64 x.toNat := by simp
  exact ⟨⟨a.regs (Cnt o) d,v.s2,v.s1,v.s0,v.s3.trans (canon _),v.s7,v.s10,v.s11,env,
    da.of_eq u.rd u.wr u.sp,D,aad,ds⟩,bk⟩

theorem tag_rel [VG.Proof.Gcm.RISCV64.GhashLaw] {e f : State}
    (g : CallPublic o p) (h : Caller o) (k : Caller p) (v : Ready o e) (q : Ready p f)
    (u : LoopAt (loopArgs o e) e (Cnt o) s) (r : LoopAt (loopArgs p f) f (Cnt p) t) :
    RelCT isa (Eq2 s t) (oneTagB true 0) TT := by
  have a := tagInput h v u
  have b := tagInput k q r
  unfold TagInput statePtr L at b
  rw [← g.c,← g.w,← g.sp,← g.r,← g.bk,← g.ad,← g.al,← g.dst,← g.length] at b
  have ct : CT (TagInput o) (oneTagB true 0) :=
    (oneTagB_ct (layoutOf h) (kb := Bk o) (o := 0) (.inl rfl) h.layout.hR).mono
      fun _ x => ⟨x.1,fun _ => ⟨rfl,x.2⟩⟩
  exact RelCT.mono ct (fun x y ⟨ex,ey⟩ => by rw [ex,ey]; exact ⟨a,b⟩) fun _ _ _ => trivial

theorem complete_ct [VG.Proof.Gcm.RISCV64.GhashLaw]
    (tagWP : ∀ (o e s : State), Caller o → Ready o e → LoopAt (loopArgs o e) e (Cnt o) s →
      WP isa (oneTagB true 0) s (ExitInput o)) :
    ConstantTime isa gatherPre gatherPub sealGather := by
  refine sealGather_ct_of fun o p h k g => body_rel_of g h k fun e f v q => ?_
  have A := loopInput h v
  have B := loopInput k q
  have X := loopAt0 h v
  have Y := loopAt0 k q
  refine rel_seq (pieces_rel (callLoopPublic g v q) A B X Y) (pieces_wp A X) (pieces_wp B Y)
    fun s t u r => ?_
  exact rel_seq (tag_rel g h k v q u r) (tagWP o e s h v u) (tagWP p f t k q r)
    fun z w ez ew => exit_rel g h k ez ew

end VG.Proof.AesGcm.RISCV64.DirectGather
