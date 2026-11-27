module

public import VerifiedGarbage.Proof.AesGcm.X86.DirectGather.CryptCT
public import VerifiedGarbage.Proof.AesGcm.X86.DirectGather.Piece
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Impl.AesGcm.X86.DirectGather
meta import VerifiedGarbage.Proof.AesGcm.X86.Callee
meta import VerifiedGarbage.TCB.X86.Isa
meta import VerifiedGarbage.TCB.X86.State

/-! Constant-time consumption of a previously generated keystream suffix. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86.DirectGather
open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86
open VG.Impl.AesGcm.X86.DirectGather (partialHead headArgs headDone)
open VG.Spec.Gcm (Block)

variable {N : Nat}

private structure MinState (N : Nat) (C St W SP D T : BitVec 32) (n off : Nat) (s : State) : Prop where
  env : Env N C St W SP s
  bO : slotv s.mem W bO = BitVec.ofNat 32 (off%16)
  len : slotv s.mem W lenO = BitVec.ofNat 32 n
  src : slotv s.mem W dataO = D
  di : s.gpr .edi=T
  cx : s.gpr .ecx = BitVec.ofNat 32 (min (16-off%16) n)
  access : min (16-off%16) n ≠ 0 → HeadAccess s St SP D T (off%16) (min (16-off%16) n)

private structure PendingXor (St W SP D T : BitVec 32) (b k : Nat) (s : State) : Prop where
  xor : XorPreG true s (headKey St b) D T k
  bp : s.gpr .ebp=W
  sp : s.gpr .esp=SP

theorem headPart_ct {I : State → Prop} {C St W SP D T : BitVec 32} {n off : Nat}
    (L : Lay N C St W SP 32) (hlt : n<2^32) (args : ∀ s, I s → PieceArgs N C St W SP D T s n off)
    (access : ∀ s, I s → min (16-off%16) n ≠ 0 → HeadAccess s St SP D T (off%16) (min (16-off%16) n)) :
    CT I (.ite .e (.block []) partialHead) := by
  refine CT.ite (decide (off%16=0)) (fun s h => (args s h).zf) (fun _ => CT.nil) (fun _ => ?_)
  let k := min (16-off%16) n
  have kn : k ≤ n := Nat.min_le_right _ _
  have klim : k<2^32 := Nat.lt_of_le_of_lt kn hlt
  refine CT.seq (J:=MinState N C St W SP D T n off) (minLen_ct (N:=N) (n:=n) (b:=off%16) (W:=W) (fun s h => ?_)) ?_ ?_
  · have x := args s h
    exact ⟨x.env.ebp,C,St,SP,32,L,x.env,x.nO,x.bO,by omega_using [],hlt⟩
  · intro s h
    have x := args s h
    refine WP.mono (minLen_ok L x.env x.nO x.bO (by omega_using []) hlt) ?_
    intro t done
    have e := x.env.keep (done.other .ebp (by decide) (by decide)) (done.other .esi (by decide) (by decide))
      (done.other .esp (by decide) (by decide)) done.rd done.wr (by rw [done.mem])
    refine ⟨e,by rw [done.mem]; exact x.bO,by rw [done.mem]; exact x.len,by rw [done.mem]; exact x.src,
      (done.other .edi (by decide) (by decide)).trans x.di,done.ecx,?_⟩
    intro nz
    have a := access s h nz
    exact ⟨a.fK,a.fS,a.fD,by rw [done.rd,done.wr]; exact a.rd,by rw [done.rd,done.wr]; exact a.rdS,
      by rw [done.wr]; exact a.wr,by rw [done.wr]; exact a.stack,a.disj,a.sd⟩
  refine CT.seq (J:=fun s => MinState N C St W SP D T n off s ∧ s.zf=some (decide (k=0)))
    (CT.taint [] (fun _ _ _ _ r hr => nomatch hr) (by taint_decide)) ?_ ?_
  · intro s h
    refine WP.of_runBlock ⟨_,by xrun [h.cx],?_⟩
    exact ⟨⟨⟨h.env.ebp,h.env.esi,h.env.esp,h.env.ctxR,h.env.stW,h.env.wW,h.env.ctx⟩,
      h.bO,h.len,h.src,h.di,h.cx,fun nz => by
        have a := h.access nz
        exact ⟨a.fK,a.fS,a.fD,a.rd,a.rdS,a.wr,a.stack,a.disj,a.sd⟩⟩,congrArg some (and_self_beq32 klim)⟩
  refine CT.ite (decide (k=0)) (fun _ h => h.2) (fun _ => CT.nil) (fun nonzero => ?_)
  have nz : k≠0 := by simpa using nonzero
  refine CT.seq (J:=PendingXor St W SP D T (off%16) k) (CT.taint [.ebp] (fun _ _ a b r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact a.1.env.ebp.trans b.1.env.ebp.symm) (by taint_decide)) ?_ ?_
  · intro s h
    have x := h.1
    have a := x.access nz
    refine WP.mono (headArgs_ok L x.env x.bO x.len x.src x.cx x.di kn hlt) ?_
    rintro t ⟨m,dx,si,di,cx,bp,sp,rd,wr⟩
    exact ⟨⟨dx,di,si,(fun e => nomatch e),cx,Nat.pos_of_ne_zero nz,klim,a.fK,a.fS,a.fD,
      by rw [rd,wr]; exact a.rd,by rw [rd,wr]; exact a.rdS,by rw [wr]; exact a.wr,a.disj,a.sd⟩,bp,sp⟩
  refine CT.seq (J:=fun s => s.gpr .ebp=W ∧ s.gpr .esp=SP)
    (xorTo_ct fun _ h => ⟨h.xor.edx,h.xor.src,h.xor.edi,h.xor.ecx⟩) ?_ ?_
  · exact fun s h => WP.mono (xorLoopG_ok true s h.xor) fun t g => ⟨(g.other _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans h.bp,(g.other _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans h.sp⟩
  · exact CT.taint [.ebp,.esp] (fun _ _ a b r hr => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl | rfl
      exacts [a.1.trans b.1.symm,a.2.trans b.2.symm]) (by taint_decide)

theorem empty_ct (v : GcmImpl) {C St W SP : BitVec 32} (L : Lay N C St W SP 32) :
    CT (fun s => Env N C St W SP s ∧ slotv s.mem W lenO=0#32) (Open.decTo v.callees v.callees.ctr) := by
  let I := fun s => Env N C St W SP s ∧ slotv s.mem W lenO=0#32
  let J := fun s => I s ∧ s.zf=some true
  have b : ∀ s, J s → isa.eval .e s=some true := fun _ h => h.2
  refine CT.seq (J:=I) ?_ ?_ ?_
  · refine CT.seq (J:=J) (CT.taint [.ebp] (fun _ _ a b r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact a.1.ebp.trans b.1.ebp.symm) (by taint_decide)) ?_
      (CT.ite true b (fun _ => CT.nil) (fun f => nomatch f))
    intro s ⟨e,len⟩
    refine WP.of_runBlock ⟨_,by xrun [e.ebp,L.aW,e.wIn',len],?_⟩
    exact ⟨⟨⟨e.ebp,e.esi,e.esp,e.ctxR,e.stW,e.wW,e.ctx⟩,len⟩,rfl⟩
  · intro s ⟨e,len⟩
    refine WP.seq (WP.of_runBlock ⟨_,by xrun [e.ebp,L.aW,e.wIn',len],?_⟩)
    exact WP.ite true rfl (fun _ => WP.block_nil ⟨⟨e.ebp,e.esi,e.esp,e.ctxR,e.stW,e.wW,e.ctx⟩,len⟩) (fun f => nomatch f)
  · refine CT.seq (J:=J) (CT.taint [.ebp] (fun _ _ a b r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact a.1.ebp.trans b.1.ebp.symm) (by taint_decide)) ?_
      (CT.ite true b (fun _ => CT.nil) (fun f => nomatch f))
    intro s ⟨e,len⟩
    refine WP.of_runBlock ⟨_,by xrun [Open.tailLen,e.ebp,L.aW,e.wIn',len],?_⟩
    exact ⟨⟨⟨e.ebp,e.esi,e.esp,e.ctxR,e.stW,e.wW,e.ctx⟩,len⟩,rfl⟩

theorem emptyPiece_ct (v : GcmImpl) {C St W SP D T : BitVec 32} {off : Nat} (L : Lay N C St W SP 32) :
    CT (fun s => PieceArgs N C St W SP D T s 0 off)
      (.seq (.ite .e (.block []) partialHead) (Open.decTo v.callees v.callees.ctr)) := by
  refine CT.seq (headPart_ct L (by decide) (fun _ h => h) (fun _ _ nz => False.elim (nz (Nat.min_zero _)))) ?_
    (empty_ct v L)
  exact fun _ h => WP.mono (headEmpty_ok L h) fun _ ⟨m,e,_,_⟩ => ⟨e,by rw [m,h.len]⟩

structure StreamPiecePre (N : Nat) (C St W SP D T : BitVec 32) (n R off : Nat) (s : State) : Prop where
  args : PieceArgs N C St W SP D T s n off
  access : PieceAccess s SP D T n
  rounds : RoundsAt s.mem W R
  argW : InRegions s.wr (w64 SP) 4
  stream : ∃ icb : Block, CtrS s.mem St (ciphOf s.mem C R) icb off

theorem processPiece_ct (v : GcmImpl) [WSize N v.ctr.scr] {C St W SP D T : BitVec 32} {n R off : Nat}
    (L : Lay N C St W SP 32) (st : St=W+16#32) (P : PieceRegions N C W SP D T n) (lt : n<2^32)
    (argCtx : (⟨w64 C,256⟩ : Region).Disjoint ⟨w64 SP,4⟩) :
    CT (StreamPiecePre N C St W SP D T n R off) (.seq (.ite .e (.block []) partialHead) (Open.decTo v.callees v.callees.ctr)) := by
  let k := headCount off n
  have kn : k≤n := by unfold k headCount; split <;> first | exact Nat.zero_le _ | exact Nat.min_le_right _ _
  let I := StreamPiecePre N C St W SP D T n R off
  have head : CT I (.ite .e (.block []) partialHead) := headPart_ct L lt (fun _ h => h.args) fun _ h _ =>
    makeHeadAccess L st P h.access h.args.env h.argW (by omega_using []) (by omega_using []) (Nat.min_le_right _ _)
  by_cases eq : k=n
  · refine CT.seq head ?_ (empty_ct v L)
    intro s h₀
    obtain ⟨icb,ctr⟩ := h₀.stream
    refine WP.mono (headPart_ok L st P h₀.access h₀.args h₀.argW lt ctr) ?_
    rintro y ⟨h,bp,si,sp,rd,wr⟩
    exact ⟨h₀.args.env.keep (bp.trans h₀.args.env.ebp.symm) (si.trans h₀.args.env.esi.symm) (sp.trans h₀.args.env.esp.symm)
      rd wr (slot_frame h.frame (slotHead P (by decide) (by decide) kn)),by
        have z : n-k=0 := by omega_using [eq]
        have len:=h.len
        change _ = BitVec.ofNat 32 (n-k) at len
        rwa [z] at len⟩
  · have less : k<n := by omega_using [kn,eq]
    have align : (off+k)%16=0 := by
      by_cases hb : off%16=0
      · simp [k,headCount,hb]
      · simp only [k,headCount,ite_eq_right hb] at less ⊢
        rw [Nat.min_eq_left (by omega_using [less] : 16-off%16 ≤ n)]
        omega_using [hb]
    refine CT.seq head ?_ (decTo_ct (R:=R) v L st (restRegions P less) (by omega_using [lt]) (fun _ => align))
    intro s h₀
    obtain ⟨icb,ctr⟩ := h₀.stream
    refine WP.mono (headPart_ok L st P h₀.access h₀.args h₀.argW lt ctr) ?_
    rintro y ⟨h,bp,si,sp,rd,wr⟩
    have c := ciph_frame h.frame (fun x hx => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; rcases hx with rfl | rfl | rfl
      · exact P.dstCtx.sub_right (Region.sub_prefix kn)
      · exact L.cw.sub_right (Lay.wSub (by decide))
      · exact argCtx) h₀.rounds.2
    refine ⟨⟨h₀.args.env.keep (bp.trans h₀.args.env.ebp.symm) (si.trans h₀.args.env.esi.symm) (sp.trans h₀.args.env.esp.symm)
      rd wr (slot_frame h.frame (slotHead P (by decide) (by decide) kn)),restAccess P h₀.access h less rd wr,
      ⟨(slot_frame h.frame (slotHead P (by decide) (by decide) kn)).trans h₀.rounds.1,h₀.rounds.2⟩,
      h.src,h.len⟩,icb,?_⟩
    rw [c]; exact h.ctr

end VG.Proof.AesGcm.X86.DirectGather
