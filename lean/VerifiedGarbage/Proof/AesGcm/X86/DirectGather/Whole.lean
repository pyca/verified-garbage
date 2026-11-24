module

public import VerifiedGarbage.Proof.AesGcm.X86.OpenTo.Verified
public import VerifiedGarbage.Proof.AesGcm.X86.Crypt
import VerifiedGarbage.Proof.AesGcm.X86.CryptWhole
import VerifiedGarbage.Proof.Framework.X86.RegUpd

/-! Whole CTR blocks in a gather piece. Its starting counter can follow any
number of blocks already consumed by earlier pieces. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86.DirectGather

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86
open VG.Spec.Gcm (Block aesWith)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm (xorKs)

variable {N : Nat}

structure PieceRegions (N : Nat) (C W SP D T : BitVec 32) (n : Nat) : Prop where
  srcWork : (⟨w64 D,n⟩ : Region).Disjoint ⟨w64 W,N⟩
  dstWork : (⟨w64 T,n⟩ : Region).Disjoint ⟨w64 W,N⟩
  dstCtx : (⟨w64 C,256⟩ : Region).Disjoint ⟨w64 T,n⟩
  srcDst : (⟨w64 D,n⟩ : Region).Disjoint ⟨w64 T,n⟩
  stackSrc : (below SP 32).Disjoint ⟨w64 D,n⟩
  stackDst : (below SP 32).Disjoint ⟨w64 T,n⟩
  argWork : (⟨w64 SP,4⟩ : Region).Disjoint ⟨w64 W,N⟩
  argDst : (⟨w64 SP,4⟩ : Region).Disjoint ⟨w64 T,n⟩
  fSP : SP.toNat+4 ≤ 2^32
  fD : D.toNat+n ≤ 2^32
  fT : T.toNat+n ≤ 2^32

structure PieceAccess (s : State) (SP D T : BitVec 32) (n : Nat) : Prop where
  dstArg : s.mem.readW (w64 SP) 32 = T
  argR : Covers [⟨w64 SP,4⟩] (s.rd++s.wr)
  rd : Covers [⟨w64 D,n⟩] (s.rd++s.wr)
  wr : Covers [⟨w64 T,n⟩] s.wr

theorem pieceCall (v : GcmImpl) [ws : WSize N v.ctr.scr] {C St W SP D T : BitVec 32} {s u : State} {n R : Nat}
    (L : Lay N C St W SP 32) (st : St = W+16#32) (E : Env N C St W SP s)
    (P : PieceRegions N C W SP D T n) (A : PieceAccess s SP D T n) (r : RoundsAt s.mem W R)
    (ax : u.gpr .eax = C) (cx : u.gpr .ecx = BitVec.ofNat 32 R) (dx : u.gpr .edx = St+48#32)
    (bx : u.gpr .ebx = D) (di : u.gpr .edi = BitVec.ofNat 32 (n/16)) (bp : u.gpr .ebp = W+512#32)
    (sp : u.gpr .esp = SP) (m : u.mem = s.mem) (rd : u.rd = s.rd) (wr : u.wr = s.wr) :
    CtrToCall v.ctr.scr u C (St+48#32) D (W+512#32) T R (n/16) := by
  have hk : 16 * (n/16) ≤ n := Nat.mul_div_le _ _
  have kw := L.aW (o:=512) (by decide)
  -- The implementation's working space, the first bytes of the callees'.
  have hS : Region.Sub ⟨w64 W + BitVec.ofNat 64 512, v.ctr.scr⟩ ⟨w64 W, N⟩ := Lay.scrSub ws.hB
  have cw : Region.Sub ⟨w64 (St+48#32),16⟩ ⟨w64 W,N⟩ := by
    rw [st,BitVec.add_assoc]
    change Region.Sub ⟨w64 (W+64#32),16⟩ _
    rw [L.aW (by decide)]
    exact Lay.wSub (by decide)
  have k28 := L.below_sub (k:=28) (by decide)
  refine ⟨ax,cx,dx,bx,di,bp,by rw [sp,m,A.dstArg],r.2,by rw [sp]; exact Nat.le_trans (by decide) L.sp,
    by rw [sp]; exact P.fSP,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (L.cw.sub_left (Region.sub_prefix (by decide))).sub_right cw
  · exact (P.dstCtx.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix hk)
  · rw [kw]; exact (L.cw.sub_left (Region.sub_prefix (by decide))).sub_right hS
  · exact ((P.dstWork.sub_left (Region.sub_prefix hk)).sub_right cw).symm
  · rw [kw,L.aS (by decide)]; exact (L.st_hi (by decide)).sub_right (Lay.hiPre ws.hB)
  · rw [kw]; exact (P.dstWork.sub_left (Region.sub_prefix hk)).sub_right hS
  · exact (P.srcWork.sub_left (Region.sub_prefix hk)).sub_right cw
  · exact (P.srcDst.sub_left (Region.sub_prefix hk)).sub_right (Region.sub_prefix hk)
  · rw [kw]; exact (P.srcWork.sub_left (Region.sub_prefix hk)).sub_right hS
  · rw [sp]; exact (L.kc.sub_right (Region.sub_prefix (by decide))).sub_left k28
  · rw [sp]; exact (L.kw.sub_right cw).sub_left k28
  · rw [sp]; exact (P.stackSrc.sub_right (Region.sub_prefix hk)).sub_left k28
  · rw [sp]; exact (P.stackDst.sub_right (Region.sub_prefix hk)).sub_left k28
  · rw [sp,kw]; exact (L.kw.sub_right hS).sub_left k28
  · rw [sp]; exact P.argWork.sub_right cw
  · rw [sp]; exact P.argDst.sub_right (Region.sub_prefix hk)
  · rw [sp,kw]; exact P.argWork.sub_right hS
  · have h := L.fc; omega_using [h]
  · rw [L.nS (by decide)]; have h := L.fs; omega_using [h]
  · have h := P.fD; omega_using [hk,h]
  · have h := P.fT; omega_using [hk,h]
  · rw [L.nW (by decide)]; have h := L.fw; have hB := ws.hB; omega_using [h, hB]
  · rw [rd,wr,sp]; exact A.argR
  · rw [rd,wr]; exact covers_cons (covers_pre E.ctxR (by decide) (by decide))
      (covers_cons (covers_pre A.rd hk (by have h := P.fD; omega_using [h])) covers_nil)
  · rw [wr,kw,L.aS (by decide)]; exact covers_cons (E.stC (by decide))
      (covers_cons (covers_pre A.wr hk (by have h := P.fT; omega_using [h]))
        (covers_cons (covers_off E.wW ws.hB L.nlt) covers_nil))

abbrev wholeFrame (N : Nat) (St W SP T : BitVec 32) (nb : Nat) : List Region :=
  [⟨w64 (St+48#32),16⟩,⟨w64 T,16*nb⟩,⟨w64 (W+512#32),N-512⟩,below SP 28]

structure WholePost (N : Nat) (s : State) (St W SP D T : BitVec 32) (ciph : Block → Block) (icb : Block)
    (off nb : Nat) (t : State) : Prop where
  bp : t.gpr .ebp = W
  si : t.gpr .esi = St
  sp : t.gpr .esp = SP
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (wholeFrame N St W SP T nb) s.mem t.mem
  out : bytesAt t.mem (w64 T) (16*nb) = xorKs ciph icb off (bytesAt s.mem (w64 D) (16*nb))
  ctr : CtrS t.mem St ciph icb (off+16*nb)

/-- A whole-block CTR call with independent input/output buffers advances the
stream position supplied by the gather loop. -/
theorem wholeCall_ok (v : GcmImpl) [ws : WSize N v.ctr.scr] {C St W SP D T : BitVec 32} {s : State} {n R off : Nat}
    {ciph : Block → Block} {icb : Block} (L : Lay N C St W SP 32) (st : St = W+16#32) (E : Env N C St W SP s)
    (P : PieceRegions N C W SP D T n) (A : PieceAccess s SP D T n) (r : RoundsAt s.mem W R)
    (bx : s.gpr .ebx = D) (di : s.gpr .edi = BitVec.ofNat 32 (n/16)) (aligned : off%16 = 0)
    (cipher : Spec.Gcm.ctxCiph s.mem (w64 C) R = ciph) (ctr : CtrS s.mem St ciph icb off) :
    WP isa (.seq (.block ctrArgs) (.seq (Open.ctrToCall ⟨v.ctr.callee.name,v.ctr.callee.code⟩) (.block unscr)))
      s (WholePost N s St W SP D T ciph icb off (n/16)) := by
  obtain ⟨u,run,ax,cx,dx,bp,g,m,rd,wr⟩ := ctrArgs_ok L E r
  obtain sp := (g .esp (by decide) (by decide) (by decide) (by decide)).trans E.esp
  obtain call := pieceCall v L st E P A r ax cx dx ((g _ (by decide) (by decide) (by decide) (by decide)).trans bx)
    ((g _ (by decide) (by decide) (by decide) (by decide)).trans di) bp sp m rd wr
  refine WP.seq (WP.of_runBlock ⟨u,run,?_⟩)
  refine WP.seq (WP.mono (ctrTo_call v call) ?_)
  intro t ht
  have bp₂ := (ht.saved .ebp (by decide)).trans bp
  have sp₂ := (ht.saved .esp (by decide)).trans sp
  have si₂ := (ht.saved .esi (by decide)).trans ((g _ (by decide) (by decide) (by decide) (by decide)).trans E.esi)
  have out := ht.out
  have count := ht.ctr
  have cipher' : aesWith R (bytesAt u.mem (w64 C) (16*(R+1))) = ciph := by rw [m]; exact cipher
  rw [cipher',m,L.aS (by decide)] at out
  rw [m,L.aS (by decide)] at count
  obtain ⟨out',ctr'⟩ := OpenTo.ctr_whole_to ctr aligned out count
  refine WP.of_runBlock ⟨_,by xrun [unscr,bp₂],?_⟩
  refine ⟨?_,si₂,sp₂,ht.rd.trans rd,ht.wr.trans wr,?_,out',ctr'⟩
  · regs [bp₂]
    exact BitVec.add_sub_cancel _ _
  · have f := ht.frame; rw [m,sp] at f
    exact f.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
          Region.sub_prefix (by have hB := ws.hB; omega_using [hB])⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))),
          fun _ h => h⟩

theorem wholeTo_ok (v : GcmImpl) [WSize N v.ctr.scr] {C St W SP D T : BitVec 32} {s : State} {n R off : Nat}
    {ciph : Block → Block} {icb : Block} (L : Lay N C St W SP 32) (st : St = W+16#32) (E : Env N C St W SP s)
    (P : PieceRegions N C W SP D T n) (A : PieceAccess s SP D T n) (r : RoundsAt s.mem W R)
    (src : slotv s.mem W dataO = D) (len : slotv s.mem W lenO = BitVec.ofNat 32 n) (hlt : n < 2^32)
    (aligned : n/16 ≠ 0 → off%16 = 0) (cipher : Spec.Gcm.ctxCiph s.mem (w64 C) R = ciph) (ctr : CtrS s.mem St ciph icb off) :
    WP isa (Open.wholeTo ⟨v.ctr.callee.name,v.ctr.callee.code⟩) s (WholePost N s St W SP D T ciph icb off (n/16)) := by
  have sh := shr4 hlt
  refine WP.seq (WP.of_runBlock ⟨_,by xrun [E.ebp,L.aW,E.wIn',src,len],?_⟩)
  refine WP.ite (decide (n/16=0)) (by simp only [sh];
                                         exact congrArg some (and_self_beq32 (by omega_using [hlt]))) (fun z => ?_) (fun nz => ?_)
  · have h0 : n/16=0 := by simpa using z
    refine WP.block_nil ?_
    rw [h0]
    exact ⟨E.ebp,E.esi,E.esp,rfl,rfl,Frame.refl _ _,rfl,ctr⟩
  · let m := BitVec.ofNat 32 n
    let q := m >>> 4
    let u := arithFlags ((((s.setReg .ebx D).setReg .edi m).setFlags (some (m.getLsbD 3)) none
      (some (q == 0)) (some q.msb)).setReg .edi q) (q &&& q) false false
    have env : Env N C St W SP u := ⟨E.ebp,E.esi,E.esp,E.ctxR,E.stW,E.wW,E.ctx⟩
    have acc : PieceAccess u SP D T n := ⟨A.dstArg,A.argR,A.rd,A.wr⟩
    refine WP.mono (wholeCall_ok v L st env P acc r rfl sh (aligned (by simpa using nz)) cipher ctr) ?_
    intro t h
    exact ⟨h.bp,h.si,h.sp,h.rd,h.wr,h.frame,h.out,h.ctr⟩

end VG.Proof.AesGcm.X86.DirectGather
