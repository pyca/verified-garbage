module

public import VerifiedGarbage.Proof.AesGcm.X86.DirectGather.WholeCT
public import VerifiedGarbage.Proof.AesGcm.X86.DirectGather.Crypt
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Impl.AesGcm.X86
meta import VerifiedGarbage.Proof.AesGcm.X86.Callee
meta import VerifiedGarbage.TCB.X86.Isa
meta import VerifiedGarbage.TCB.X86.State

/-! Trace agreement for a gather piece's aligned remainder. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86.DirectGather

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86
open VG.Spec.Gcm (Block)

theorem xorTo_ct {K D T : BitVec 32} {n : Nat} {I : State → Prop}
    (req : ∀ s, I s → s.gpr .edx=K ∧ s.gpr .esi=D ∧ s.gpr .edi=T ∧ s.gpr .ecx=BitVec.ofNat 32 n) :
    CT I (xorLoopG true) := by
  refine CT.taint [.edx,.esi,.edi,.ecx] ?_ (by taint_decide)
  intro a b a₀ b₀ r hr
  obtain ⟨a₁,a₂,a₃,a₄⟩ := req a a₀
  obtain ⟨b₁,b₂,b₃,b₄⟩ := req b b₀
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [a₁.trans b₁.symm,a₂.trans b₂.symm,a₃.trans b₃.symm,a₄.trans b₄.symm]

private structure XorAt (W K D T : BitVec 32) (n : Nat) (s : State) : Prop where
  wp : XorPreG true s K D T n
  bp : s.gpr .ebp=W

theorem xorTail_ct {C St W SP D T : BitVec 32} {n R : Nat} (L : Lay C St W SP 32) (st : St=W+16#32)
    (P : PieceRegions C W SP D T n) (hlt : n<2^32) (nz : n%16 ≠ 0) :
    CT (WholePre C St W SP D T n R) (.seq (.block Open.tailRegs) (.seq (xorLoopG true)
      (.block [.mov .esi (.reg .ebp),.alu .add .esi (imm stO)]))) := by
  refine CT.seq (J:=XorAt W (St+64#32) (tailPtr D n) (tailPtr T n) (n%16)) (CT.taint [.esp,.ebp,.esi]
    (fun _ _ a b r hr => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [a.env.esp.trans b.env.esp.symm,a.env.ebp.trans b.env.ebp.symm,a.env.esi.trans b.env.esi.symm]) (by taint_decide)) ?_ ?_
  · intro s h
    refine WP.mono (tailCursors_ok L h.env h.src h.len h.access.dstArg
      (by simpa using in_off h.access.argR (d:=0) (n:=4) (by decide) (by decide)) hlt) ?_
    rintro u ⟨dx,di,si,cx,bp,sp,m,rd,wr⟩
    have fd := P.fD
    have ft := P.fT
    have d : w64 (tailPtr D n) = w64 D+BitVec.ofNat 64 (16*(n/16)) := w64_add (by omega_using [fd,nz])
    have t : w64 (tailPtr T n) = w64 T+BitVec.ofNat 64 (16*(n/16)) := w64_add (by omega_using [ft,nz])
    have ds : Region.Sub ⟨w64 (tailPtr D n),n%16⟩ ⟨w64 D,n⟩ := by rw [d]; exact Offset.sub_base _ (by omega_using [])
    have ts : Region.Sub ⟨w64 (tailPtr T n),n%16⟩ ⟨w64 T,n⟩ := by rw [t]; exact Offset.sub_base _ (by omega_using [])
    have ks : Region.Sub ⟨w64 (St+64#32),n%16⟩ ⟨w64 W,2560⟩ := by
      rw [L.aS (by decide)]; exact fun _ q => stSub L st _ (Lay.stSub (by omega_using []) _ q)
    exact ⟨⟨dx,di,si,(fun e => nomatch e),cx,by omega_using [nz],by omega_using [],
      by rw [L.nS (by decide)]; have f:=L.fs; omega_using [f],
      by unfold tailPtr; rw [toNat_add32 (by omega_using [fd,nz])]; omega_using [fd],
      by unfold tailPtr; rw [toNat_add32 (by omega_using [ft,nz])]; omega_using [ft],
      by rw [rd,wr,L.aS (by decide)]; exact covers_left (h.env.stC (by omega_using [])),
      by rw [rd,wr,d]; exact covers_off h.access.rd (by omega_using []) (by omega_using [hlt]),
      by rw [wr,t]; exact covers_off h.access.wr (by omega_using []) (by omega_using [hlt]),
      ((P.dstWork.sub_left ts).sub_right ks).symm,P.srcDst.imp (congrArg (fun p => tailPtr p n)) (fun hd => (hd.sub_left ds).sub_right ts)⟩,bp⟩
  refine CT.seq (J:=fun s => s.gpr .ebp=W) (xorTo_ct (fun _ h => ⟨h.wp.edx,h.wp.src,h.wp.edi,h.wp.ecx⟩))
    (fun s h => WP.mono (xorLoopG_ok true s h.wp) fun t a => (a.other _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h.bp) ?_
  exact CT.taint [.ebp] (fun _ _ a b r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact a.trans b.symm) (by taint_decide)

structure AlignedPre (C St W SP D T : BitVec 32) (n R off : Nat) (s : State) : Prop extends WholePre C St W SP D T n R s where
  stream : ∃ icb : Block, CtrS s.mem St (ciphOf s.mem C R) icb off

private theorem afterWhole {C St W SP D T : BitVec 32} {n R off : Nat} {s t : State} {icb : Block}
    (L : Lay C St W SP 32) (st : St=W+16#32) (P : PieceRegions C W SP D T n)
    (h : WholePre C St W SP D T n R s) (done : WholePost s St W SP D T (ciphOf s.mem C R) icb off (n/16) t) :
    AlignedPre C St W SP D T n R (off+16*(n/16)) t := by
  have dw := h.access.dataW L st P
  have f := whole_crFrame L done.frame
  have rounds := rounds_frame f (kept_crFrame L dw) h.rounds
  obtain c := ciph_crFrame L dw f h.rounds.2
  exact ⟨⟨env_crFrame L dw h.env f (done.bp.trans h.env.ebp.symm) (done.si.trans h.env.esi.symm)
    (done.sp.trans h.env.esp.symm) done.rd done.wr,afterAccess L st P h.access done.rd done.wr f,
    rounds,(keptSlot L st P h.access f (by decide) (by decide)).trans h.src,
    (keptSlot L st P h.access f (by decide) (by decide)).trans h.len⟩,icb,by rw [c]; exact done.ctr⟩

theorem decTo_ct (v : GcmImpl) {C St W SP D T : BitVec 32} {n R off : Nat}
    (L : Lay C St W SP 32) (st : St=W+16#32) (P : PieceRegions C W SP D T n) (hlt : n<2^32)
    (aligned : n≠0 → off%16=0) :
    CT (AlignedPre C St W SP D T n R off) (Open.decTo v.callees v.callees.ctr) := by
  let J := AlignedPre C St W SP D T n R (off+16*(n/16))
  refine CT.seq (J:=J) ((wholeTo_ct v L st P hlt).mono fun _ h => h.toWholePre) ?_ ?_
  · intro s h
    obtain ⟨icb,ctr⟩ := h.stream
    exact WP.mono (wholeTo_ok v L st h.env P h.access h.rounds h.src h.len hlt
      (fun nz => aligned (by omega_using [nz])) rfl ctr) (fun _ done => afterWhole L st P h.toWholePre done)
  refine CT.seq (J:=fun s => J s ∧ s.zf=some (decide (n%16=0))) (CT.taint [.ebp] (fun _ _ a b r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact a.env.ebp.trans b.env.ebp.symm) (by taint_decide)) ?_ ?_
  · intro s h
    refine WP.mono (tailTest L h.env h.len hlt) ?_
    rintro t ⟨z,e,m,rd,wr⟩
    exact ⟨⟨⟨e,⟨by rw [m]; exact h.access.dstArg,by rw [rd,wr]; exact h.access.argR,
      by rw [rd,wr]; exact h.access.rd,by rw [wr]; exact h.access.wr⟩,by rw [m]; exact h.rounds,
      by rw [m]; exact h.src,by rw [m]; exact h.len⟩,by rw [m]; exact h.stream⟩,z⟩
  refine CT.ite (decide (n%16=0)) (fun _ h => h.2) (fun _ => CT.nil) (fun h₀ => ?_)
  have nz : n%16 ≠ 0 := by simpa using h₀
  refine CT.seq (J:=WholePre C St W SP D T n R) ?_ ?_ (xorTail_ct L st P hlt nz)
  · refine CT.seq (J:=CtrReady C St W SP R (St+48#32) (St+64#32) 1)
      (CT.taint [.ebp,.esi] (fun _ _ a b r hr => by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl | rfl
        · exact a.1.env.ebp.trans b.1.env.ebp.symm
        · exact a.1.env.esi.trans b.1.env.esi.symm) (by taint_decide)) ?_ (ctrW_ct (vg:=v) L rfl)
    exact fun _ h => WP.mono (ksReady L rfl h.1.env h.1.rounds) fun _ g => g.2.1
  · intro s h
    obtain ⟨icb,ctr⟩ := h.1.stream
    refine WP.mono (keyStream_ok v L h.1.env h.1.rounds rfl ctr
      (by have a:=aligned (by omega_using [nz]); omega_using [a]) (k:=n%16) (by omega_using []) nz) ?_
    intro t done
    have f := ksFrame_crFrame L rfl (D:=T) (n:=n) done.frame
    have a := h.1.access
    exact ⟨done.env,afterAccess L st P a done.rd done.wr f,rounds_frame f (kept_crFrame L (a.dataW L st P)) h.1.rounds,
      (keptSlot L st P a f (by decide) (by decide)).trans h.1.src,(keptSlot L st P a f (by decide) (by decide)).trans h.1.len⟩

end VG.Proof.AesGcm.X86.DirectGather
