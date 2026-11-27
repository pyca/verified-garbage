module

public import VerifiedGarbage.Proof.AesGcm.X86.DirectGather.Whole
import VerifiedGarbage.Proof.AesGcm.X86.CryptWhole
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Impl.AesGcm.X86
meta import VerifiedGarbage.Proof.AesGcm.X86.Callee
meta import VerifiedGarbage.TCB.X86.Isa
meta import VerifiedGarbage.TCB.X86.State

/-! Trace agreement for the calls processing whole CTR blocks. The public
quantities here are buffer addresses, lengths, and round count. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86.DirectGather
open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86

variable {N : Nat}

structure WholePre (N : Nat) (C St W SP D T : BitVec 32) (n R : Nat) (s : State) : Prop where
  env : Env N C St W SP s
  access : PieceAccess s SP D T n
  rounds : RoundsAt s.mem W R
  src : slotv s.mem W dataO = D
  len : slotv s.mem W lenO = BitVec.ofNat 32 n

private structure Split (N : Nat) (C St W SP D T : BitVec 32) (n R : Nat) (s : State) : Prop extends WholePre N C St W SP D T n R s where
  bx : s.gpr .ebx=D
  di : s.gpr .edi=BitVec.ofNat 32 (n/16)
  zf : s.zf=some (decide (n/16=0))

theorem wholeTo_ct (v : GcmImpl) [WSize N v.ctr.scr] {C St W SP D T : BitVec 32} {n R : Nat}
    (L : Lay N C St W SP 32) (st : St=W+16#32) (P : PieceRegions N C W SP D T n) (hlt : n < 2^32) :
    CT (WholePre N C St W SP D T n R) (Open.wholeTo v.callees.ctr) := by
  refine CT.seq (J:=Split N C St W SP D T n R) (CT.taint [.ebp] (fun s₁ s₂ a b r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact a.env.ebp.trans b.env.ebp.symm) (by taint_decide)) ?_ ?_
  · intro s h
    have sh := shr4 hlt
    refine WP.of_runBlock ⟨_,by xrun [h.env.ebp,L.aW,h.env.wIn',h.src,h.len],?_⟩
    refine ⟨⟨⟨h.env.ebp,h.env.esi,h.env.esp,h.env.ctxR,h.env.stW,h.env.wW,h.env.ctx⟩,
      ⟨h.access.dstArg,h.access.argR,h.access.rd,h.access.wr⟩,h.rounds,h.src,h.len⟩,rfl,sh,?_⟩
    simp only [sh]
    exact congrArg some (and_self_beq32 (by omega_using [hlt]))
  refine CT.ite (decide (n/16=0)) (fun _ h => h.zf) (fun _ => CT.nil) (fun _ => ?_)
  refine CT.seq (J:=fun s => CtrToCall v.ctr.scr s C (St+48#32) D (W+512#32) T R (n/16) ∧ s.gpr .esp=SP)
    (CT.taint [.ebp,.esi] (fun s₁ s₂ a b r hr => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl | rfl
      · exact a.env.ebp.trans b.env.ebp.symm
      · exact a.env.esi.trans b.env.esi.symm) (by taint_decide)) ?_ ?_
  · intro s h
    obtain ⟨u,run,ax,cx,dx,bp,g,m,rd,wr⟩ := ctrArgs_ok L h.env h.rounds
    have sp := (g .esp (by decide) (by decide) (by decide) (by decide)).trans h.env.esp
    exact WP.of_runBlock ⟨u,run,pieceCall v L st h.env P h.access h.rounds ax cx dx
      ((g _ (by decide) (by decide) (by decide) (by decide)).trans h.bx)
      ((g _ (by decide) (by decide) (by decide) (by decide)).trans h.di) bp sp m rd wr,sp⟩
  refine CT.seq (J:=fun s => s.gpr .ebp=W+512#32) (ctrTo_ct v fun _ h => h)
    (fun _ h => WP.mono (ctrTo_call v h.1) (fun _ g => (g.saved .ebp (by decide)).trans h.1.ebp)) ?_
  exact CT.taint [.ebp] (fun s₁ s₂ a b r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact a.trans b.symm) (by taint_decide)

end VG.Proof.AesGcm.X86.DirectGather
