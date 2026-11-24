module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.PreparedPayload
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.BodyResult
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Impl.AesGcm.RISCV64.Contiguous

/-! # Timing of the public contiguous RISC-V seal for either supported layout -/

public section
namespace VG.Proof.AesGcm.RISCV64.Contiguous
open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64 VG.Impl.AesGcm.RISCV64.Contiguous VG.Impl.Gcm.RISCV64.Prepared
open VG.Proof.Gather.RISCV64 (Eq2 TT rel_taint rel_seq rel_ite)

abbrev callScope (p : Args) := payloadScope (p.regs true) p.sp p.keys p.dst

theorem preparedBody_rel {p : Args} {s t : State} (a : ArgsAt p s) (b : ArgsAt p t)
    (l : callScope p s) (r : callScope p t) : RelCT isa (Eq2 s t) (bodyWith preparedInvocation) TT := by
  have spin := a.sp.trans b.sp.symm
  refine rel_seq (entry_rel a.shape b.shape spin) (begin_wp a) (begin_wp b) fun x y ex ey => ?_
  have sc {v u : State} (q : callScope p v) (e : BeforeAad p v u) : nonceScope (p.regs false) p.sp p.keys u :=
    (q.after e.keeps (e.frame.sub (fun r hr => before_sealSub r (List.mem_cons.mpr (.inl (List.mem_singleton.mp hr)))))).narrow j0_sealSub
  have ji {v u : State} (q : ArgsAt p v) (e : BeforeAad p v u) :
      J0In (p.regs false) p.sp (Spec.Gcm.blockAt u.mem (p.ctx+BitVec.ofNat 64 240)) p.iv p.ivLen.toNat u :=
    ⟨e.env,rfl,e.nonce,by simpa using e.nonceLen,by simp [Args.regs],q.ivRead.of_eq e.keeps.rd e.keeps.wr e.keeps.sp⟩
  have cr := preparedAad_rel (V:=p.regs false) a.lay (ji a ex) (ji b ey)
    (a.aadRead.of_eq ex.keeps.rd ex.keeps.wr ex.keeps.sp) (b.aadRead.of_eq ey.keeps.rd ey.keeps.wr ey.keeps.sp)
    ex.aad ey.aad (sc l ex) (sc r ey)
  refine rel_seq cr (aad_wp a ex l.action) (aad_wp b ey r.action) fun u v ux vy => ?_
  obtain ⟨_,au⟩ := ux.auth
  obtain ⟨_,av⟩ := vy.auth
  have argsCT : RelCT isa (Eq2 u v) (.block (payloadArgs ++ [.li .t0 241])) TT := by
    exact rel_taint [.s0] (au.env.sp.trans av.env.sp.symm) (fun x hx => by
      obtain rfl := List.mem_singleton.mp hx;exact au.env.s0.trans av.env.s0.symm) (by taint_decide)
  refine rel_seq argsCT (prepare_wp a ux) (prepare_wp b vy) fun u v eu ev => ?_
  have lu := l.after eu.keeps (eu.frame.sub before_sealSub)
  have rv := r.after ev.keeps (ev.frame.sub before_sealSub)
  have cmp {z : State} (reg : z.gpr .s5=p.len) (cut : z.gpr .t0=241) :
      isa.eval (.ltu .s5 .t0) z=some (decide (p.len.toNat<241)) := by
    change some (decide (z.gpr .s5 < z.gpr .t0))=_
    rw [reg,cut];rfl
  refine rel_seq (rel_ite (cmp eu.payload.len eu.cut) (cmp ev.payload.len ev.cut)
    (fun small => preparedShort_rel a.lay eu.payload ev.payload (by have := of_decide_eq_true small;exact Nat.le_of_lt_succ this) lu rv)
    (fun _ => preparedLong_rel a.lay eu.payload ev.payload lu rv))
    (WP.with_rdwr' (payload_wp a.lay eu.payload eu.cut lu.action)) (WP.with_rdwr' (payload_wp b.lay ev.payload ev.cut rv.action))
    fun i j ⟨oi,ri,wi⟩ ⟨oj,rj,wj⟩ => exit_rel (exitArgs a eu oi ri wi) (exitArgs b ev oj rj wj)
      (oi.env.sp.trans oj.env.sp.symm)

end VG.Proof.AesGcm.RISCV64.Contiguous
