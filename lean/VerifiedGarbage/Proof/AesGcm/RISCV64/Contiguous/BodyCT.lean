module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.BodyResult
import VerifiedGarbage.Proof.AesGcm.RISCV64.Contiguous.Timing
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTSeal
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Gather.RISCV64.LoopCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Impl.AesGcm.RISCV64.Contiguous

/-! # Constant-time execution of the contiguous RISC-V seal body -/

public section
namespace VG.Proof.AesGcm.RISCV64.Contiguous
open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Impl.AesGcm.RISCV64.Contiguous
open VG.Proof.Gather.RISCV64 (Eq2 TT rel_seq rel_taint)

private abbrev AadIn (p : Args) (s : State) :=
  OneI p.ctx p.work p.sp p.rounds p.iv p.ivLen.toNat p.aad p.aadLen p.src p.len s ∧
    s.gpr .s4=p.iv ∧ s.gpr .s5=BitVec.ofNat 64 p.ivLen.toNat

private theorem BeforeAad.aadIn {p : Args} {s t : State} (e : BeforeAad p s t) (h : ArgsAt p s) : AadIn p t :=
  ⟨⟨p.regs false,rfl,rfl,rfl,rfl,by simp [Args.regs],rfl,rfl,e.env,
    h.ivRead.of_eq e.keeps.rd e.keeps.wr e.keeps.sp,h.aadRead.of_eq e.keeps.rd e.keeps.wr e.keeps.sp,
    h.srcRead.of_eq e.keeps.rd e.keeps.wr e.keeps.sp,e.aad,e.src⟩,e.nonce,by simpa using e.nonceLen⟩

theorem body_rel [VG.Proof.Gcm.RISCV64.GhashLaw] {p : Args} {s t : State} (a : ArgsAt p s) (b : ArgsAt p t) :
    RelCT isa (Eq2 s t) body TT := by
  have spin := a.sp.trans b.sp.symm
  unfold body
  refine rel_seq (entry_rel a.shape b.shape spin) (begin_wp a) (begin_wp b) fun x y ex ey => ?_
  have ca : CT (AadIn p) oneAad := oneAad_ct a.lay
  have cr : RelCT isa (Eq2 x y) oneAad TT := RelCT.mono ca (fun _ _ ⟨hx,hy⟩ => by
    rw [hx,hy];exact ⟨ex.aadIn a,ey.aadIn b⟩) (fun _ _ _ => trivial)
  refine rel_seq cr (aad_wp a ex) (aad_wp b ey) fun u v ux vy => ?_
  obtain ⟨_,au⟩ := ux.auth
  obtain ⟨_,av⟩ := vy.auth
  have argsCT : RelCT isa (Eq2 u v) (.block (payloadArgs ++ [.li .t0 241])) TT := by
    refine rel_taint [.s0] (au.env.sp.trans av.env.sp.symm) ?_ (by taint_decide)
    intro r hr;obtain rfl := List.mem_singleton.mp hr
    exact (au.env.fr .s0 (by decide)).trans (av.env.fr .s0 (by decide)).symm
  refine rel_seq argsCT (prepare_wp a ux) (prepare_wp b vy) fun u v eu ev => ?_
  refine rel_seq (payload_rel a.lay eu.payload ev.payload eu.cut ev.cut rfl
    (a.aadRead.of_eq eu.keeps.rd eu.keeps.wr eu.keeps.sp) (b.aadRead.of_eq ev.keeps.rd ev.keeps.wr ev.keeps.sp) eu.aad ev.aad)
    (WP.with_rdwr' (payload_wp a.lay eu.payload eu.cut)) (WP.with_rdwr' (payload_wp b.lay ev.payload ev.cut))
    fun i j ⟨oi,ri,wi⟩ ⟨oj,rj,wj⟩ => exit_rel (exitArgs a eu oi ri wi) (exitArgs b ev oj rj wj)
      (oi.env.sp.trans oj.env.sp.symm)

end VG.Proof.AesGcm.RISCV64.Contiguous
