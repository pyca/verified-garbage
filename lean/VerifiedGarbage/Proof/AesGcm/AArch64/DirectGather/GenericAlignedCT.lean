module

public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.GenericLoop
public import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
import VerifiedGarbage.Proof.AesGcm.AArch64.Env
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.GenericLoop

/-! Equal public offsets and lengths select identical tail loops and CTR calls. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather.Generic

open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Impl.AesGcm.AArch64.DirectGather (aligned leftover)
open VG.Proof.AesGcm.AArch64 (rel_taint rel_seq rel_ite)
variable {Wn : Nat} {Ctx St W SP D O : Addr} {P R n : Nat} {s t : State} {k l : Reg → BitVec 64}

theorem head_rel (a : CrInG Wn true Ctx St W SP k R P D O n s) (b : CrInG Wn true Ctx St W SP l R P D O n t) :
    RelCT isa (Eq2 s t) leftover TT :=
  rel_taint [.x20,.x23,.x24,.x25,.x26] (a.env.sp.trans b.env.sp.symm)
    (by agree_tac [a.env.x20,b.env.x20,a.x23,b.x23,a.x24,b.x24,a.x25,b.x25,a.outAt.2.2,b.outAt.2.2])
    ⟨_,by taint_decide⟩

theorem aligned_rel (L : Lay Wn Ctx St W) (v : GcmImpl)
    (a : CrInG Wn true Ctx St W SP k R P D O n s) (b : CrInG Wn true Ctx St W SP l R P D O n t)
    (hP : P%16=0) (hv : v.ctr.scratch ≤ Wn-512) :
    RelCT isa (Eq2 s t) (aligned v.callees) TT := by
  have hc {σ : State} {k' : Reg → BitVec 64} (h : CrInG Wn true Ctx St W SP k' R P D O n σ) {m' : Mem}
      (hf : Frame (crFrame Wn St W O n) σ.mem m') :=
    ciph_frame hf (ctx_crFrame L (OutAt.dataW h.outAt h.data)) h.rounds
  refine rel_seq (rel_taint [.x19,.x20,.x21,.x22,.x23,.x24] (a.env.sp.trans b.env.sp.symm)
      (by agree_tac [a.env.x19,b.env.x19,a.env.x20,b.env.x20,a.env.x21,b.env.x21,
        a.x22,b.x22,a.x23,b.x23,a.x24,b.x24]) ⟨_,by taint_decide⟩)
    (crArgsG_ok L true (a.mid (icb := 0) hP)) (crArgsG_ok L true (b.mid (icb := 0) hP)) fun _ _ x y => ?_
  refine rel_seq (ctrTo_relLe v.ctr hv (fun _ _ ⟨rfl,rfl⟩ => ⟨_,_,_,_,_,_,_,x.call,y.call,x.env.sp.trans y.env.sp.symm⟩))
    (ctrCallG1_ok L v x (hc a x.frame) hv) (ctrCallG1_ok L v y (hc b y.frame) hv) fun _ _ ⟨g,lg⟩ ⟨h,lh⟩ => ?_
  refine rel_ite (eval_zero g.x24 (by omega_arith)) (eval_zero h.x24 (by omega_arith))
    (fun _ => rel_taint [] (g.env.sp.trans h.env.sp.symm) (by agree_tac []) ⟨.block [] 256,by decide⟩) (fun _ => ?_)
  refine rel_seq (rel_taint [.x19,.x20,.x21,.x22,.x23,.x24,.x25] (g.env.sp.trans h.env.sp.symm)
      (by agree_tac [g.env.x19,h.env.x19,g.env.x20,h.env.x20,g.env.x21,h.env.x21,
        g.x22,h.x22,g.x23,h.x23,g.x24,h.x24,g.x25,h.x25]) ⟨_,by taint_decide⟩)
    (crSeg2_ok L g lg) (crSeg2_ok L h lh) fun _ _ c d => ?_
  refine rel_seq (rel_ctrLe v.ctr hv c.call d.call (c.env.sp.trans d.env.sp.symm))
    (ctrCall2_ok L v c (hc a c.frame) hv) (ctrCall2_ok L v d (hc b d.frame) hv) fun _ _ e f => ?_
  exact rel_taint [.x20,.x23,.x24,.x26] (e.env.sp.trans f.env.sp.symm)
    (by agree_tac [e.env.x20,f.env.x20,e.x23,f.x23,e.x24,f.x24,e.outAt.2.2,f.outAt.2.2]) ⟨_,by taint_decide⟩

end VG.Proof.AesGcm.AArch64.DirectGather.Generic
