module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.StandaloneFrame
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.StandaloneAuthStage
import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.StandaloneTagCT
import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.Standalone

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Standalone
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Impl.AesGcm.AArch64.Contiguous.Standalone (body encrypt tagDirect)
open VG.Proof.Gcm.AArch64.Stitch (GatherLaws)
open VG.Spec.Gcm (inc32)
variable {wn : Nat} {W : Addr} {s t : State}

private theorem tagExit_rel {C SP Tg : Addr} {R : Nat} (L : Lay wn C (W+16#64) W) (v : GcmImpl)
    (ea : Env wn C (W+16#64) W SP s) (eb : Env wn C (W+16#64) W SP t)
    (da : DataW wn C (W+16#64) W s Tg 16) (db : DataW wn C (W+16#64) W t Tg 16)
    (nr : R=10 ∨ R=12 ∨ R=14) (ra : s.gpr .x22=BitVec.ofNat 64 R) (rb : t.gpr .x22=BitVec.ofNat 64 R)
    (pa : s.mem.readW (W+248#64) 64=Tg) (pb : t.mem.readW (W+248#64) 64=Tg) (hv : v.ctr.scratch≤wn-512) :
    RelCT isa (Eq2 s t) (.seq (tagDirect v.callees) (.block restore)) TT := by
  refine rel_seq (tag_rel L v ea eb da db nr ra rb pa pb hv)
    (tag_ok L v ea (k := s.gpr) (fun _ _ => rfl) da nr ra pa hv)
    (tag_ok L v eb (k := t.gpr) (fun _ _ => rfl) db nr rb pb hv) ?_
  rintro x y ⟨px,_,_,_⟩ ⟨py,_,_,_⟩
  exact rel_taint [.x19] (px.sp.trans py.sp.symm) (by agree_tac [px.x19,py.x19]) ⟨_,by taint_decide⟩

private theorem fin_ok {o : State} (e : Env wn (o.gpr .x0) (W+16#64) W o.sp s) (h : ReturnPrep wn W o s) :
    WP isa (.block finPrep) s fun u => Regs [.x26,.x27] s u := by
  refine (finPrep_ok (al := (o.gpr .x5).toNat) (n := (stackArg o 0).toNat) e.x19 (covers_left e.perm.w)
    (by simpa using h.alen) (by simpa using h.len) e.perm.hWn).mono ?_
  exact fun _ r => r.2.2

theorem body_rel (v : GcmImpl) (gh : v.calls.pmull=true → GatherLaws) (hv : v.ctr.scratch≤v.calls.pwWn-512) :
    BodyRel v := by
  intro a b W ca cb pub
  have pf := front_rel v ca cb pub
  obtain ⟨cx,rnd,_,_,_,_,src,dst,sp,stk⟩ := pub
  have n := stk 0 (by decide)
  have tag := stk 1 (by decide)
  apply front_then_rel
  refine rel_seq pf (front_ok v ca) (front_ok v cb) ?_
  intro x y f g
  have ib := g.input
  rw [←cx,←rnd,←n,←src,←dst,←sp] at ib
  refine rel_seq (encrypt_rel v ca.lay f.input ib gh hv)
    (encrypt_ok v ca.lay f.input gh hv) (encrypt_ok v cb.lay g.input gh hv) ?_
  rintro m o ⟨e,pa⟩ ⟨i,pb⟩
  have dx := ca.dst.ok.of_eq (e.rd.trans f.rd) (e.wr.trans f.wr)
  have dy := cb.dst.ok.of_eq (i.rd.trans g.rd) (i.wr.trans g.wr)
  have eb := i.env
  have endB := i.x26
  rw [←cx,←sp] at eb
  rw [←dst,←n] at endB
  rw [←dst,←n] at dy
  rw [←dst,←n] at pb
  obtain ⟨j,le,sl,_⟩ := e.auth
  have sl' := pb.trans (pa.symm.trans sl)
  apply RelCT.assoc
  refine rel_seq (auth_rel ca.lay v e.env eb dx dy le e.x26 endB sl sl')
    (auth_stage v ca f e) (auth_stage v cb g i) ?_
  intro q r h k
  have ap := returnPrep ca f e h.frame
  have bp := returnPrep cb g i k.frame
  refine rel_seq (rel_taint [.x19] (h.env.sp.trans (sp.trans k.env.sp.symm))
    (by agree_tac [h.env.x19,k.env.x19]) ⟨_,by taint_decide⟩)
    (fin_ok h.env ap) (fin_ok k.env bp) ?_
  intro u z ar br
  have ae := h.env.of_regs ar
  have be := k.env.of_regs br
  have atag := ca.tagData.of_eq (ar.rd.trans (h.rd.trans (e.rd.trans f.rd))) (ar.wr.trans (h.wr.trans (e.wr.trans f.wr)))
  have btag := cb.tagData.of_eq (br.rd.trans (k.rd.trans (i.rd.trans g.rd))) (br.wr.trans (k.wr.trans (i.wr.trans g.wr)))
  have xA := (ar.others .x22 (by decide)).trans ((h.kept _ (by decide)).trans (e.x22.trans f.input.x22))
  have xB := (br.others .x22 (by decide)).trans ((k.kept _ (by decide)).trans (i.x22.trans g.input.x22))
  have slotA : u.mem.readW (W+248#64) 64=stackArg a 1 := ar.mem ▸ ap.tag
  have slotB : z.mem.readW (W+248#64) 64=stackArg b 1 := br.mem ▸ bp.tag
  rw [←cx,←sp] at be
  rw [←cx,←tag] at btag
  rw [←rnd] at xB
  rw [←tag] at slotB
  exact tagExit_rel ca.lay v ae be atag btag ca.nr xA xB slotA slotB hv

end VG.Proof.AesGcm.AArch64.Contiguous.Standalone
