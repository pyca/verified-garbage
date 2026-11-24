module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.Padded
import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
public import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.Standalone
import VerifiedGarbage.Proof.Framework.RelCTAssoc

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Standalone
open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Impl.AesGcm.AArch64.Contiguous.Standalone
variable {wn n : Nat} {C St W SP D : Addr} {a b : State}

theorem hash_rel (v : GcmImpl) {H Y B S : Addr} {nb : Nat} (p : GhCall a H Y B S nb)
    (q : GhCall b H Y B S nb) (sp : a.sp = b.sp) : RelCT isa (Eq2 a b) (hashBlocks v.callees) TT := by
  refine rel_ite (eval_zero p.x3 (by have := p.n_lt; omega)) (eval_zero q.x3 (by have := q.n_lt; omega))
    (fun _ => ?_) (fun _ => rel_gh v.gh p q sp)
  exact rel_taint [] sp (by agree_tac []) ⟨.block [] 256,by decide⟩

theorem padded_rel (L : Lay wn C St W) (v : GcmImpl) (ea : Env wn C St W SP a) (eb : Env wn C St W SP b)
    (sa : a.gpr .x23 = D) (sb : b.gpr .x23 = D) (na : a.gpr .x24 = BitVec.ofNat 64 n)
    (nb : b.gpr .x24 = BitVec.ofNat 64 n) (da : DataOk wn St W a D n) (db : DataOk wn St W b D n) :
    RelCT isa (Eq2 a b) (padded v.callees) TT := by
  have ia := initial (x := []) ea (k := a.gpr) (fun _ _ => rfl) sa na da rfl (by decide)
  have ib := initial (x := []) eb (k := b.gpr) (fun _ _ => rfl) sb nb db rfl (by decide)
  unfold padded
  refine rel_seq (rel_taint [.x19,.x20,.x21,.x23,.x24] (ea.sp.trans eb.sp.symm)
    (by agree_tac [ea.x19,eb.x19,ea.x20,eb.x20,ea.x21,eb.x21,sa,sb,na,nb]) ⟨_,by taint_decide⟩)
    (absSeg2_ok L (.inr rfl) ia) (absSeg2_ok L (.inr rfl) ib) ?_
  intro u z p q
  refine rel_seq (hash_rel v p.call q.call (p.env.sp.trans q.env.sp.symm))
    (absCall2With_ok L (.inr rfl) p (hash_ok v p.call)) (absCall2With_ok L (.inr rfl) q (hash_ok v q.call)) ?_
  rintro u z ⟨p,lt⟩ ⟨q,_⟩
  refine rel_ite (eval_zero p.x24 (by omega)) (eval_zero q.x24 (by omega)) (fun _ => ?_) (fun _ => ?_)
  · exact rel_taint [] (p.env.sp.trans q.env.sp.symm) (by agree_tac []) ⟨.block [] 256,by decide⟩
  apply RelCT.assoc
  refine rel_seq (rel_taint [.x19,.x20,.x21,.x23,.x24] (p.env.sp.trans q.env.sp.symm)
    (by agree_tac [p.env.x19,q.env.x19,p.env.x20,q.env.x20,p.env.x21,q.env.x21,p.x23,q.x23,p.x24,q.x24])
    ⟨_,by taint_decide⟩)
    (lastArgs_ok L p.env p.kept p.x23 p.x24 lt (p.data.drop p.le))
    (lastArgs_ok L q.env q.kept q.x23 q.x24 lt (q.data.drop q.le)) ?_
  intro u z h g
  exact rel_gh v.gh h.call g.call (h.env.sp.trans g.env.sp.symm)

end VG.Proof.AesGcm.AArch64.Contiguous.Standalone
