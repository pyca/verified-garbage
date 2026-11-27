module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.StandaloneTag
public import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
import VerifiedGarbage.Proof.AesGcm.AArch64.Body
import VerifiedGarbage.Proof.AesGcm.AArch64.PieceCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.Standalone

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Standalone
open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Impl.AesGcm.AArch64.Contiguous.Standalone
variable {wn R : Nat} {C St W SP Tg : Addr} {a b : State}

theorem direct_rel (L : Lay wn C St W) (v : GcmImpl) (ea : Env wn C St W SP a) (eb : Env wn C St W SP b)
    (ta : DataW wn C St W a Tg 16) (tb : DataW wn C St W b Tg 16) (hr : R=10 ∨ R=12 ∨ R=14)
    (ra : a.gpr .x22 = BitVec.ofNat 64 R) (rb : b.gpr .x22 = BitVec.ofNat 64 R)
    (sa : a.mem.readW (W+BitVec.ofNat 64 tlO) 64 = Tg) (sb : b.mem.readW (W+BitVec.ofNat 64 tlO) 64 = Tg)
    (hv : v.ctr.scratch ≤ wn-512) :
    RelCT isa (Eq2 a b) (.seq (.block tagArgs) (ctrCallG v.callees true)) TT := by
  refine rel_seq (rel_taint [.x19] (ea.sp.trans eb.sp.symm)
    (by agree_tac [ea.x19,eb.x19]) ⟨_,by taint_decide⟩)
    (tagArgs_ok L ea ta hr ra sa) (tagArgs_ok L eb tb hr rb sb) ?_
  rintro u z ⟨p,h⟩ ⟨q,g⟩
  refine ctrTo_relLe v.ctr hv (fun u z eq => ?_)
  rcases eq with ⟨rfl,rfl⟩
  exact ⟨_,_,_,_,_,_,_,h,g,p.sp.trans (ea.sp.trans (eb.sp.symm.trans q.sp.symm))⟩

theorem tag_rel (L : Lay wn C St W) (v : GcmImpl) (ea : Env wn C St W SP a) (eb : Env wn C St W SP b)
    (ta : DataW wn C St W a Tg 16) (tb : DataW wn C St W b Tg 16) (hr : R=10 ∨ R=12 ∨ R=14)
    (ra : a.gpr .x22 = BitVec.ofNat 64 R) (rb : b.gpr .x22 = BitVec.ofNat 64 R)
    (sa : a.mem.readW (W+BitVec.ofNat 64 tlO) 64 = Tg) (sb : b.mem.readW (W+BitVec.ofNat 64 tlO) 64 = Tg)
    (hv : v.ctr.scratch ≤ wn-512) : RelCT isa (Eq2 a b) (tagDirect v.callees) TT := by
  have ka : Kept a.gpr a := fun _ _ => rfl
  have kb : Kept b.gpr b := fun _ _ => rfl
  refine rel_seq (lens_rel L v (.inr rfl) (by decide) ea eb ka kb
    (show a.gpr .x25 = BitVec.ofNat 64 (a.gpr .x25).toNat by simp)
    (show b.gpr .x25 = BitVec.ofNat 64 (b.gpr .x25).toNat by simp) ⟨_,by taint_decide⟩)
    (WP.with_rdwr (lengths_ok L v ea ka)) (WP.with_rdwr (lengths_ok L v eb kb)) ?_
  rintro u z ⟨p,rd,wr⟩ ⟨q,rd',wr'⟩
  exact direct_rel L v p.env q.env (ta.of_eq rd wr) (tb.of_eq rd' wr') hr
    ((p.kept _ (by decide)).trans ra) ((q.kept _ (by decide)).trans rb)
    ((tagSlot L p.frame).trans sa) ((tagSlot L q.frame).trans sb) hv

end VG.Proof.AesGcm.AArch64.Contiguous.Standalone
