module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.InitialTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.BasisLoopTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeTable
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Precompute
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! All 32 public comb entries are built on a fixed public schedule. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure TablePublic extends InitialPublic where
 bits : 0<p.N ∧ p.N≤8192

structure TableReady (q : TablePublic) (s : State) : Prop extends TableInitialReady q.toInitialPublic s where
 rows : word s.mem q.p.B (8*sRows)=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows q.p.N)

structure TableInitialized (q : TablePublic) (s : State) : Prop where
 basis : Basis q.p 1 s
 space : ContextSpace q.p s
 context : word s.mem q.p.B (8*sCtx)=q.p.ctx
 rows : word s.mem q.p.B (8*sRows)=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows q.p.N)
 table : TablePrefix q.p 2 s

theorem precomputeTable_ct (M : Mont) : RelCT isa (Two TableReady) (Precompute.table M.mm) (fun _ _ =>True) := by
 unfold Precompute.table
 refine RelCT.seq (two_post (Ψ:=TableInitialized)
  (two_map TablePublic.toInitialPublic (fun _ _ h =>h.toTableInitialReady) (precomputeInitial_ct M)) ?_) ?_
 · intro q s h
   exact WP.mono (precomputeInitial_ok M h.field h.space h.generator q.words q.positive q.size q.reduced h.context h.domain h.length h.rows)
    (fun _ ⟨basis,space,ctx,rows,table,_,_⟩ =>⟨basis,space,ctx,rows,table⟩)
 · refine RelCT.seq (two_piece (Ψ:=fun q s =>BasisLoopReady (⟨q.p,q.bits⟩ : BasisLoopPublic) 0 s) [.x0]
    (fun q s t hs ht r hr =>by
     have eq : r= .x0 := by simpa using hr
     subst r;exact hs.basis.good.x0.trans ht.basis.good.x0.symm) (by taint_decide) ?_)
    (two_map (fun q =>(⟨q.p,q.bits⟩ : BasisLoopPublic)) (fun _ _ h =>h) (precomputeBasisLoop_ct M))
   intro q s h
   refine WP.mono (setControlNat_ok h.basis.good q.p.room (by decide : 16≤sD) (by decide : sD<32) (by decide : 2<2^16)) ?_
   rintro t ⟨good,index,frame,rest⟩
   have inscr : InScr q.p.B q.p.Z s.mem t.mem :=InScr.of_outside frame
    (by have :=hdr_lt_slot q.p.w 8 (show sD<32 by decide);have :=q.p.room;omega)
   refine ⟨⟨by decide,by decide⟩,q.bits,?_,h.space.after rest,
    (header_other frame (by decide) (by decide) (by decide)).trans h.context,index,
    (header_other frame (by decide) (by decide) (by decide)).trans h.rows,h.table.after_inscr h.space (by decide) inscr⟩
   simpa only [Nat.sub_self,Nat.zero_mul,Nat.pow_zero] using h.basis.after_header good frame (by decide : sD<32)

end VG.Proof.Ffdh.AArch64.Cached
