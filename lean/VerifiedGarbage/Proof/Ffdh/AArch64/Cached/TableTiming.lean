module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.InitialTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.BasisTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeBasisLoop
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeTable
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Precompute
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! ### `Ffdh.AArch64.Cached.BasisLoopTiming`, which only this module used -/

section

/-! The public table completes exactly four tooth rounds. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (eval_nonzero ne_zero_iff)

structure BasisLoopPublic where
 p : Parameters
 bits : 0<p.N ∧ p.N≤8192

def BasisLoopReady (q : BasisLoopPublic) (i : Nat) (s : State) : Prop := BasisState q.p (i+1) s

private theorem basisFlag : ∀ i<4,
 (BitVec.ofNat 64 (2^((i+1)+1))-32#64 !=0#64)=decide (i+1<4) := by decide +kernel

theorem precomputeBasisLoop_ct (M : Mont) : RelCT isa (Two fun q s =>BasisLoopReady q 0 s)
 (.loop (Precompute.basis M.mm) (.nonzero .x .x3)) (fun _ _ =>True) := by
 have hct : RelCT isa (Two fun (q : BasisLoopPublic × Fin 4) s =>BasisLoopReady q.1 q.2.val s)
  (Precompute.basis M.mm) (fun _ _ =>True) :=
  two_map (fun q =>(⟨q.1.p,q.2.val+1,by omega_using [],by have :=q.2.isLt;omega_using [],q.1.bits⟩ : BasisPublic))
   (fun _ _ h =>h) (precomputeBasis_ct M)
 have stepCt : RelCT isa (Two fun (q : BasisLoopPublic × Nat) s =>q.2<4 ∧ BasisLoopReady q.1 q.2 s)
  (Precompute.basis M.mm) (fun _ _ =>True) := by
  intro s t ts tt u v h es et
  obtain ⟨⟨q,i⟩,⟨hi,hs⟩,⟨_,ht⟩,sp⟩:=h
  exact hct _ _ _ _ _ _ ⟨(q,⟨i,hi⟩),hs,ht,sp⟩ es et
 have loop:=two_loop (cond:= .nonzero .x .x3) (Φ:=BasisLoopReady) (Ψ:=fun _ _ =>True)
  (fun _ : BasisLoopPublic =>4) stepCt (by
   intro q i s hi h
   refine WP.mono (precomputeBasis_ok M h (by omega_using [hi] : i+1<5)) ?_
   rintro t ⟨state,index,_,_⟩
   refine ⟨?_,fun _ =>state,fun _ =>trivial⟩
   rw [eval_nonzero,index]
   exact congrArg some (basisFlag i hi))
 exact loop.mono (fun _ _ ⟨q,hs,ht,sp⟩ =>⟨q,⟨by decide,hs⟩,⟨by decide,ht⟩,sp⟩) (fun _ _ _ =>trivial)

end VG.Proof.Ffdh.AArch64.Cached

end

end


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
    (by have :=hdr_lt_slot q.p.w 8 (show sD<32 by decide);have :=q.p.room;omega_arith)
   refine ⟨⟨by decide,by decide⟩,q.bits,?_,h.space.after rest,
    (header_other frame (by decide) (by decide) (by decide)).trans h.context,index,
    (header_other frame (by decide) (by decide) (by decide)).trans h.rows,h.table.after_inscr h.space (by decide) inscr⟩
   simpa only [Nat.sub_self,Nat.zero_mul,Nat.pow_zero] using h.basis.after_header good frame (by decide : sD<32)

end VG.Proof.Ffdh.AArch64.Cached
