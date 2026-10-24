module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.EntryTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeProductIO
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Precompute
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! Subset entry transfers use only the public tooth and subset indices. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure ProductIO where
 p : Parameters
 j : Nat
 d : Nat

structure ProductIOReady (q : ProductIO) (s : State) : Prop where
 good : Good s q.p.B q.p.Z q.p.w q.p.mi
 context : word s.mem q.p.B (8*sCtx)=q.p.ctx
 index : word s.mem q.p.B (8*sJ)=BitVec.ofNat 64 q.j
 tooth : word s.mem q.p.B (8*sD)=BitVec.ofNat 64 q.d

theorem productLoad_ct : RelCT isa (Two ProductIOReady) Precompute.productLoad (fun _ _ =>True) := by
 unfold Precompute.productLoad
 refine RelCT.seq (two_piece (Ψ:=fun q s =>EntryReady (q.p,q.j) s) [.x0] ?_ (by taint_decide) ?_)
  (two_map (fun q =>(q.p,q.j)) (fun _ _ h =>h) (loadEntry_ct 1 (by decide) (by taint_decide)))
 · intro q s t hs ht r hr
   have eq : r= .x0 := by simpa using hr
   subst r
   exact hs.good.x0.trans ht.good.x0.symm
 · intro q s h
   refine WP.mono (WP.keep [.x3] (Q:=fun t =>t.gpr .x3=BitVec.ofNat 64 q.j ∧ t.mem=s.mem) ?_ rfl rfl rfl) ?_
   · brun [h.good.x0,hdr_enc (show sJ<32 by decide),header_read h.good q.p.room (show sJ<32 by decide),h.index]
   · rintro t ⟨⟨index,mem⟩,rest⟩
     exact ⟨⟨h.good.scr.congr rest.wr,(rest.gpr .x0 (by decide)).trans h.good.x0,mem ▸ h.good.hdr⟩,
      mem ▸ h.context,index⟩

theorem productStore_ct : RelCT isa (Two ProductIOReady) Precompute.productStore (fun _ _ =>True) := by
 unfold Precompute.productStore
 refine RelCT.seq (two_piece (Ψ:=fun q s =>EntryReady (q.p,q.j+q.d) s) [.x0] ?_ (by taint_decide) ?_)
  (two_map (fun q =>(q.p,q.j+q.d)) (fun _ _ h =>h) (storeEntry_ct 6 (by decide) (by taint_decide)))
 · intro q s t hs ht r hr
   have eq : r= .x0 := by simpa using hr
   subst r
   exact hs.good.x0.trans ht.good.x0.symm
 · intro q s h
   refine WP.mono (WP.keep [.x3,.x4] (Q:=fun t =>t.gpr .x3=BitVec.ofNat 64 (q.j+q.d) ∧ t.mem=s.mem) ?_ rfl rfl rfl) ?_
   · brun [h.good.x0,hdr_enc (show sJ<32 by decide),hdr_enc (show sD<32 by decide),
      header_read h.good q.p.room (show sJ<32 by decide),header_read h.good q.p.room (show sD<32 by decide),
      h.index,h.tooth,←BitVec.ofNat_add]
   · rintro t ⟨⟨index,mem⟩,rest⟩
     exact ⟨⟨h.good.scr.congr rest.wr,(rest.gpr .x0 (by decide)).trans h.good.x0,mem ▸ h.good.hdr⟩,
      mem ▸ h.context,index⟩

end VG.Proof.Ffdh.AArch64.Cached
