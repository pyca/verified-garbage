module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Metadata
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Policy
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ToDual

/-! Public metadata uses a public row count and fixed context addresses. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure MetadataPublic where
 B : Addr
 Z : Nat
 ctx : Addr
 N : Nat
 room : 256≤Z
 positive : 0<N
 bound : N≤8192

structure MetadataReady (q : MetadataPublic) (s : State) : Prop where
 scratch : Scr s q.B q.Z
 base : s.gpr .x0=q.B
 context : word s.mem q.B (8*sCtx)=q.ctx
 bits : word s.mem q.B (8*sBits)=BitVec.ofNat 64 q.N

structure MetadataHeadReady (q : MetadataPublic) (s : State) : Prop where
 scratch : Scr s q.B q.Z
 base : s.gpr .x0=q.B
 context : word s.mem q.B (8*sCtx)=q.ctx
 remaining : s.gpr .x12=BitVec.ofNat 64 (q.N+4)
 count : s.gpr .x13=0#64

structure MetadataTailReady (q : MetadataPublic) (s : State) : Prop where
 scratch : Scr s q.B q.Z
 base : s.gpr .x0=q.B
 context : word s.mem q.B (8*sCtx)=q.ctx

theorem metadataTail_ct : RelCT isa (Two MetadataTailReady) (.block Policy.metadataTail) (fun _ _ =>True) := by
 change RelCT isa (Two MetadataTailReady) (.block ([sth .x13 sRows,ldh .x8 sCtx]++[st .x10 .x8 0,st .x11 .x8 8,st .x13 .x8 16])) _
 apply RelCT.block_append
 refine RelCT.seq (two_piece (Ψ:=fun q s =>s.gpr .x8=q.ctx) [.x0] (fun _ s t hs ht r hr =>by
  have eq : r= .x0 := by simpa using hr
  subst r;exact hs.base.trans ht.base.symm) (by taint_decide) ?_)
  (two_taint [.x8] (fun _ s t hs ht r hr =>by
   have eq : r= .x8 := by simpa using hr
   subst r;exact hs.trans ht.symm) (by taint_decide))
 intro q s h
 have frame :=writeW_outside s.mem q.B (d:=8*sRows) (s.gpr .x13) (by decide : 8*sRows+8≤2^64)
 have pointer :=(frame.word (Or.inl (by decide : 8*sCtx+8≤8*sRows)) (by decide)).trans h.context
 brun [h.base,hdr_enc (show sRows<32 by decide),hdr_enc (show sCtx<32 by decide),
  h.scratch.st (d:=8*sRows) (by have :=q.room;unfold sRows;omega),
  h.scratch.ld (d:=8*sCtx) (by have :=q.room;unfold sCtx;omega),pointer]

theorem metadata_ct : RelCT isa (Two MetadataReady) Policy.metadata (fun _ _ =>True) := by
 unfold Policy.metadata
 refine RelCT.seq (two_piece (Ψ:=MetadataHeadReady) [.x0] (fun _ s t hs ht r hr =>by
  have eq : r= .x0 := by simpa using hr
  subst r;exact hs.base.trans ht.base.symm) (by taint_decide) ?_) ?_
 · intro q s h
   refine WP.mono (metadataHead_ok h.scratch q.room h.base q.bound h.bits) ?_
   rintro t ⟨⟨_,_,remaining,count,mem⟩,rest⟩
   have frame : Outside q.B (8*sBytes) 8 s.mem t.mem :=by rw [mem];exact writeW_outside _ _ _ (by decide)
   exact ⟨h.scratch.congr rest.wr,(rest.gpr .x0 (by decide)).trans h.base,
    (header_other frame (by decide) (by decide) (by decide)).trans h.context,remaining,count⟩
 · refine RelCT.seq (two_post (Ψ:=MetadataTailReady)
    (two_taint [.x12,.x13] (fun _ s t hs ht r hr =>by
     simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
     rcases hr with rfl|rfl
     · exact hs.remaining.trans ht.remaining.symm
     · exact hs.count.trans ht.count.symm) (by taint_decide)) ?_) metadataTail_ct
   intro q s h
   refine WP.mono (metadataRows_ok s q.positive q.bound h.remaining h.count) ?_
   rintro t ⟨_,mem,rest⟩
   exact ⟨h.scratch.congr rest.wr,(rest.gpr .x0 (by decide)).trans h.base,mem ▸ h.context⟩

end VG.Proof.Ffdh.AArch64.Cached
