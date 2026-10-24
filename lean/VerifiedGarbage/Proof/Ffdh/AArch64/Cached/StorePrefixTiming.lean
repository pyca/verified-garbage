module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.StorePrefix
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Precompute
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! Serialization copies two complete public-length limb ranges to fixed context offsets. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def StorePrefixReady (p : Parameters) (s : State) : Prop :=
 Good s p.B p.Z p.w p.mi ∧ ContextSpace p s ∧ word s.mem p.B (8*sCtx)=p.ctx

def StoreFirstReady (p : Parameters) (s : State) : Prop :=
 StorePrefixReady p s ∧ s.gpr .x16=off p.B (slot p.w 0) ∧ s.gpr .x17=off p.ctx 24 ∧ s.gpr .x12=BitVec.ofNat 64 p.w

def StoreSecondReady (p : Parameters) (s : State) : Prop :=
 Good s p.B p.Z p.w p.mi ∧ s.gpr .x17=off p.ctx (24+8*p.w)

theorem storePrefix_ct : RelCT isa (Two StorePrefixReady) Precompute.storePrefix (fun _ _ =>True) := by
 unfold Precompute.storePrefix
 simp only [seqs]
 refine RelCT.seq (two_piece (Ψ:=StoreFirstReady) [.x0] (fun p s t hs ht r hr =>by
  have eq : r= .x0 := by simpa using hr
  subst r;exact hs.1.x0.trans ht.1.x0.symm) (by taint_decide) ?_) ?_
 · rintro p s ⟨good,space,ctx⟩
   refine WP.mono (WP.keep [.x12,.x16,.x17] (Q:=fun t =>t.gpr .x16=off p.B (slot p.w 0) ∧
    t.gpr .x17=off p.ctx 24 ∧ t.gpr .x12=BitVec.ofNat 64 p.w ∧ t.mem=s.mem) ?_ rfl rfl rfl) ?_
   · brun [good.x0,hdr_enc (show sCtx<32 by decide),hdr_enc (show sArr 0<32 by decide),hdr_enc (show sW<32 by decide),
      header_read good p.room (show sCtx<32 by decide),header_read good p.room (show sArr 0<32 by decide),
      header_read good p.room (show sW<32 by decide),ctx,good.hdr.harr 0 (by decide),good.hdr.hw]
   · rintro t ⟨⟨ptr,dst,count,mem⟩,rest⟩
     exact ⟨⟨⟨good.scr.congr rest.wr,(rest.gpr .x0 (by decide)).trans good.x0,mem ▸ good.hdr⟩,
      space.after rest,mem ▸ ctx⟩,ptr,dst,count⟩
 · refine RelCT.seq (two_post (Ψ:=StoreSecondReady)
    (two_taint [.x16,.x17,.x12] (fun _ s t hs ht r hr =>by
     simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
     rcases hr with rfl|rfl|rfl
     · exact hs.2.1.trans ht.2.1.symm
     · exact hs.2.2.1.trans ht.2.2.1.symm
     · exact hs.2.2.2.trans ht.2.2.2.symm) (by taint_decide)) ?_) ?_
   · rintro p s ⟨⟨good,space,_⟩,src,dst,count⟩
     refine WP.mono (copyToContext_ok good space (by decide : 0<8) (by omega : 3+p.w≤3+34*p.w) src dst count) ?_
     rintro t ⟨good,_,_,_,ptr,_⟩
     exact ⟨good,by simpa only [Nat.mul_add,Nat.reduceMul] using ptr⟩
   · refine RelCT.seq (two_piece (Ψ:=fun p s =>s.gpr .x16=off p.B (slot p.w 4) ∧
      s.gpr .x17=off p.ctx (24+8*p.w) ∧ s.gpr .x12=BitVec.ofNat 64 p.w) [.x0]
      (fun p s t hs ht r hr =>by
       have eq : r= .x0 := by simpa using hr
       subst r;exact hs.1.x0.trans ht.1.x0.symm) (by taint_decide) ?_)
      (two_taint [.x16,.x17,.x12] (fun _ s t hs ht r hr =>by
       simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
       rcases hr with rfl|rfl|rfl
       · exact hs.1.trans ht.1.symm
       · exact hs.2.1.trans ht.2.1.symm
       · exact hs.2.2.trans ht.2.2.symm) (by taint_decide))
     rintro p s ⟨good,ptr⟩
     brun [good.x0,hdr_enc (show sArr 4<32 by decide),hdr_enc (show sW<32 by decide),
      header_read good p.room (show sArr 4<32 by decide),header_read good p.room (show sW<32 by decide),
      good.hdr.harr 4 (by decide),good.hdr.hw,ptr]

end VG.Proof.Ffdh.AArch64.Cached
