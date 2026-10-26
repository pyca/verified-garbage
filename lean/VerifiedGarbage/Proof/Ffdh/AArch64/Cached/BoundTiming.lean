module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.BoundHead
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.CopyTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.LoadTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Generate
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ToDual

/-! Choosing q or p−1 and loading the bound exposes no private-scalar data. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

structure BoundPublic where
 workspace : Ws
 ptr : Addr
 k : Nat
 dl : Nat
 positive : 0<workspace.w
 size : workspace.w<2^31
 lengthBound : k<2^31
 shape : dl=2*k ∨ dl=3*k

structure BoundReady (p : BoundPublic) (s : State) : Prop where
 good : GoodW p.workspace s
 pointer : word s.mem p.workspace.B (8*sDom)=p.ptr
 length : word s.mem p.workspace.B (8*sLen)=BitVec.ofNat 64 p.k
 domainLength : word s.mem p.workspace.B (8*sDL)=BitVec.ofNat 64 p.dl

structure BoundHeadReady (p : BoundPublic) (s : State) : Prop where
 good : GoodW p.workspace s
 ptr : s.gpr .x1=p.ptr
 len : s.gpr .x2=BitVec.ofNat 64 p.k
 test : s.gpr .x3=BitVec.ofNat 64 (p.dl-2*p.k)
 offset : s.gpr .x4=BitVec.ofNat 64 (2*p.k)

theorem boundNoQ_ct : RelCT isa (Two fun (p : BoundPublic) s =>GoodW p.workspace s)
 (.seq (copy 5 0) (.block [ldh .x8 (sArr 5),ld .x3 .x8,.subImm .x .x3 .x3 1,st .x3 .x8])) (fun _ _ =>True) := by
 refine RelCT.seq (two_post (Ψ:=fun (p : BoundPublic) s =>GoodW p.workspace s)
  (two_map (fun p =>p.workspace) (fun _ _ h =>h) (copy_ct (by decide : 5<8) (by decide : 0<8) (by taint_decide))) ?_)
  ?_
 · rintro p s ⟨mi,good,room⟩
   refine WP.mono (copy_ok good room p.positive p.size (by decide : 5<8) (by decide : 0<8) (by decide)) ?_
   rintro t ⟨goodT,_,_,_⟩
   exact ⟨mi,goodT,room⟩
 · change RelCT isa (Two fun (p : BoundPublic) s =>GoodW p.workspace s)
    (.block ([ldh .x8 (sArr 5)]++[ld .x3 .x8,.subImm .x .x3 .x3 1,st .x3 .x8])) _
   apply RelCT.block_append
   refine RelCT.seq (two_piece (Ψ:=fun (p : BoundPublic) s =>s.gpr .x8=off p.workspace.B (slot p.workspace.w 5))
    [.x0] (fun p s t hs ht =>pins_goodW _ s t hs ht) (by taint_decide) ?_)
    (two_taint [.x8] (fun p s t hs ht r hr =>by
     have eq : r= .x8 := by simpa using hr
     subst r;exact hs.trans ht.symm) (by taint_decide))
   rintro p s ⟨mi,good,room⟩
   brun [good.x0,hdr_enc (show sArr 5<32 by decide),header_read good room (show sArr 5<32 by decide),good.hdr.harr 5 (by decide)]

theorem scalarBound_ct : RelCT isa (Two BoundReady) Generate.bound (fun _ _ =>True) := by
 unfold Generate.bound
 refine RelCT.seq (two_piece (Ψ:=BoundHeadReady) [.x0]
  (fun _ s t hs ht =>pins_goodW _ s t hs.good ht.good) (by taint_decide) ?_) ?_
 · rintro p s h
   obtain ⟨mi,good,room⟩ := h.good
   refine WP.mono (boundHead_ok good room p.lengthBound p.shape h.pointer h.length h.domainLength) ?_
   rintro t ⟨⟨ptr,len,test,offset,mem⟩,rest⟩
   exact ⟨⟨mi,⟨good.scr.congr rest.wr,(rest.gpr .x0 (by decide)).trans good.x0,mem ▸ good.hdr⟩,room⟩,ptr,len,test,offset⟩
 · refine RelCT.ite ?_ ?_ ?_
   · rintro s t ⟨p,hs,ht,_⟩
     rw [eval_zero,eval_zero,hs.test,ht.test]
   · exact boundNoQ_ct.mono (fun _ _ h =>by rcases h.1 with ⟨p,hs,ht,sp⟩;exact ⟨p,hs.good,ht.good,sp⟩) (fun _ _ h =>h)
   · refine (RelCT.seq (two_piece (Ψ:=fun p s =>LoadReady (⟨p.workspace,p.ptr+BitVec.ofNat 64 (2*p.k),p.k⟩ : LoadPublic) s)
      [.x1,.x4] ?_ (by taint_decide) ?_)
      (two_map (fun p =>(⟨p.workspace,p.ptr+BitVec.ofNat 64 (2*p.k),p.k⟩ : LoadPublic)) (fun _ _ h =>h)
       (load_ct (by decide : 5<8) (by taint_decide)))).mono (fun _ _ h =>h.1) (fun _ _ h =>h)
     · intro p s t hs ht r hr
       simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
       rcases hr with rfl|rfl
       · exact hs.ptr.trans ht.ptr.symm
       · exact hs.offset.trans ht.offset.symm
     · rintro p s h
       obtain ⟨mi,good,room⟩ := h.good
       refine WP.mono (WP.keep [.x1] (Q:=fun t =>t.gpr .x1=p.ptr+BitVec.ofNat 64 (2*p.k) ∧ t.mem=s.mem) ?_ rfl rfl rfl) ?_
       · brun [h.ptr,h.offset]
       · rintro t ⟨⟨ptr,mem⟩,rest⟩
         exact ⟨⟨mi,⟨good.scr.congr rest.wr,(rest.gpr .x0 (by decide)).trans good.x0,mem ▸ good.hdr⟩,room⟩,
          ptr,(rest.gpr .x2 (by decide)).trans h.len⟩

end VG.Proof.Ffdh.AArch64.Cached
