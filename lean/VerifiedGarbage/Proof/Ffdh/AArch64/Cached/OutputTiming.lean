module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Finish
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Clear
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Generate
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! Output masks and zeroing use public lengths and addresses for either acceptance result. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure OutputPublic where
 p : Parameters
 yp : Addr
 words : p.w=(p.k+7)/8
 positive : 0<p.k
 size : p.k<2^31
 outsideX : ∀ i<p.k,p.Z≤ofs p.B (p.src+BitVec.ofNat 64 i)

def OutputReady (q : OutputPublic) (s : State) : Prop :=
 Good s q.p.B q.p.Z q.p.w q.p.mi ∧
 word s.mem q.p.B (8*sX)=q.p.src ∧ word s.mem q.p.B (8*sY)=q.yp ∧
 word s.mem q.p.B (8*sLen)=BitVec.ofNat 64 q.p.k ∧
 (∀ i<q.p.k,InRegions s.wr (q.p.src+BitVec.ofNat 64 i) 1)

structure ClearPublic where
 B : Addr
 Z : Nat
 out : Addr
 k : Nat
 room : 256≤Z

structure ClearReady (q : ClearPublic) (i : Nat) (s : State) : Prop where
 scratch : Scr s q.B q.Z
 base : s.gpr .x0=q.B
 pointer : word s.mem q.B (8*i)=q.out
 length : word s.mem q.B (8*sLen)=BitVec.ofNat 64 q.k

theorem clear_ct {i : Nat} (index : i<32) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
 (check : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x1 i,ldh .x2 sLen,movi .x3 0]) hc).isSome=true) :
 RelCT isa (Two fun q s =>ClearReady q i s) (Generate.clear i) (fun _ _ =>True) := by
 unfold Generate.clear
 refine RelCT.seq (two_piece (Ψ:=fun q s =>s.gpr .x1=q.out ∧ s.gpr .x2=BitVec.ofNat 64 q.k) [.x0]
  (fun _ s t hs ht r hr =>by
   have eq : r= .x0 := by simpa using hr
   subst r
   exact hs.base.trans ht.base.symm) check ?_)
  (two_taint [.x1,.x2] (fun _ s t hs ht r hr =>by
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl
   · exact hs.1.trans ht.1.symm
   · exact hs.2.trans ht.2.symm) (by taint_decide))
 intro q s h
 brun [h.base,hdr_enc index,hdr_enc (show sLen<32 by decide),h.pointer,h.length,
  h.scratch.ld (d:=8*i) (by have :=q.room;omega),h.scratch.ld (d:=8*sLen) (by have :=q.room;unfold sLen;omega)]

theorem maskX_ct : RelCT isa (Two OutputReady) Generate.maskX (fun _ _ =>True) := by
 unfold Generate.maskX
 refine RelCT.seq (two_piece (Ψ:=fun q s =>s.gpr .x1=q.p.src ∧ s.gpr .x2=BitVec.ofNat 64 q.p.k) [.x0]
  (fun _ s t hs ht r hr =>by
   have eq : r= .x0 := by simpa using hr
   subst r
   exact hs.1.x0.trans ht.1.x0.symm)
  (by taint_decide) ?_) (two_taint [.x1,.x2] (fun _ s t hs ht r hr =>by
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl
   · exact hs.1.trans ht.1.symm
   · exact hs.2.trans ht.2.symm) (by taint_decide))
 rintro q s ⟨good,x,_,len,_⟩
 brun [good.x0,hdr_enc (show sX<32 by decide),hdr_enc (show sLen<32 by decide),hdr_enc (show sTmp<32 by decide),
  header_read good q.p.room (show sX<32 by decide),header_read good q.p.room (show sLen<32 by decide),
  header_read good q.p.room (show sTmp<32 by decide),x,len]

def FinishReady (q : OutputPublic) (s : State) : Prop :=
 OutputReady q s ∧ ∃ c : Bool,word s.mem q.p.B (8*sTmp)=BitVec.ofNat 64 c.toNat

theorem finish_ct : RelCT isa (Two FinishReady) Generate.finish (fun _ _ =>True) := by
 unfold Generate.finish
 simp only [seqs]
 refine RelCT.seq (two_post (Ψ:=OutputReady)
  (maskX_ct.mono (fun _ _ ⟨q,hs,ht,sp⟩ =>⟨q,hs.1,ht.1,sp⟩) (fun _ _ h =>h)) ?_) ?_
 · rintro q s ⟨h,c,flag⟩
   obtain ⟨good,x,y,len,write⟩ := h
   have room256 : 256≤q.p.Z := by have :=q.p.room;dsimp only [slot,hdrBytes] at this;omega
   refine WP.mono (maskX_ok good.scr room256 good.x0 q.positive q.size x len flag write q.outsideX) ?_
   rintro t ⟨_,_,_,same,rest⟩
   have header (i : Nat) (hi : i<32) := workspace_word (B:=q.p.B) (by have :=good.scr.nowrap;omega) same
    (by have :=hdr_lt_slot q.p.w 8 hi;have :=q.p.room;omega : 8*i+8≤q.p.Z)
   exact ⟨⟨good.scr.congr rest.wr,(rest.gpr .x0 (by decide)).trans good.x0,
    (header sW (by decide)).trans good.hdr.hw,(header sMinv (by decide)).trans good.hdr.hminv,
    fun i hi =>(header (sArr i) (by unfold sArr;omega)).trans (good.hdr.harr i hi)⟩,
    (header sX (by decide)).trans x,(header sY (by decide)).trans y,(header sLen (by decide)).trans len,
    fun i hi =>by rw [rest.wr];exact write i hi⟩
 · refine RelCT.seq (two_piece (Ψ:=fun q s =>s.gpr .x0=q.p.B ∧ s.gpr .x8=off q.p.B (slot q.p.w 6) ∧
    s.gpr .x1=q.yp+BitVec.ofNat 64 q.p.k ∧ s.gpr .x9=BitVec.ofNat 64 q.p.k) [.x0]
    (fun _ s t hs ht r hr =>by
   have eq : r= .x0 := by simpa using hr
   subst r
   exact hs.1.x0.trans ht.1.x0.symm)
    (by taint_decide) ?_)
    (two_taint [.x0,.x8,.x1,.x9] ?_ (by taint_decide))
   · rintro q s ⟨good,_,y,len,_⟩
     brun [good.x0,hdr_enc (show sArr 6<32 by decide),hdr_enc (show sY<32 by decide),hdr_enc (show sLen<32 by decide),
      header_read good q.p.room (show sArr 6<32 by decide),header_read good q.p.room (show sY<32 by decide),
      header_read good q.p.room (show sLen<32 by decide),good.hdr.harr 6 (by decide),y,len]
   · intro q s t hs ht r hr
     simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
     rcases hr with rfl|rfl|rfl|rfl
     · exact hs.1.trans ht.1.symm
     · exact hs.2.1.trans ht.2.1.symm
     · exact hs.2.2.1.trans ht.2.2.1.symm
     · exact hs.2.2.2.trans ht.2.2.2.symm

theorem fail_ct : RelCT isa (Two OutputReady) Generate.fail (fun _ _ =>True) := by
 unfold Generate.fail
 let clearInfo (q : OutputPublic) (out : Addr) : ClearPublic := ⟨q.p.B,q.p.Z,out,q.p.k,by
  have :=q.p.room;dsimp only [slot,hdrBytes] at this;omega⟩
 refine RelCT.seq (two_post (Ψ:=fun q s =>ClearReady (clearInfo q q.yp) sY s)
  (two_map (fun q =>clearInfo q q.p.src) (fun q s h =>⟨h.1.scr,h.1.x0,h.2.1,h.2.2.2.1⟩)
   (clear_ct (by decide : sX<32) (by taint_decide))) ?_)
  (RelCT.seq (two_map (fun q =>clearInfo q q.yp) (fun _ _ h =>h) (clear_ct (by decide : sY<32) (by taint_decide)))
   ?_)
 · rintro q s ⟨good,x,y,len,write⟩
   refine WP.mono (clear_ok good.scr (clearInfo q q.p.src).room good.x0 q.positive q.size (by decide : sX<32) x len write) ?_
   rintro t ⟨_,frame,rest⟩
   have same (a : Addr) (ha : ofs q.p.B a<q.p.Z) : t.mem a=s.mem a :=
    frame a (Or.inr (by have :=le_ofs_of_sep q.outsideX ha;omega))
   have header (i : Nat) (hi : i<32) := workspace_word (B:=q.p.B) (by have :=good.scr.nowrap;omega) same
    (by have :=hdr_lt_slot q.p.w 8 hi;have :=q.p.room;omega : 8*i+8≤q.p.Z)
   exact ⟨good.scr.congr rest.wr,(rest.gpr .x0 (by decide)).trans good.x0,
    (header sY (by decide)).trans y,(header sLen (by decide)).trans len⟩
 · intro s t trS trT u v _ es et
   cases es with
   | block es =>
     cases et with
     | block et =>
       simp [execBlock,exec,movi,Size.bits,addrs] at es et
       exact ⟨es.2.trans et.2.symm,trivial⟩


end VG.Proof.Ffdh.AArch64.Cached
