module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SetLowBit
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.LessTiming
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Generate
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Source
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
public import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.BoundHead
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Copy
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Generate
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.LoadArray
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SourceSlices
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Nonzero
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Less
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PowerState
public import VerifiedGarbage.Proof.Ffdh.Domain
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Initial
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.CopyTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.LoadTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs

/-! ### `Ffdh.AArch64.Cached.NonzeroTiming`, which only this module used -/

section

/-! The zero test's complete trace depends only on public workspace geometry. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem nonzero_ct : RelCT isa (Two GoodW) Generate.nonzero (fun _ _ =>True) := by
 unfold Generate.nonzero
 refine RelCT.seq (two_piece (Ψ:=fun q s =>s.gpr .x0=q.B ∧ s.gpr .x8=off q.B (slot q.w 1) ∧
  s.gpr .x12=BitVec.ofNat 64 q.w) [.x0] pins_goodW (by taint_decide) ?_)
  (two_taint [.x0,.x8,.x12] ?_ (by taint_decide))
 · rintro q s ⟨mi,good,room⟩
   brun [good.x0,hdr_enc (show sArr 1<32 by decide),hdr_enc (show sW<32 by decide),
    header_read good room (show sArr 1<32 by decide),header_read good room (show sW<32 by decide),
    good.hdr.harr 1 (by decide),good.hdr.hw]
 · intro q s t hs ht r hr
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl|rfl
   · exact hs.1.trans ht.1.symm
   · exact hs.2.1.trans ht.2.1.symm
   · exact hs.2.2.trans ht.2.2.symm

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.BoundTiming`, which only this module used -/

section

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

end

end

/-! ### `Ffdh.AArch64.Cached.SourceEncoding`, which this module and modules that import it used -/

section

/-! ### `Ffdh.AArch64.Cached.RangeFrame`, which the modules that import this one used -/

section

/-! ### `Ffdh.AArch64.Cached.ScalarRange`, which only this module used -/

section

/-! ### `Ffdh.AArch64.Cached.ScalarBound`, which only this module used -/

section

/-! ### `Ffdh.AArch64.Cached.BoundNoQ`, which only this module used -/

section

/-! ### `Ffdh.AArch64.Cached.LowDecrement`, which only this module used -/

section

/-! An odd modulus permits p−1 by decrementing only its low limb, without a borrow. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.Proof.Bignum

theorem wv_low_decrement (m : Mem) (B : Addr) {d w : Nat} (positive : 0<w)
 (fit : d+8*w≤2^64) (odd : wv m B d w%2=1) :
 wv (m.writeW (off B d) (word m B d-1#64)) B d w=wv m B d w-1 := by
 obtain low := wv_mod64 m B d (by omega_using [positive] : 1≤w)
 obtain positiveLow : 0<(word m B d).toNat := by
  have : wv m B d w%2^64%2=1 := by omega_using [odd]
  rw [low] at this
  omega_using [this]
 obtain sub : (word m B d-1#64).toNat=(word m B d).toNat-1 := by
  simp only [BitVec.toNat_sub,show (1#64).toNat=1 from rfl]
  have := (word m B d).isLt
  omega_using [positiveLow]
 have split (m : Mem) : wv m B d w= (word m B d).toNat + 2^64*wv m B (d+8) (w-1) := by
  obtain h := wv_add m B d 1 (w-1)
  rw [show 1+(w-1)=w by omega_using [positive]] at h
  simpa only [wv,Nat.mul_zero,Nat.pow_zero,Nat.mul_one,Nat.one_mul,Nat.add_zero,Nat.zero_add,Nat.reduceMul,Nat.reducePow] using h
 obtain frame := writeW_outside m B (word m B d-1#64) (by omega_using [positive, fit] : d+8≤2^64)
 rw [split,word_writeW_self,sub,frame.wv (Or.inr (by omega_using [] : d+8≤d+8)) (by omega_using [positive, fit]),split]
 omega_using [positiveLow]

end VG.Proof.Ffdh.AArch64.Cached

end

end


/-! For domains without q the rejection bound is p−1, with no propagated borrow. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem boundNoQ_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (positive : 0<w) (size : w<2^31)
 (odd : wv s.mem B (slot w 0) w%2=1) :
 WP isa (.seq (copy 5 0) (.block [ldh .x8 (sArr 5),ld .x3 .x8,.subImm .x .x3 .x3 1,st .x3 .x8])) s fun t =>
 Good t B Z w mi ∧ wv t.mem B (slot w 5) w=wv s.mem B (slot w 0) w-1 ∧
 Arrays B w [5] s.mem t.mem ∧ Keep mmRegs s t := by
 rw [WP.seq_iff]
 refine WP.mono (copy_ok good room positive size (by decide : 5<8) (by decide : 0<8) (by decide)) ?_
 rintro a ⟨goodA,valueA,frameA,restA⟩
 obtain arrayRoom := Nat.le_trans (slot_le (w:=w) (show 5<8 by decide)) room
 refine WP.mono (WP.keep [.x8,.x3] (Q:=fun t =>t.mem=a.mem.writeW (off B (slot w 5)) (word a.mem B (slot w 5)-1#64)) ?_ rfl rfl rfl) ?_
 · brun [goodA.x0,hdr_enc (show sArr 5<32 by decide),header_read goodA room (show sArr 5<32 by decide),
    goodA.hdr.harr 5 (by decide),goodA.scr.ld (d:=slot w 5) (by omega_using [arrayRoom]),goodA.scr.st (d:=slot w 5) (by omega_using [arrayRoom])]
 · rintro t ⟨memT,restT⟩
   obtain nowrap : slot w 5+8*w≤2^64 := by have := goodA.scr.nowrap;omega_using [arrayRoom, this]
   obtain value : wv t.mem B (slot w 5) w=wv s.mem B (slot w 0) w-1 := by
    rw [memT,wv_low_decrement _ _ positive nowrap (by rw [valueA];exact odd),valueA]
   obtain frameT : Arrays B w [5] a.mem t.mem := by
    apply Arrays.of_outside (j:=5) (by simp) (o:=slot w 5) (n:=8)
    · rw [memT];exact writeW_outside _ _ _ (by omega_using [positive, nowrap])
    · omega_using []
    · omega_using []
   obtain rest : Keep mmRegs s t := (restA.trans restT).mono (by simp [mmRegs])
   exact ⟨good_after_arrays goodA frameT restT ((restT.gpr .x0 (by decide)).trans goodA.x0),
    value,frameA.trans frameT,rest⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end


/-! The rejection bound is exactly the reviewed q-or-p−1 value for both domain encodings. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

theorem scalarBound_ok {s : State} {B ptr : Addr} {Z w k dl : Nat} {mi : BitVec 64} {dom : List Byte}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (words : w=(k+7)/8) (positive : 0<k) (size : k<2^31)
 (shape : dl=2*k ∨ dl=3*k) (domLength : dom.length=dl) (source : Src s B Z ptr dom)
 (pointer : word s.mem B (8*sDom)=ptr) (length : word s.mem B (8*sLen)=BitVec.ofNat 64 k)
 (domainLength : word s.mem B (8*sDL)=BitVec.ofNat 64 dl)
 (modulus : wv s.mem B (slot w 0) w=(Spec.Ffdh.domainOf k dom).p)
 (odd : (Spec.Ffdh.domainOf k dom).p%2=1) :
 WP isa Generate.bound s fun t =>
 Good t B Z w mi ∧ wv t.mem B (slot w 5) w=Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) ∧
 Arrays B w [5] s.mem t.mem ∧ Keep mmRegs s t := by
 unfold Generate.bound
 rw [WP.seq_iff]
 refine WP.mono (boundHead_ok good room size shape pointer length domainLength) ?_
 rintro a ⟨⟨ptrA,lenA,testA,offsetA,memA⟩,restA⟩
 obtain goodA : Good a B Z w mi :=
  ⟨good.scr.congr restA.wr,(restA.gpr .x0 (by decide)).trans good.x0,memA ▸ good.hdr⟩
 obtain sourceA := source.congrK (fun x _ =>by rw [memA]) restA
 by_cases noQ : dl=2*k
 · have branch := boundNoQ_ok goodA room (by rw [words];omega_using [positive]) (by rw [words];omega_using [size])
    (by rw [memA,modulus];exact odd)
   obtain condition : isa.eval (.zero .x .x3) a=some true := by rw [eval_zero,testA,noQ,Nat.sub_self];decide
   obtain ⟨tr,t,run,goodT,value,frame,rest⟩ := branch
   refine ⟨_,t,.iteT condition run,goodT,?_,?_,(restA.trans rest).mono (by simp [mmRegs])⟩
   · rw [memA,modulus] at value
     simpa only [Spec.Ffdh.scalarBound,Spec.Ffdh.domainOf,
      ite_eq_right (by omega_using [positive, domLength, noQ] : ¬dom.length=3*k),Option.getD_none] using value
   · rw [←memA];exact frame
 · have three : dl=3*k := by omega_using [shape, noQ]
   obtain condition : isa.eval (.zero .x .x3) a=some false := by
    rw [eval_zero,testA,three]
    obtain nonzero : BitVec.ofNat 64 (3*k-2*k)≠0#64 := by
     intro eq;have := congrArg BitVec.toNat eq;change (3*k-2*k)%2^64=0 at this;omega_using [room, words, positive, size, shape, domLength, pointer, length, domainLength, modulus, odd, ptrA, lenA, testA, offsetA, noQ, three, eq, this]
    simp [nonzero]
   obtain body : WP isa (.seq (.block [.add .x .x1 .x1 .x4]) (load 5)) a fun t =>
    Good t B Z w mi ∧ wv t.mem B (slot w 5) w=Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) ∧
    Arrays B w [5] s.mem t.mem ∧ Keep mmRegs s t := by
    rw [WP.seq_iff]
    refine WP.mono (WP.keep [.x1] (Q:=fun b =>b.gpr .x1=ptr+BitVec.ofNat 64 (2*k) ∧ b.mem=a.mem) ?_ rfl rfl rfl) ?_
    · brun [ptrA,offsetA]
    · rintro b ⟨⟨ptrB,memB⟩,restB⟩
      obtain goodB : Good b B Z w mi :=
       ⟨goodA.scr.congr restB.wr,(restB.gpr .x0 (by decide)).trans goodA.x0,memB ▸ goodA.hdr⟩
      obtain srcB := sourceA.congrK (fun x _ =>by rw [memB]) restB
      refine WP.mono (loadArray_ok goodB room words positive size (by decide : 5<8)
       (src_take (src_drop srcB (2*k)) k) (by simp only [List.length_take,List.length_drop];omega_using [shape, domLength, noQ])
       ptrB ((restB.gpr .x2 (by decide)).trans lenA)) ?_
      rintro t ⟨goodT,value,frame,restT⟩
      refine ⟨goodT,?_,?_,((restA.trans restB).trans restT).mono (by simp [mmRegs])⟩
      · simpa only [Spec.Ffdh.scalarBound,Spec.Ffdh.domainOf,ite_eq_left (by omega_using [shape, domLength, noQ] : dom.length=3*k),Option.getD_some] using value
      · rw [←memA,←memB];exact frame
   obtain ⟨tr,t,run,post⟩ := body
   exact ⟨_,t,.iteF condition run,post⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end


/-! The complete rejection predicate is 0<x<q, or 0<x<p−1, at a fixed public width. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def scalarRanges (w : Nat) : List (Nat × Nat) :=
 [(slot w 1,8*(w+2)),(slot w 5,8*(w+2)),(8*sTmp,8)]

theorem scalarRange_ok {s : State} {B xp dp : Addr} {Z w k dl : Nat} {mi : BitVec 64} {dom bs : List Byte}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (words : w=(k+7)/8) (positive : 0<k) (size : k<2^31)
 (shape : dl=2*k ∨ dl=3*k) (domLength : dom.length=dl)
 (domainSource : Src s B Z dp dom) (scalarSource : Src s B Z xp bs) (bsLength : bs.length=k)
 (output : word s.mem B (8*sX)=xp) (domain : word s.mem B (8*sDom)=dp)
 (length : word s.mem B (8*sLen)=BitVec.ofNat 64 k) (domainLength : word s.mem B (8*sDL)=BitVec.ofNat 64 dl)
 (modulus : wv s.mem B (slot w 0) w=(Spec.Ffdh.domainOf k dom).p)
 (odd : (Spec.Ffdh.domainOf k dom).p%2=1) :
 WP isa Generate.scalarRange s fun t =>
 Good t B Z w mi ∧ wv t.mem B (slot w 1) w=Spec.Rsa.os2ip bs ∧
 t.gpr .x9=(if 0<Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs<Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) then 1#64 else 0#64) ∧
 Frm B (scalarRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
 obtain wPositive : 0<w := by rw [words];omega_using [positive]
 obtain wSize : w<2^31 := by rw [words];omega_using [size]
 obtain nowrap : slot w 8≤2^64 := by have := good.scr.nowrap;omega_using [room, this]
 obtain array0 := slot_le (w:=w) (show 0<8 by decide)
 obtain array1 := slot_le (w:=w) (show 1<8 by decide)
 unfold Generate.scalarRange
 simp only [seqs]
 rw [WP.seq_iff]
 refine WP.mono (WP.keep [.x1,.x2] (Q:=fun a =>a.gpr .x1=xp ∧ a.gpr .x2=BitVec.ofNat 64 k ∧ a.mem=s.mem) ?_ rfl rfl rfl) ?_
 · brun [good.x0,hdr_enc (show sX<32 by decide),hdr_enc (show sLen<32 by decide),
    header_read good room (show sX<32 by decide),header_read good room (show sLen<32 by decide),output,length]
 · rintro a ⟨⟨ptrA,lenA,memA⟩,restA⟩
   obtain goodA : Good a B Z w mi := ⟨good.scr.congr restA.wr,(restA.gpr .x0 (by decide)).trans good.x0,memA ▸ good.hdr⟩
   obtain scalarA := scalarSource.congrK (fun x _ =>by rw [memA]) restA
   rw [WP.seq_iff]
   refine WP.mono (loadArray_ok goodA room words positive size (by decide : 1<8) scalarA bsLength ptrA lenA) ?_
   rintro b ⟨goodB,valueB,frameB,restB⟩
   rw [WP.seq_iff]
   refine WP.mono (nonzero_ok goodB room wPositive wSize) ?_
   rintro c ⟨goodC,_,nonzeroC,frameC,restC⟩
   obtain before := (restA.trans restB).trans restC
   obtain inscrB := InScr.of_arrays frameB room (by simp : ∀ i∈[1],i<8)
   obtain inscrC : InScr B Z b.mem c.mem := InScr.of_outside frameC (by have := hdr_lt_slot w 8 (show sTmp<32 by decide);omega_using [room, this])
   obtain inscrSA : InScr B Z s.mem a.mem := by intro x hx;rw [memA]
   obtain sourceC := domainSource.congrK ((inscrSA.trans inscrB).trans inscrC) before
   have headerC (i : Nat) (hi : i<32) (different : i≠sTmp) : word c.mem B (8*i)=word s.mem B (8*i) := by
    rw [header_other frameC (by decide) hi different,arrays_header frameB hi,memA]
   obtain modulusC : wv c.mem B (slot w 0) w=(Spec.Ffdh.domainOf k dom).p := by
    rw [frameC.wv (Or.inr (hdr_lt_slot w 0 (show sTmp<32 by decide))) (by omega_using [nowrap, array0]),
     frameB.wv_of_not_mem (by decide) (by decide) (by have := good.scr.nowrap;omega_using [room, this]),memA]
    exact modulus
   obtain valueC : wv c.mem B (slot w 1) w=Spec.Rsa.os2ip bs := by
    rw [frameC.wv (Or.inr (hdr_lt_slot w 1 (show sTmp<32 by decide))) (by omega_using [nowrap, array1])];exact valueB
   rw [WP.seq_iff]
   refine WP.mono (scalarBound_ok goodC room words positive size shape domLength sourceC
    ((headerC sDom (by decide) (by decide)).trans domain)
    ((headerC sLen (by decide) (by decide)).trans length)
    ((headerC sDL (by decide) (by decide)).trans domainLength) modulusC odd) ?_
   rintro d ⟨goodD,boundD,frameD,restD⟩
   obtain valueD : wv d.mem B (slot w 1) w=Spec.Rsa.os2ip bs :=
    (frameD.wv_of_not_mem (by decide) (by decide) (by have := good.scr.nowrap;omega_using [room, this])).trans valueC
   obtain nzD : word d.mem B (8*sTmp)=(if Spec.Rsa.os2ip bs=0 then 0#64 else 1#64) := by
    rw [arrays_header frameD (by decide),nonzeroC,valueB]
   rw [WP.seq_iff]
   refine WP.mono (less_ok goodD room wPositive wSize (by decide : 1<8) (by decide : 5<8)) ?_
   rintro e ⟨lessE,memE,restE⟩
   rw [valueD,boundD] at lessE
   obtain rest := ((before.trans restD).trans restE)
   obtain maskE : word e.mem B (8*sTmp)=(if Spec.Rsa.os2ip bs=0 then 0#64 else 1#64) := by rw [memE];exact nzD
   obtain flag : (if Spec.Rsa.os2ip bs<Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) then 1#64 else 0#64) &&&
    (if Spec.Rsa.os2ip bs=0 then 0#64 else 1#64)=
    (if 0<Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs<Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) then 1#64 else 0#64) := by
    split <;> split <;> rename_i h₁ h₂ <;> simp [h₁, h₂]
   refine WP.mono (WP.keep [.x3,.x9] (Q:=fun t =>
    t.gpr .x9=(if 0<Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs<Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) then 1#64 else 0#64) ∧ t.mem=e.mem)
    ?_ rfl rfl rfl) ?_
   · brun [(rest.gpr .x0 (by simp [mmRegs])).trans good.x0,hdr_enc (show sTmp<32 by decide),
      (good.scr.congr rest.wr).ld (d:=8*sTmp) (by have := hdr_lt_slot w 8 (show sTmp<32 by decide);omega_using [room, this]),maskE,lessE,flag]
   · rintro t ⟨⟨flagT,memT⟩,restT⟩
     obtain total : Keep mmRegs s t := (rest.trans restT).mono (by decide)
     obtain same : t.mem=d.mem := memT.trans memE
     obtain goodT : Good t B Z w mi :=
      ⟨good.scr.congr total.wr,(total.gpr .x0 (by simp [mmRegs])).trans good.x0,same ▸ goodD.hdr⟩
     obtain first : Frm B (scalarRanges w) s.mem b.mem := by
      rw [←memA];exact Frm.of_arrays frameB (by simp [scalarRanges])
     obtain second : Frm B (scalarRanges w) b.mem c.mem := Frm.of_outside frameC (by simp [scalarRanges])
     obtain third : Frm B (scalarRanges w) c.mem d.mem := Frm.of_arrays frameD (by simp [scalarRanges])
     exact ⟨goodT,by rw [same];exact valueD,flagT,by rw [same];exact (first.trans second).trans third,total⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.PublicRange`, which only this module used -/

section

/-! Public powers are checked for 1<y<p−1 without repeating their proven subgroup test. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def publicRangeRanges (w : Nat) : List (Nat × Nat) := [(slot w 1,8*(w+2)),(8*sTmp,8)]

theorem publicRange_ok {p : Parameters} {s : State} (state : ModState p s) (odd : p.P%2=1) :
 WP isa Generate.publicRange s fun t =>
 ModState p t ∧ wv t.mem p.B (slot p.w 6) p.w=wv s.mem p.B (slot p.w 6) p.w ∧
 t.gpr .x9=(if 1<wv s.mem p.B (slot p.w 6) p.w ∧ wv s.mem p.B (slot p.w 6) p.w<p.P-1 then 1#64 else 0#64) ∧
 word t.mem p.B (8*sTmp)=t.gpr .x9 ∧ Frm p.B (publicRangeRanges p.w) s.mem t.mem ∧ Keep mmRegs s t := by
 obtain positive : 0<p.w := by have := p.positive;omega_using [this]
 obtain nowrap : p.B.toNat+slot p.w 8≤2^64 := by have := state.good.scr.nowrap;have := p.room;omega_arith
 obtain yRoom := slot_le (w:=p.w) (show 6<8 by decide)
 unfold Generate.publicRange
 simp only [seqs]
 rw [WP.seq_iff]
 refine WP.mono (less_ok state.good p.room positive p.width (by decide : 7<8) (by decide : 6<8)) ?_
 rintro a ⟨valueA,memA,restA⟩
 rw [state.one] at valueA
 obtain stateA := state.after_mem memA restA ((restA.gpr .x0 (by simp [mmRegs])).trans state.good.x0)
 rw [WP.seq_iff]
 refine WP.mono (store_control_ok stateA.good p.room (by decide : 16≤sTmp) (by decide : sTmp<32) .x9) ?_
 rintro b ⟨goodB,memB,frameB,restB⟩
 obtain stateB := stateA.after_header goodB frameB (by decide : sTmp<32)
 obtain flagB : word b.mem p.B (8*sTmp)=(if 1<wv s.mem p.B (slot p.w 6) p.w then 1#64 else 0#64) := by
  rw [memB,word_writeW_self];exact valueA
 obtain yB : wv b.mem p.B (slot p.w 6) p.w=wv s.mem p.B (slot p.w 6) p.w := by
  rw [frameB.wv (Or.inr (hdr_lt_slot p.w 6 (show sTmp<32 by decide))) (by omega_using [nowrap, yRoom]),memA]
 rw [WP.seq_iff]
 refine WP.mono (copy_ok goodB p.room positive p.width (by decide : 1<8) (by decide : 6<8) (by decide)) ?_
 rintro c ⟨goodC,valueC,frameC,restC⟩
 obtain stateC := stateB.after_arrays goodC frameC (by decide) (by decide) (by decide)
 rw [WP.seq_iff]
 refine WP.mono (setLowBit_ok goodC p.room positive) ?_
 rintro d ⟨goodD,valueD,frameD,restD⟩
 obtain stateD := stateC.after_arrays goodD frameD (by decide) (by decide) (by decide)
 obtain valueD : wv d.mem p.B (slot p.w 1) p.w=2*(wv s.mem p.B (slot p.w 6) p.w/2)+1 := by rw [valueD,valueC,yB]
 obtain yD : wv d.mem p.B (slot p.w 6) p.w=wv s.mem p.B (slot p.w 6) p.w :=
  (frameD.wv_of_not_mem (by decide) (by decide) nowrap).trans
   ((frameC.wv_of_not_mem (by decide) (by decide) nowrap).trans yB)
 obtain flagD : word d.mem p.B (8*sTmp)=(if 1<wv s.mem p.B (slot p.w 6) p.w then 1#64 else 0#64) := by
  rw [arrays_header frameD (by decide),arrays_header frameC (by decide)];exact flagB
 rw [WP.seq_iff]
 refine WP.mono (less_ok goodD p.room positive p.width (by decide : 1<8) (by decide : 0<8)) ?_
 rintro e ⟨valueE,memE,restE⟩
 rw [valueD,stateD.modulus] at valueE
 simp only [VG.Proof.Ffdh.lt_pm1 odd] at valueE
 obtain total := (((restA.trans restB).trans restC).trans restD).trans restE
 obtain goodE := good_after_mem goodD memE restE ((restE.gpr .x0 (by simp [mmRegs])).trans goodD.x0)
 obtain flagE : word e.mem p.B (8*sTmp)=(if 1<wv s.mem p.B (slot p.w 6) p.w then 1#64 else 0#64) := by rw [memE];exact flagD
 let flag : Addr := if 1<wv s.mem p.B (slot p.w 6) p.w ∧ wv s.mem p.B (slot p.w 6) p.w<p.P-1 then 1#64 else 0#64
 obtain combine : (if wv s.mem p.B (slot p.w 6) p.w<p.P-1 then 1#64 else 0#64) &&&
  (if 1<wv s.mem p.B (slot p.w 6) p.w then 1#64 else 0#64)=flag := by
  unfold flag
  split <;> split <;> simp_all
 refine WP.mono (WP.keep [.x3,.x9] (Q:=fun t =>t.gpr .x9=flag ∧ t.mem=e.mem.writeW (off p.B (8*sTmp)) flag) ?_ rfl rfl rfl) ?_
 · brun [goodE.x0,hdr_enc (show sTmp<32 by decide),header_read goodE p.room (show sTmp<32 by decide),
    goodE.scr.st (d:=8*sTmp) (by have := hdr_lt_slot p.w 8 (show sTmp<32 by decide);have := p.room;omega_arith),
    flagE,valueE,combine]
 · rintro t ⟨⟨flagT,memT⟩,restT⟩
   obtain frameT : Outside p.B (8*sTmp) 8 e.mem t.mem := by rw [memT];exact writeW_outside _ _ _ (by decide)
   obtain stateE := stateD.after_mem memE restE goodE.x0
   obtain goodT := good_after_header goodE (by decide) (by decide) frameT restT ((restT.gpr .x0 (by decide)).trans goodE.x0)
   obtain stateT := stateE.after_header goodT frameT (by decide)
   obtain yT : wv t.mem p.B (slot p.w 6) p.w=wv s.mem p.B (slot p.w 6) p.w := by
    rw [frameT.wv (Or.inr (hdr_lt_slot p.w 6 (show sTmp<32 by decide))) (by omega_using [nowrap, yRoom]),memE];exact yD
   obtain first : Frm p.B (publicRangeRanges p.w) s.mem b.mem := by
    rw [←memA];exact Frm.of_outside frameB (by simp [publicRangeRanges])
   obtain middle : Frm p.B (publicRangeRanges p.w) b.mem d.mem :=
    (Frm.of_arrays frameC (by simp [publicRangeRanges])).trans (Frm.of_arrays frameD (by simp [publicRangeRanges]))
   obtain last : Frm p.B (publicRangeRanges p.w) d.mem t.mem := by
    rw [←memE];exact Frm.of_outside frameT (by simp [publicRangeRanges])
   exact ⟨stateT,yT,flagT,by rw [memT,word_writeW_self,flagT],(first.trans middle).trans last,
    (total.trans restT).mono (by simp [mmRegs])⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end


/-! Range checks preserve the canonical field, scalar bytes and comb controls. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem scalarRanges_le (w : Nat) : ∀ r∈scalarRanges w,r.1+r.2≤slot w 8 := by
 simp only [scalarRanges,List.mem_cons,List.not_mem_nil,or_false]
 rintro _ (rfl|rfl|rfl)
 all_goals dsimp only [slot,hdrBytes,sTmp];omega_using []

theorem publicRangeRanges_le (w : Nat) : ∀ r∈publicRangeRanges w,r.1+r.2≤slot w 8 := by
 simp only [publicRangeRanges,List.mem_cons,List.not_mem_nil,or_false]
 rintro _ (rfl|rfl)
 all_goals dsimp only [slot,hdrBytes,sTmp];omega_using []

theorem scalarFrame_header {B : Addr} {w i : Nat} {m m' : Mem}
 (frame : Frm B (scalarRanges w) m m') (inside : i<32) (different : i≠sTmp) :
 word m' B (8*i)=word m B (8*i) := by
 apply frame.word_eq _ (by omega_using [inside])
 simp only [scalarRanges,List.mem_cons,List.not_mem_nil,or_false]
 rintro _ (rfl|rfl|rfl)
 all_goals dsimp only [slot,hdrBytes,sTmp] at *;omega_arith

theorem publicRangeFrame_header {B : Addr} {w i : Nat} {m m' : Mem}
 (frame : Frm B (publicRangeRanges w) m m') (inside : i<32) (different : i≠sTmp) :
 word m' B (8*i)=word m B (8*i) := by
 apply frame.word_eq _ (by omega_using [inside])
 simp only [publicRangeRanges,List.mem_cons,List.not_mem_nil,or_false]
 rintro _ (rfl|rfl)
 all_goals dsimp only [slot,hdrBytes,sTmp] at *;omega_arith

theorem FieldInitial.after_scalarRange {p : Parameters} {s t : State}
 (field : FieldInitial p s) (good : Good t p.B p.Z p.w p.mi) (frame : Frm p.B (scalarRanges p.w) s.mem t.mem) : FieldInitial p t := by
 obtain nowrap : slot p.w 8≤2^64 := by have := field.good.scr.nowrap;have := p.room;omega_arith
 have same (j : Nat) (allowed : j=0 ∨ j=4) : wv t.mem p.B (slot p.w j) p.w=wv s.mem p.B (slot p.w j) p.w := by
  apply frame.wv_eq
  · simp only [scalarRanges,List.mem_cons,List.not_mem_nil,or_false]
    rintro _ (rfl|rfl|rfl)
    all_goals rcases allowed with rfl|rfl <;> dsimp only [slot,hdrBytes,sTmp] <;>omega_using []
  · rcases allowed with rfl|rfl <;> dsimp only [slot,hdrBytes] at * <;>omega_using [nowrap]
 obtain wordSame : word t.mem p.B (slot p.w 0)=word s.mem p.B (slot p.w 0) := by
  apply frame.word_eq
  · simp only [scalarRanges,List.mem_cons,List.not_mem_nil,or_false]
    rintro _ (rfl|rfl|rfl)
    all_goals have := p.positive;dsimp only [slot,hdrBytes,sTmp];omega_using []
  · have := p.positive;dsimp only [slot,hdrBytes] at *;omega_using []
 refine ⟨good,(same 0 (by simp)).trans field.modulus,?_,(same 4 (by simp)).trans field.r2⟩
 rw [wordSame]
 exact field.inverse

theorem Controls.after_scalarRange {B src ctx : Addr} {k N w : Nat} {m : State} {t : State}
 (h : Controls B src ctx k N m) (frame : Frm B (scalarRanges w) m.mem t.mem) : Controls B src ctx k N t :=
 ⟨(scalarFrame_header frame (by decide) (by decide)).trans h.context,
  (scalarFrame_header frame (by decide) (by decide)).trans h.source,
  (scalarFrame_header frame (by decide) (by decide)).trans h.length,
  (scalarFrame_header frame (by decide) (by decide)).trans h.bits,
  (scalarFrame_header frame (by decide) (by decide)).trans h.rows⟩

theorem Initial.after_scalarRange {p : Parameters} {s t : State} {bs : List Byte} {rs : List Reg}
 (h : Initial p bs s) (good : Good t p.B p.Z p.w p.mi) (frame : Frm p.B (scalarRanges p.w) s.mem t.mem)
 (rest : Keep rs s t) : Initial p bs t :=
 ⟨h.toFieldInitial.after_scalarRange good frame,h.controls.after_scalarRange frame,
  h.reads.after_inscr (InScr.of_frm frame (fun r hr =>Nat.le_trans (scalarRanges_le _ r hr) p.room)) rest⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! Byte views are exact fixed-length encodings, including leading zero padding. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem source_bytesAt {ptr : Addr} {bs : List Byte} {s : State} (source : Source ptr bs s) :
 Spec.Rsa.bytesAt s.mem ptr bs.length=bs := by
 apply List.ext_getElem
 · simp only [Spec.Rsa.bytesAt,List.length_map,List.length_range]
 · intro i hi hj
   simp only [Spec.Rsa.bytesAt,List.getElem_map,List.getElem_range]
   have value := source.bytes i hj
   simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some] using value

theorem source_of_bytesAt (s : State) (ptr : Addr) (k : Nat)
 (readable : ∀ i<k,InRegions (s.rd++s.wr) (ptr+BitVec.ofNat 64 i) 1) :
 Source ptr (Spec.Rsa.bytesAt s.mem ptr k) s := by
 constructor
 · intro i hi
   exact readable i (by simpa only [Spec.Rsa.bytesAt,List.length_map,List.length_range] using hi)
 · intro i hi
   have inside : i<k := by simpa only [Spec.Rsa.bytesAt,List.length_map,List.length_range] using hi
   simp only [Spec.Rsa.bytesAt,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range inside,Option.map_some,Option.getD_some]

theorem source_encoding {ptr : Addr} {bs : List Byte} {s : State} (source : Source ptr bs s) :
 Spec.Rsa.bytesAt s.mem ptr bs.length=Spec.Rsa.i2osp (Spec.Rsa.os2ip bs) bs.length := by
 rw [source_bytesAt source,VG.Proof.Rsa.i2osp_os2ip]

theorem source_src {ptr B : Addr} {Z : Nat} {bs : List Byte} {s : State}
 (source : Source ptr bs s) (outside : ∀ i<bs.length,Z≤ofs B (ptr+BitVec.ofNat 64 i)) : Src s B Z ptr bs := by
 refine ⟨source.readable,?_,outside⟩
 intro i hi
 simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some] using source.bytes i hi

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.ScalarTimingState`, which only this module used -/

section

/-! The rejection checks preserve all public controls and immutable scalar/context inputs. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure ScalarPublic where
 p : Parameters
 dp : Addr
 dl : Nat
 dom : List Byte
 words : p.w=(p.k+7)/8
 positive : 0<p.k
 size : p.k<2^31
 shape : dl=2*p.k ∨ dl=3*p.k
 domLength : dom.length=dl
 modulus : p.P=(Spec.Ffdh.domainOf p.k dom).p
 odd : p.P%2=1

structure ScalarState (q : ScalarPublic) (bs : List Byte) (s : State) : Prop where
 initial : Initial q.p bs s
 length : bs.length=q.p.k
 source : Src s q.p.B q.p.Z q.dp q.dom
 domain : word s.mem q.p.B (8*sDom)=q.dp
 domainLength : word s.mem q.p.B (8*sDL)=BitVec.ofNat 64 q.dl

def ScalarReady (q : ScalarPublic) (s : State) : Prop := ∃ bs,ScalarState q bs s

theorem ScalarState.after {q : ScalarPublic} {bs : List Byte} {s t : State} {rs : List Reg}
 (h : ScalarState q bs s) (good : Good t q.p.B q.p.Z q.p.w q.p.mi)
 (frame : Frm q.p.B (scalarRanges q.p.w) s.mem t.mem) (rest : Keep rs s t) : ScalarState q bs t :=
 ⟨h.initial.after_scalarRange good frame rest,h.length,
  h.source.congrK (InScr.of_frm frame (fun r hr =>Nat.le_trans (scalarRanges_le _ r hr) q.p.room)) rest,
  (scalarFrame_header frame (by decide) (by decide)).trans h.domain,
  (scalarFrame_header frame (by decide) (by decide)).trans h.domainLength⟩

theorem ScalarState.after_mem {q : ScalarPublic} {bs : List Byte} {s t : State} {rs : List Reg}
 (h : ScalarState q bs s) (mem : t.mem=s.mem) (rest : Keep rs s t) (base : t.gpr .x0=q.p.B) : ScalarState q bs t :=
 h.after (good_after_mem h.initial.good mem rest base) (fun a _ =>by rw [mem]) rest

def scalarWs (q : ScalarPublic) : Ws := ⟨q.p.B,q.p.Z,q.p.w⟩

def scalarBoundPublic (q : ScalarPublic) : BoundPublic :=
 ⟨scalarWs q,q.dp,q.p.k,q.dl,by change 0<q.p.w;have :=q.p.positive;omega_using [this],q.p.width,q.size,q.shape⟩

theorem scalarReady_bound {q : ScalarPublic} {s : State} (h : ScalarReady q s) : BoundReady (scalarBoundPublic q) s := by
 obtain ⟨bs,h⟩ :=h
 exact ⟨⟨q.p.mi,h.initial.good,q.p.room⟩,h.domain,(by change word s.mem q.p.B (8*sLen)=BitVec.ofNat 64 q.p.k;rw [←h.length];exact h.initial.controls.length),h.domainLength⟩

theorem scalarReady_nonzero {q : ScalarPublic} {s : State} (h : ScalarReady q s) :
 WP isa Generate.nonzero s (ScalarReady q) := by
 obtain ⟨bs,h⟩ :=h
 refine WP.mono (nonzero_ok h.initial.good q.p.room (by have :=q.p.positive;omega_using [this]) q.p.width) ?_
 rintro t ⟨good,_,_,frame,rest⟩
 exact ⟨bs,h.after good (Frm.of_outside frame (by simp [scalarRanges])) rest⟩

theorem scalarReady_bound_ok {q : ScalarPublic} {s : State} (h : ScalarReady q s) :
 WP isa Generate.bound s (ScalarReady q) := by
 obtain ⟨bs,h⟩ :=h
 refine WP.mono (scalarBound_ok h.initial.good q.p.room q.words q.positive q.size q.shape q.domLength h.source
  h.domain (h.length ▸ h.initial.controls.length) h.domainLength (h.initial.modulus.trans q.modulus)
  (by rw [←q.modulus];exact q.odd)) ?_
 rintro t ⟨good,_,frame,rest⟩
 exact ⟨bs,h.after good (Frm.of_arrays frame (by simp [scalarRanges])) rest⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end


/-! The complete scalar rejection predicate scans a fixed public geometry. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def ScalarLoadReady (q : ScalarPublic) (s : State) : Prop :=
 ScalarReady q s ∧ s.gpr .x1=q.p.src ∧ s.gpr .x2=BitVec.ofNat 64 q.p.k

theorem scalarRange_ct : RelCT isa (Two ScalarReady) Generate.scalarRange (fun _ _ =>True) := by
 unfold Generate.scalarRange
 simp only [seqs]
 refine RelCT.seq (two_piece (Ψ:=ScalarLoadReady) [.x0] ?_ (by taint_decide) ?_) ?_
 · rintro q s t ⟨bs,hs⟩ ⟨bt,ht⟩ r hr
   have eq : r= .x0 := by simpa using hr
   subst r
   exact hs.initial.good.x0.trans ht.initial.good.x0.symm
 · rintro q s ⟨bs,h⟩
   have good := h.initial.good
   have x := h.initial.controls.source
   have len := h.initial.controls.length
   rw [h.length] at len
   refine WP.mono (WP.keep [.x1,.x2] (Q:=fun t =>
    t.gpr .x1=q.p.src ∧ t.gpr .x2=BitVec.ofNat 64 q.p.k ∧ t.mem=s.mem) ?_ rfl rfl rfl) ?_
   · brun [good.x0,hdr_enc (show sX<32 by decide),hdr_enc (show sLen<32 by decide),
      header_read good q.p.room (show sX<32 by decide),header_read good q.p.room (show sLen<32 by decide),x,len]
   · rintro t ⟨⟨ptr,len,mem⟩,rest⟩
     exact ⟨⟨bs,h.after_mem mem rest ((rest.gpr .x0 (by decide)).trans good.x0)⟩,ptr,len⟩
 · refine RelCT.seq (two_post (Ψ:=ScalarReady)
    (two_map (fun q =>(⟨scalarWs q,q.p.src,q.p.k⟩ : LoadPublic))
     (fun q s h =>by obtain ⟨⟨bs,h⟩,ptr,len⟩:=h;exact ⟨⟨q.p.mi,h.initial.good,q.p.room⟩,ptr,len⟩)
     (load_ct (by decide : 1<8) (by taint_decide))) ?_) ?_
   · rintro q s ⟨⟨bs,h⟩,ptr,len⟩
     refine WP.mono (loadArray_ok h.initial.good q.p.room q.words q.positive q.size (by decide : 1<8)
      (source_src h.initial.reads.source h.initial.reads.scalarOutside) h.length ptr len) ?_
     rintro t ⟨good,_,frame,rest⟩
     exact ⟨bs,h.after good (Frm.of_arrays frame (by simp [scalarRanges])) rest⟩
   · refine RelCT.seq (two_post (Ψ:=ScalarReady)
      (two_map scalarWs (fun q s h =>by obtain ⟨bs,h⟩:=h;exact ⟨q.p.mi,h.initial.good,q.p.room⟩) nonzero_ct)
      (fun _ _ h =>scalarReady_nonzero h)) ?_
     refine RelCT.seq (two_post (Ψ:=ScalarReady)
      (two_map scalarBoundPublic (fun _ _ h =>scalarReady_bound h) scalarBound_ct)
      (fun _ _ h =>scalarReady_bound_ok h)) ?_
     refine RelCT.seq (two_post (Ψ:=ScalarReady)
      (two_map scalarWs (fun q s h =>by obtain ⟨bs,h⟩:=h;exact ⟨q.p.mi,h.initial.good,q.p.room⟩)
       (less_ct (by decide : 1<8) (by decide : 5<8) (by taint_decide))) ?_)
      (two_taint [.x0] ?_ (by taint_decide))
     · rintro q s ⟨bs,h⟩
       refine WP.mono (less_ok h.initial.good q.p.room (by have :=q.p.positive;omega_using [this]) q.p.width
        (by decide : 1<8) (by decide : 5<8)) ?_
       rintro t ⟨_,mem,rest⟩
       exact ⟨bs,h.after_mem mem rest ((rest.gpr .x0 (by simp [mmRegs])).trans h.initial.good.x0)⟩
     · rintro q s t ⟨bs,hs⟩ ⟨bt,ht⟩ r hr
       have eq : r= .x0 := by simpa using hr
       subst r
       exact hs.initial.good.x0.trans ht.initial.good.x0.symm

end VG.Proof.Ffdh.AArch64.Cached
