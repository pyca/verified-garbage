module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.BoundHead
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Copy
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Generate
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.LoadArray
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SourceSlices
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Nonzero
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Less
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Controls
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.MemoryState
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SetLowBit
public import VerifiedGarbage.Proof.Ffdh.Domain
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Initial

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
