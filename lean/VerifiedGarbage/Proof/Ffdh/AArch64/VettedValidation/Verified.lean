module

import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.VettedValidation
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyLoop
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SourceSlices
public import VerifiedGarbage.Impl.Ffdh.AArch64.Domain
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody
public import VerifiedGarbage.Spec.Ffdh.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.CT
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Ffdh.VettedValidation.Facts
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyTable
import VerifiedGarbage.Impl.Ffdh.VettedGroups
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyLoopTiming
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import Batteries.Logic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.Contract
meta import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Impl.Ffdh.AArch64.VettedValidation
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Bit
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.Contract
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyConsts
public import VerifiedGarbage.Proof.Framework.AArch64.Inline

/-! ### `Ffdh.AArch64.VettedValidation.Recognize`, which only this module used -/

section

/-! ### `Ffdh.AArch64.VettedValidation.Contract`, which this module and modules that import it used -/

section

/-! The unchanged domain-check contract with its public recognition table. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.VettedValidation
open VG VG.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open CheckDomain

abbrev plain (s : State) : State := stripConsts Policy.tableConsts s

def pre (s : State) : Prop := cdPre (plain s) ∧ ConstsOk Policy.tableConsts 0 s

def pub (s t : State) : Prop := cdPub s t ∧ s.syms Policy.tableSym=t.syms Policy.tableSym

def contract : Contract isa where
  pre := pre
  post := cdPost
  pub := pub

theorem shared_pre {s : State}
    (h : (Spec.Ffdh.checkDomainContract (abi.withConsts Policy.tableConsts)).pre s) : pre s := by
  obtain ⟨h,c⟩:=pre_consts.mp h
  exact ⟨cd_implies.pre _ h,c⟩

theorem shared_post {s t : State} (h : cdPost s t) :
    (Spec.Ffdh.checkDomainContract (abi.withConsts Policy.tableConsts)).post s t := by
  apply post_consts.mpr
  have post : ∀ s t, True → cdPost s t → (Spec.Ffdh.checkDomainContract abi).post s t := by
    sig_implies_post [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs, cdPost, cdDom]
  exact post s t True.intro h

end VG.Proof.Ffdh.AArch64.VettedValidation

end

end

/-! ### `Ffdh.AArch64.VettedValidation.Entry`, which only this module used -/

section

/-! Save the public input arguments and initialize an unmatched recognition sentinel. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.VettedValidation
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

private theorem execAdr (s : State) (r : Reg) (sym : String) :
  exec (.adrSym r sym) s=some (s.write .x r (s.syms sym)) := rfl

def entryMemory (m : Mem) (B dom dl k words : Addr) : Mem :=
  ((((m.writeW (off B (8*sDom)) dom).writeW (off B (8*sDL)) dl).writeW
    (off B (8*sLen)) k).writeW (off B (8*sCtx)) words).writeW (off B (8*sBits)) (4095#64)

theorem entry_ok {s : State} {B : Addr} {Z : Nat}
    (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x3=B) :
    WP isa (.block VG.Impl.Ffdh.AArch64.VettedValidation.entry) s fun t =>
    (t.gpr .x0=B ∧ t.gpr .x4=s.syms Policy.tableSym ∧ t.gpr .x7=10#64 ∧
      t.mem=entryMemory s.mem B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x4)) ∧
    Keep [.x0,.x4,.x7,.x10] s t := by
  refine WP.keep [.x0,.x4,.x7,.x10] ?_ rfl rfl rfl
  unfold VG.Impl.Ffdh.AArch64.VettedValidation.entry entryMemory
  brun [base,st,execAdr,hdr_enc (show sBits<32 by decide),
    scratch.st (d:=8*sDom) (by unfold sDom;omega_using [room]),
    scratch.st (d:=8*sDL) (by unfold sDL;omega_using [room]),
    scratch.st (d:=8*sLen) (by unfold sLen;omega_using [room]),
    scratch.st (d:=8*sCtx) (by unfold sCtx;omega_using [room]),
    scratch.st (d:=8*sBits) (by unfold sBits;omega_using [room])]
  exact ⟨rfl,rfl⟩

theorem entryMemory_header (m : Mem) (B dom dl k words : Addr) :
    word (entryMemory m B dom dl k words) B (8*sDom)=dom ∧
    word (entryMemory m B dom dl k words) B (8*sDL)=dl ∧
    word (entryMemory m B dom dl k words) B (8*sLen)=k ∧
    word (entryMemory m B dom dl k words) B (8*sCtx)=words ∧
    word (entryMemory m B dom dl k words) B (8*sBits)=4095#64 := by
  have separate (m : Mem) (i j : Nat) (hi : i<32) (hj : j<32) (different : i≠j) (v : Addr) :
      word (m.writeW (off B (8*i)) v) B (8*j)=word m B (8*j) :=
    Mem.readW_writeW_sep (Offset.sep B (by omega_using [different]) (by omega_using [hj]) (by omega_using [hi])) (by decide)
  unfold entryMemory
  rw [separate _ sBits sDom (by decide) (by decide) (by decide),separate _ sCtx sDom (by decide) (by decide) (by decide),
    separate _ sLen sDom (by decide) (by decide) (by decide),separate _ sDL sDom (by decide) (by decide) (by decide),word_writeW_self,
    separate _ sBits sDL (by decide) (by decide) (by decide),separate _ sCtx sDL (by decide) (by decide) (by decide),
    separate _ sLen sDL (by decide) (by decide) (by decide),word_writeW_self,
    separate _ sBits sLen (by decide) (by decide) (by decide),separate _ sCtx sLen (by decide) (by decide) (by decide),word_writeW_self,
    separate _ sBits sCtx (by decide) (by decide) (by decide),word_writeW_self,word_writeW_self]
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem entryMemory_range (m : Mem) (B dom dl k words : Addr) :
    Outside B 128 40 m (entryMemory m B dom dl k words) := by
  intro x hx
  have store (m : Mem) (i : Nat) (low : 16≤i) (high : i<21) (v : Addr) :
      (m.writeW (off B (8*i)) v) x=m x :=
    writeW_outside m B v (by omega_using [high]) x (by omega_using [hx, low, high])
  unfold entryMemory
  rw [store _ sBits (by decide) (by decide),store _ sCtx (by decide) (by decide),
    store _ sLen (by decide) (by decide),store _ sDL (by decide) (by decide),
    store _ sDom (by decide) (by decide)]

end VG.Proof.Ffdh.AArch64.VettedValidation

end

end

/-! Exact public recognition is safe for every permitted input, including invalid domains. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/VettedValidation/Geometry.lean`, which only this module imported.
section

/-! The existing domain-check ABI supplies the recognizer's buffer geometry. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.VettedValidation
open VG VG.AArch64 VG.Impl.Bignum
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open Cached

structure Geometry (s : State) : Prop where
  small : 64≤(s.gpr .x2).toNat
  large : (s.gpr .x2).toNat≤1024
  shape : (s.gpr .x1).toNat=2*(s.gpr .x2).toNat ∨ (s.gpr .x1).toNat=3*(s.gpr .x2).toNat
  scratch : Scr s (s.gpr .x3) ((s.gpr .x4).toNat*8)
  room : 256≤(s.gpr .x4).toNat*8
  source : Source (s.gpr .x0) (CheckDomain.cdDom s) s
  outside : ∀ i<(CheckDomain.cdDom s).length,168≤ofs (s.gpr .x3) (s.gpr .x0+BitVec.ofNat 64 i)
  records : PolicyTableAt (s.gpr .x3) (s.syms Policy.tableSym) Policy.groups s

theorem geometry {s : State} (h : pre s) : Geometry s := by
  obtain ⟨hp,constants⟩:=h
  simp only [CheckDomain.cdPre,stripConsts_gpr,stripConsts_wr] at hp
  obtain ⟨rd,wr,disjoint,domainWrap,scratchWrap,⟨small,large⟩,shape,length⟩:=hp
  change (s.gpr .x1).toNat=2*(s.gpr .x2).toNat ∨ (s.gpr .x1).toNat=3*(s.gpr .x2).toNat at shape
  change s.rd.take (s.rd.length-Policy.tableConsts.length)=[⟨s.gpr .x0,(s.gpr .x1).toNat⟩] at rd
  have member : (⟨s.gpr .x0,(s.gpr .x1).toNat⟩ : Region)∈s.rd := by
    apply List.mem_of_mem_take
    rw [rd];simp
  have scratch : Scr s (s.gpr .x3) ((s.gpr .x4).toNat*8) :=
    Scr.of_mem (by rw [wr];simp) scratchWrap
  have room : 256≤(s.gpr .x4).toNat*8 := by
    unfold Spec.Rsa.scratchWords at length
    omega_using [length]
  have src :=src_of_region (List.mem_append_left s.wr member) (by omega_using []) disjoint
  refine ⟨small,large,shape,scratch,room,src_source src,?_,policyConsts_table constants scratch room⟩
  intro i hi
  have bound :=src.out i hi
  omega

end VG.Proof.Ffdh.AArch64.VettedValidation
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.VettedValidation
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open Cached

private theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat=x := by simp

def clobbers : List Reg := .x0::recordClobbers

def width (s : State) : Nat := policyWidth 4095 (s.gpr .x2).toNat (CheckDomain.cdDom s) Policy.groups

structure Result (s t : State) : Prop where
  base : t.gpr .x0=s.gpr .x3
  test : t.gpr .x10=BitVec.ofNat 64 (width s)-4095#64
  savedDomain : word t.mem (s.gpr .x3) (8*sDom)=s.gpr .x0
  savedLength : word t.mem (s.gpr .x3) (8*sDL)=s.gpr .x1
  savedKeyLength : word t.mem (s.gpr .x3) (8*sLen)=s.gpr .x2
  savedWords : word t.mem (s.gpr .x3) (8*sCtx)=s.gpr .x4
  frame : Outside (s.gpr .x3) 128 40 s.mem t.mem
  keep : Keep clobbers s t

theorem width_le (s : State) : width s≤4095 := by
  have bound (gs : List Policy.Group) : policyWidth 4095 (s.gpr .x2).toNat (CheckDomain.cdDom s) gs≤4095 := by
    induction gs with
    | nil => exact Nat.le_refl _
    | cons g gs ih =>
      unfold policyWidth
      split
      · exact Nat.min_le_left _ _
      · exact ih
  exact bound _

theorem recognize_ok {s : State} (g : Geometry s) :
    WP isa VG.Impl.Ffdh.AArch64.VettedValidation.recognize s (Result s) := by
  unfold VG.Impl.Ffdh.AArch64.VettedValidation.recognize
  rw [WP.seq_iff]
  refine WP.mono (entry_ok g.scratch g.room rfl) ?_
  rintro a ⟨⟨baseA,ptrA,countA,memA⟩,restA⟩
  have headers :=entryMemory_header s.mem (s.gpr .x3) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x4)
  have frameA : Outside (s.gpr .x3) 128 40 s.mem a.mem := by
    rw [memA];exact entryMemory_range _ _ _ _ _ _
  have recordsA :=g.records.after_belowBits frameA restA (by decide)
  have sourceA :=g.source.after_outside frameA restA g.outside
  rw [WP.seq_iff]
  refine WP.mono (policyLoop_ok (g.scratch.congr restA.wr) g.room baseA sourceA recordsA
    (by simpa only [CheckDomain.cdDom,Spec.Rsa.bytesAt,List.length_map,List.length_range] using g.shape)
    (by have :=g.small;omega_using [this]) (by have :=g.large;omega_using [this])
    (by rw [memA];exact headers.1)
    (by rw [memA];simpa only [CheckDomain.cdDom,Spec.Rsa.bytesAt,List.length_map,List.length_range,ofNat_toNat64] using headers.2.1)
    (by rw [memA];simpa only [ofNat_toNat64] using headers.2.2.1)
    (by rw [memA];exact headers.2.2.2.2) (by decide) ptrA countA (by decide) (by decide)) ?_
  rintro b ⟨bitsB,frameB,restB⟩
  have baseB :=(restB.gpr .x0 (by simp [recordClobbers])).trans baseA
  have headerB (i : Nat) (hi : i<32) (different : i≠sBits) :
      word b.mem (s.gpr .x3) (8*i)=word a.mem (s.gpr .x3) (8*i) :=
    header_other frameB (by decide) hi different
  refine WP.mono (WP.keep [.x10] (Q:=fun t =>t.gpr .x10=BitVec.ofNat 64 (width s)-4095#64 ∧ t.mem=b.mem) ?_ rfl rfl rfl) ?_
  · brun [baseB,hdr_enc (show sBits<32 by decide),((g.scratch.congr restA.wr).congr restB.wr).ld (d:=8*sBits) (by unfold sBits;have :=g.room;omega_using [this]),
      bitsB,width]
  · rintro t ⟨⟨testT,memT⟩,restT⟩
    refine ⟨(restT.gpr .x0 (by simp)).trans baseB,testT,?_,?_,?_,?_,?_,?_⟩
    · rw [memT,headerB sDom (by decide) (by decide),memA];exact headers.1
    · rw [memT,headerB sDL (by decide) (by decide),memA];exact headers.2.1
    · rw [memT,headerB sLen (by decide) (by decide),memA];exact headers.2.2.1
    · rw [memT,headerB sCtx (by decide) (by decide),memA];exact headers.2.2.2.1
    · rw [memT];exact frameA.trans (frameB.mono (by decide) (by decide))
    · exact ((restA.trans restB).trans restT).mono (by
        intro r hr
        simp only [List.mem_append] at hr
        rcases hr with (hr|hr)|hr
        · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
          rcases hr with rfl|rfl|rfl|rfl <;> decide
        · exact List.mem_cons_of_mem _ hr
        · have same : r= .x10 := by simpa using hr
          subst r
          decide)


end VG.Proof.Ffdh.AArch64.VettedValidation

end

end

/-! ### `Ffdh.AArch64.VettedValidation.Sat`, which only this module used -/

section

/-! A permitted domain buffer and disjoint public table witness contract satisfiability. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.VettedValidation
open VG VG.AArch64
open VG.Impl.Ffdh.AArch64.Cached

private def satState (W : List (BitVec 64)) : State where
  gpr r := match r with
    | .x0=>0x1000 | .x1=>128 | .x2=>64 | .x3=>0x9000 | .x4=>1056 | _=>0
  sp:=0x8000
  mem:=constMem 0x200000 W
  rd:=[⟨0x1000,128⟩,⟨0x200000,17744⟩]
  wr:=[⟨0x9000,8448⟩]
  syms:=fun _=>0x200000

private theorem shared_sat_aux (W : List (BitVec 64)) (length : W.length=2218) :
    ∃s,(Spec.Ffdh.checkDomainContract (abi.withConsts [(Policy.tableSym,W)])).pre s := by
  refine ⟨satState W,pre_consts.mpr ⟨?_,?_⟩⟩
  · sig_pre [Spec.Ffdh.checkDomainContract,Spec.Ffdh.checkDomainSig,Spec.Ffdh.pLenValid,
      Spec.Ffdh.domainLenValid,Spec.Rsa.scratchWords,abi,argRegs]
    repeat' apply And.intro
    all_goals first
      | rfl
      | decide +kernel
      | (apply Region.disjoint_of_sep;decide +kernel)
  · refine ⟨?_,?_,?_,?_⟩
    · simp only [satState,constRegs,Abi.constRegions,List.map_cons,List.map_nil,length]
      rfl
    · intro c hc i hi
      simp only [List.mem_singleton] at hc
      subst c
      exact constMem_held 0x200000 W (by rw [length];decide) i hi
    · intro r hr
      simp only [constRegs,Abi.constRegions,List.mem_map,List.mem_singleton] at hr
      obtain ⟨c,rfl,rfl⟩:=hr
      rw [length]
      dsimp only [satState]
      refine ⟨by decide,?_,?_⟩
      · intro q hq
        change q∈([⟨0x9000,8448⟩] : List Region) at hq
        simp only [List.mem_singleton] at hq
        subst q
        apply Region.disjoint_of_sep
        decide
      · intro q hq
        simp only [abi,stackBelow,List.not_mem_nil] at hq
    · intro r hr
      simp only [constRegs,Abi.constRegions,List.mem_map,List.mem_singleton] at hr
      obtain ⟨c,rfl,rfl⟩:=hr
      dsimp only [satState]
      decide

theorem shared_sat : ∃s,(Spec.Ffdh.checkDomainContract (abi.withConsts Policy.tableConsts)).pre s :=
  shared_sat_aux Policy.tableWords Cached.Policy.tableWords_length

end VG.Proof.Ffdh.AArch64.VettedValidation

end

end

/-! ### `Ffdh.AArch64.VettedValidation.Timing`, which only this module used -/

section

/-! ### `Ffdh.AArch64.VettedValidation.RecognizeTiming`, which only this module used -/

section

/-! ### `Ffdh.AArch64.VettedValidation.TimingState`, which only this module used -/

section

/-! Public ABI values determine every recognition record and loop exit. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.VettedValidation
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open Cached

structure Public where
  ptr : Addr
  dl : Addr
  k : Addr
  B : Addr
  words : Addr
  table : Addr
  dom : List Byte
  small : 64≤k.toNat
  large : k.toNat≤1024
  room : 256≤words.toNat*8
  shape : dom.length=2*k.toNat ∨ dom.length=3*k.toNat
  length : dom.length=dl.toNat

structure Ready (q : Public) (s : State) : Prop where
  assumptions : pre s
  domain : s.gpr .x0=q.ptr
  length : s.gpr .x1=q.dl
  keyLength : s.gpr .x2=q.k
  base : s.gpr .x3=q.B
  words : s.gpr .x4=q.words
  bytes : CheckDomain.cdDom s=q.dom
  symbol : s.syms Policy.tableSym=q.table

def loopPublic (q : Public) : PolicyLoopPublic :=
  ⟨⟨q.B,q.words.toNat*8,q.ptr,q.table,q.dom,
    ⟨256,225,Spec.Ffdh.modp2048Prime⟩,q.k.toNat,q.room,q.shape,
    by have :=q.small;omega_using [this],by have :=q.large;omega_using [this]⟩,
    Policy.groups.tail,4095,by decide,by decide⟩

theorem entry_ready {q : Public} {s : State} (h : Ready q s) :
    WP isa (.block VG.Impl.Ffdh.AArch64.VettedValidation.entry) s (PolicyLoopReady (loopPublic q)) := by
  have g:=geometry h.assumptions
  refine WP.mono (entry_ok g.scratch g.room rfl) ?_
  rintro t ⟨⟨base,ptr,count,mem⟩,rest⟩
  have frame : Outside (s.gpr .x3) 128 40 s.mem t.mem := by rw [mem];exact entryMemory_range _ _ _ _ _ _
  have source :=g.source.after_outside frame rest g.outside
  have records :=g.records.after_belowBits frame rest (by decide)
  have head :=entryMemory_header s.mem (s.gpr .x3) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x4)
  rw [←mem] at head
  have table : PolicyTableAt q.B q.table Policy.groups t := by rw [←h.base,←h.symbol];exact records
  refine ⟨⟨?_,base.trans h.base,?_,table.1,?_,?_,?_,?_,ptr.trans h.symbol⟩,table,count⟩
  · change Scr t q.B (q.words.toNat*8)
    rw [←h.base,←h.words];exact g.scratch.congr rest.wr
  · change Source q.ptr q.dom t
    rw [←h.domain,←h.bytes];exact source
  · change word t.mem q.B (8*sDom)=q.ptr
    rw [←h.base,←h.domain];exact head.1
  · change word t.mem q.B (8*sDL)=BitVec.ofNat 64 q.dom.length
    rw [←h.base,q.length,←h.length,BitVec.ofNat_toNat,BitVec.setWidth_eq];exact head.2.1
  · change word t.mem q.B (8*sLen)=BitVec.ofNat 64 q.k.toNat
    rw [←h.base,←h.keyLength,BitVec.ofNat_toNat,BitVec.setWidth_eq];exact head.2.2.1
  · change word t.mem q.B (8*sBits)=4095#64
    rw [←h.base];exact head.2.2.2.2

end VG.Proof.Ffdh.AArch64.VettedValidation

end

end


/-! The recognizer leaks only the public inputs, with no dependence on scratch contents. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.VettedValidation
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open Cached

theorem entry_ct : RelCT isa (Two Ready)
    (.block VG.Impl.Ffdh.AArch64.VettedValidation.entry) (fun _ _ =>True) :=
  two_taint [.x3] (fun _ _ _ hs ht r hr =>by
    have same : r= .x3 := by simpa using hr
    subst r
    exact hs.base.trans ht.base.symm) (by taint_decide)

theorem loop_base {q : Public} {s : State} (h : PolicyLoopReady (loopPublic q) s) :
    WP isa (.loop Policy.record (.nonzero .x .x7)) s (fun t =>t.gpr .x0=q.B) := by
  have r:=h.record
  refine WP.mono (policyLoop_ok r.scratch q.room r.base r.source h.records q.shape
    (by have :=q.small;omega_using [this]) (by have :=q.large;omega_using [this]) r.domain r.length r.keyLength
    r.width (loopPublic q).fit r.pointer h.count (by simp) (by change 10<2^64;decide)) ?_
  rintro t ⟨_,_,rest⟩
  exact (rest.gpr .x0 (by simp [recordClobbers])).trans r.base

theorem recognize_ct : RelCT isa (Two Ready)
    VG.Impl.Ffdh.AArch64.VettedValidation.recognize (fun _ _ =>True) := by
  unfold VG.Impl.Ffdh.AArch64.VettedValidation.recognize
  refine RelCT.seq (two_post entry_ct (fun _ _ h =>entry_ready h)) ?_
  refine RelCT.seq (two_post (two_map loopPublic (fun _ _ h =>h) policyLoop_ct)
    (fun _ _ h =>loop_base h)) ?_
  exact two_taint [.x0] (fun _ _ _ hs ht r hr =>by
    have same : r= .x0 := by simpa using hr
    subst r
    exact hs.trans ht.symm) (by taint_decide)

end VG.Proof.Ffdh.AArch64.VettedValidation

end

end

/-! ### `Ffdh.AArch64.VettedValidation.Correct`, which this module and modules that import it used -/

section

/-! Recognized domains satisfy the original contract; every miss uses its original validator. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/VettedValidation/Restore.lean`, which only this module imported.
section

/-! A recognition miss restores exactly the original general-validator arguments. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.VettedValidation
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure Restored (s t : State) : Prop where
  args : t.gpr .x0=s.gpr .x0 ∧ t.gpr .x1=s.gpr .x1 ∧ t.gpr .x2=s.gpr .x2 ∧
    t.gpr .x3=s.gpr .x3 ∧ t.gpr .x4=s.gpr .x4
  domain : CheckDomain.cdDom t=CheckDomain.cdDom s
  keep : Keep clobbers s t

theorem restore_ok {s t : State} (g : Geometry s) (h : Result s t) :
    WP isa (.block VG.Impl.Ffdh.AArch64.VettedValidation.restore) t (Restored s) := by
  refine WP.mono (WP.keep [.x0,.x1,.x2,.x3,.x4] (Q:=fun u =>
    (u.gpr .x0=s.gpr .x0 ∧ u.gpr .x1=s.gpr .x1 ∧ u.gpr .x2=s.gpr .x2 ∧
     u.gpr .x3=s.gpr .x3 ∧ u.gpr .x4=s.gpr .x4) ∧ u.mem=t.mem) ?_ rfl rfl rfl) ?_
  · unfold VG.Impl.Ffdh.AArch64.VettedValidation.restore
    brun [h.base,hdr_enc (show sDom<32 by decide),hdr_enc (show sDL<32 by decide),
      hdr_enc (show sLen<32 by decide),hdr_enc (show sCtx<32 by decide),
      (g.scratch.congr h.keep.wr).ld (d:=8*sDom) (by unfold sDom;have :=g.room;omega_using [this]),
      (g.scratch.congr h.keep.wr).ld (d:=8*sDL) (by unfold sDL;have :=g.room;omega_using [this]),
      (g.scratch.congr h.keep.wr).ld (d:=8*sLen) (by unfold sLen;have :=g.room;omega_using [this]),
      (g.scratch.congr h.keep.wr).ld (d:=8*sCtx) (by unfold sCtx;have :=g.room;omega_using [this]),
      h.savedDomain,h.savedLength,h.savedKeyLength,h.savedWords]
  · rintro u ⟨⟨args,mem⟩,rest⟩
    refine ⟨args,?_,(h.keep.trans rest).mono (by
      intro r hr
      rcases List.mem_append.mp hr with hr|hr
      · exact hr
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl|rfl|rfl|rfl <;> decide)⟩
    unfold CheckDomain.cdDom
    rw [args.1,args.2.1,mem]
    unfold Spec.Rsa.bytesAt
    apply List.map_congr_left
    intro i hi
    exact h.frame _ (Or.inr (g.outside i (by simpa only [CheckDomain.cdDom,Spec.Rsa.bytesAt,List.length_map,List.length_range] using List.mem_range.mp hi)))

theorem Restored.pre {s t : State} (h : Restored s t) (hs : pre s) : CheckDomain.cdPre (plain t) := by
  obtain ⟨hp,_⟩:=hs
  simp only [CheckDomain.cdPre,stripConsts_gpr,stripConsts_wr] at hp ⊢
  rw [h.args.1,h.args.2.1,h.args.2.2.1,h.args.2.2.2.1,h.args.2.2.2.2]
  change t.rd.take (t.rd.length-Policy.tableConsts.length)=_ ∧ _
  rw [h.keep.rd,h.keep.wr]
  exact hp

theorem Restored.abi {s t : State} (h : Restored s t) : abiPreserved s t :=
  ⟨fun r hr =>h.keep.gpr r (by revert r;decide),h.keep.sp,h.keep.vcs⟩

end VG.Proof.Ffdh.AArch64.VettedValidation
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/VettedValidation/Fallback.lean`, which only this module imported.
section

/-! Extra read-only recognition constants do not change the general validator's behavior. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.VettedValidation
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open CheckDomain VG.Proof.Bignum.AArch64.WindowFive

theorem plain_covers (s : State) : Covers ((plain s).rd++(plain s).wr) (s.rd++s.wr) :=
  (Covers.of_mem (fun _ h =>List.mem_of_mem_take h)).append (Covers.refl _)

theorem fallback_run (W : Window) (M : Mont) (S : Selector) {s : State} (h : cdPre (plain s)) :
    ∃ trace t, Exec isa (VG.Impl.Ffdh.AArch64.Domain.CheckDomain.code W.code S.code M.mm) s trace t ∧
      abiPreserved s t ∧ cdPost s t := by
  obtain ⟨trace,t,run,abi,post⟩:=cd_correct W M S (plain s) h
  have wide:=VG.AArch64.Exec.widen run (rd:=s.rd) (wr:=s.wr) (plain_covers s) (Covers.refl _)
  refine ⟨trace,t.withRegions s.rd s.wr,?_,abi,post⟩
  simpa only [plain,stripConsts,State.withRegions_withRegions,State.withRegions_self] using wide

theorem fallback_ct (W : Window) (M : Mont) (S : Selector) :
    RelCT isa (fun s t =>cdPre (plain s) ∧ cdPre (plain t) ∧ cdPub s t)
      (VG.Impl.Ffdh.AArch64.Domain.CheckDomain.code W.code S.code M.mm) (fun _ _ =>True) := by
  intro s t ts tt u v ⟨hs,ht,hp⟩ es et
  obtain ⟨ts',u',eu,au,pu⟩:=cd_correct W M S (plain s) hs
  obtain ⟨tt',v',ev,av,pv⟩:=cd_correct W M S (plain t) ht
  have eus:=VG.AArch64.Exec.widen eu (rd:=s.rd) (wr:=s.wr) (plain_covers s) (Covers.refl _)
  have evt:=VG.AArch64.Exec.widen ev (rd:=t.rd) (wr:=t.wr) (plain_covers t) (Covers.refl _)
  have eus' : Exec isa (VG.Impl.Ffdh.AArch64.Domain.CheckDomain.code W.code S.code M.mm)
      s ts' (u'.withRegions s.rd s.wr) := by
    simpa only [plain,stripConsts,State.withRegions_withRegions,State.withRegions_self] using eus
  have evt' : Exec isa (VG.Impl.Ffdh.AArch64.Domain.CheckDomain.code W.code S.code M.mm)
      t tt' (v'.withRegions t.rd t.wr) := by
    simpa only [plain,stripConsts,State.withRegions_withRegions,State.withRegions_self] using evt
  have sameS:ts=ts':=(Exec.det es eus').1
  have sameT:tt=tt':=(Exec.det et evt').1
  refine ⟨?_,True.intro⟩
  rw [sameS,sameT]
  exact cd_constantTime W M S _ _ _ _ _ _ hs ht hp eu ev

end VG.Proof.Ffdh.AArch64.VettedValidation
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/VettedValidation/Facts.lean`, which only this module imported.
section

/-! The AArch64 cap sentinel is non-default only for an algebraically valid domain. -/
section
namespace VG.Proof.Ffdh.AArch64.VettedValidation
open VG
open VG.Impl.Ffdh.AArch64.Cached

theorem policyWidth_valid {gs : List Policy.Group} (members : ∀ g∈gs,g∈Policy.groups)
    {k : Nat} {dom : List Byte} (shape : dom.length=2*k ∨ dom.length=3*k)
    (hit : VG.Proof.Ffdh.AArch64.Cached.policyWidth 4095 k dom gs≠4095) : Spec.Ffdh.domainValid k dom=true := by
  induction gs with
  | nil => exact False.elim (hit rfl)
  | cons g gs ih =>
    unfold VG.Proof.Ffdh.AArch64.Cached.policyWidth at hit
    by_cases same : k=g.len ∧ dom=g.domain.take dom.length
    · exact VG.Proof.Ffdh.VettedValidation.matched_domain_valid (members g (by simp)) shape same
    · rw [ite_eq_right same] at hit
      exact ih (fun a h =>members a (by simp [h])) hit

end VG.Proof.Ffdh.AArch64.VettedValidation
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.VettedValidation
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero)

private theorem abi_trans {s t u : State} (a : abiPreserved s t) (b : abiPreserved t u) : abiPreserved s u :=
  ⟨fun r hr =>(b.1 r hr).trans (a.1 r hr),b.2.1.trans a.2.1,
    fun r hr =>(b.2.2 r hr).trans (a.2.2 r hr)⟩

theorem result_eval {s t : State} (h : Result s t) :
    isa.eval (.nonzero .x .x10) t=some (decide (width s≠4095)) := by
  rw [eval_nonzero,h.test]
  change some (!(BitVec.ofNat 64 (width s)-BitVec.ofNat 64 4095==0#64))=_
  rw [Cached.sub_zero_iff (by have :=width_le s;omega_using [this]) (by decide)]
  simp

theorem correct (W : Window) (M : Mont) (S : Selector) {s : State} (hs : pre s) :
    WP isa (VG.Impl.Ffdh.AArch64.VettedValidation.code W.code S.code M.mm) s
      (fun t =>abiPreserved s t ∧ CheckDomain.cdPost s t) := by
  have g:=geometry hs
  unfold VG.Impl.Ffdh.AArch64.VettedValidation.code
  rw [WP.seq_iff]
  refine WP.mono (recognize_ok g) ?_
  intro t h
  by_cases hit : width s≠4095
  · refine WP.ite true (by rw [result_eval h,decide_eq_true hit]) (fun _ =>?_) (fun bad =>Bool.noConfusion bad)
    have valid : Spec.Ffdh.domainValid (s.gpr .x2).toNat (CheckDomain.cdDom s)=true :=
      VG.Proof.Ffdh.AArch64.VettedValidation.policyWidth_valid (fun _ hg =>hg)
        (by simpa only [CheckDomain.cdDom,Spec.Rsa.bytesAt,List.length_map,List.length_range] using g.shape) hit
    refine WP.mono (WP.keep [.x0] (Q:=fun u =>u.gpr .x0=1#64) ?_ rfl rfl rfl) ?_
    · brun []
    · rintro u ⟨value,rest⟩
      have keep :=(h.keep.trans rest).mono (rs':=clobbers) (by
        intro r hr
        rcases List.mem_append.mp hr with hr|hr
        · exact hr
        · have eq : r= .x0 := by simpa using hr
          subst r
          decide)
      refine ⟨⟨fun r hr =>keep.gpr r (by revert r;decide),keep.sp,keep.vcs⟩,?_⟩
      unfold CheckDomain.cdPost
      rw [value,valid]
      rfl
  · refine WP.ite false (by rw [result_eval h,decide_eq_false hit]) (fun bad =>Bool.noConfusion bad) (fun _ =>?_)
    rw [WP.seq_iff]
    refine WP.mono (restore_ok g h) ?_
    intro u hu
    obtain ⟨trace,v,run,preserved,post⟩:=fallback_run W M S (hu.pre hs)
    refine ⟨trace,v,run,abi_trans hu.abi preserved,?_⟩
    unfold CheckDomain.cdPost at post ⊢
    rw [hu.args.2.2.1,hu.domain] at post
    exact post

end VG.Proof.Ffdh.AArch64.VettedValidation

end

end

/-! The fast acceptance and general fallback both depend only on the public domain. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.VettedValidation
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive
open Cached

def Recognized (q : Public) (t : State) : Prop := ∃s,Ready q s ∧ Result s t

def RestoredReady (q : Public) (t : State) : Prop := ∃s,Ready q s ∧ Restored s t

theorem ready_width {q : Public} {s : State} (h : Ready q s) :
    width s=policyWidth 4095 q.k.toNat q.dom Policy.groups := by
  unfold width
  rw [h.keyLength,h.bytes]

theorem recognized_eval {q : Public} {t : State} (h : Recognized q t) :
    isa.eval (.nonzero .x .x10) t=some (decide (policyWidth 4095 q.k.toNat q.dom Policy.groups≠4095)) := by
  obtain ⟨s,ready,result⟩:=h
  rw [result_eval result,ready_width ready]

theorem restore_ct : RelCT isa (Two Recognized)
    (.block VG.Impl.Ffdh.AArch64.VettedValidation.restore) (fun _ _ =>True) :=
  two_taint [.x0] (fun _ _ _ hs ht r hr =>by
    have same : r= .x0 := by simpa using hr
    subst r
    obtain ⟨s,hs,resultS⟩:=hs
    obtain ⟨t,ht,resultT⟩:=ht
    exact (resultS.base.trans hs.base).trans (resultT.base.trans ht.base).symm) (by taint_decide)

theorem restored_pub {q : Public} {s t : State} (hs : RestoredReady q s) (ht : RestoredReady q t)
    (sp : s.sp=t.sp) : CheckDomain.cdPub s t := by
  obtain ⟨a,ha,sa⟩:=hs
  obtain ⟨b,hb,tb⟩:=ht
  refine ⟨sp,?_,?_,?_,?_,?_,?_⟩
  · rw [sa.domain,ha.bytes,tb.domain,hb.bytes]
  · exact (sa.args.1.trans ha.domain).trans (tb.args.1.trans hb.domain).symm
  · exact (sa.args.2.1.trans ha.length).trans (tb.args.2.1.trans hb.length).symm
  · exact (sa.args.2.2.1.trans ha.keyLength).trans (tb.args.2.2.1.trans hb.keyLength).symm
  · exact (sa.args.2.2.2.1.trans ha.base).trans (tb.args.2.2.2.1.trans hb.base).symm
  · exact (sa.args.2.2.2.2.trans ha.words).trans (tb.args.2.2.2.2.trans hb.words).symm

theorem miss_ct (W : Window) (M : Mont) (S : Selector) : RelCT isa (Two Recognized)
    (.seq (.block VG.Impl.Ffdh.AArch64.VettedValidation.restore)
      (VG.Impl.Ffdh.AArch64.Domain.CheckDomain.code W.code S.code M.mm)) (fun _ _ =>True) := by
  refine RelCT.seq (two_post (Ψ:=RestoredReady) restore_ct ?_) ?_
  · intro q s h
    obtain ⟨original,ready,result⟩:=h
    exact WP.mono (restore_ok (geometry ready.assumptions) result) (fun _ restored =>⟨original,ready,restored⟩)
  · exact (fallback_ct W M S).mono (fun s t ⟨q,hs,ht,sp⟩ =>
      ⟨hs.choose_spec.2.pre hs.choose_spec.1.assumptions,
       ht.choose_spec.2.pre ht.choose_spec.1.assumptions,restored_pub hs ht sp⟩) (fun _ _ h =>h)

theorem native_ct (W : Window) (M : Mont) (S : Selector) : RelCT isa (Two Ready)
    (VG.Impl.Ffdh.AArch64.VettedValidation.code W.code S.code M.mm) (fun _ _ =>True) := by
  unfold VG.Impl.Ffdh.AArch64.VettedValidation.code
  refine RelCT.seq (two_post (Ψ:=Recognized) recognize_ct (fun q s h =>
    WP.mono (recognize_ok (geometry h.assumptions)) (fun _ result =>⟨s,h,result⟩))) ?_
  refine RelCT.ite (fun s t ⟨q,hs,ht,_⟩ =>(recognized_eval hs).trans (recognized_eval ht).symm) ?_ ?_
  · exact (two_taint [] (fun _ _ _ _ _ r hr =>by simp at hr) (by taint_decide)).mono
      (fun _ _ h =>h.1) (fun _ _ h =>h)
  · exact (miss_ct W M S).mono (fun _ _ h =>h.1) (fun _ _ h =>h)

def publicInput (s : State) (g : Geometry s) : Public :=
  ⟨s.gpr .x0,s.gpr .x1,s.gpr .x2,s.gpr .x3,s.gpr .x4,s.syms Policy.tableSym,CheckDomain.cdDom s,
    g.small,g.large,g.room,
    by simpa only [CheckDomain.cdDom,Spec.Rsa.bytesAt,List.length_map,List.length_range] using g.shape,
    by simp only [CheckDomain.cdDom,Spec.Rsa.bytesAt,List.length_map,List.length_range]⟩

theorem constantTime (W : Window) (M : Mont) (S : Selector) :
    ConstantTime isa pre pub (VG.Impl.Ffdh.AArch64.VettedValidation.code W.code S.code M.mm) := by
  intro s t ts tt u v hs ht hp es et
  obtain ⟨⟨sp,bytes,r0,r1,r2,r3,r4⟩,symbol⟩:=hp
  have sameBytes : CheckDomain.cdDom s=CheckDomain.cdDom t := by
    have recover:=congrArg (List.map (BitVec.ofNat 8)) bytes
    simpa only [List.map_map,Function.comp_def,BitVec.ofNat_toNat,BitVec.setWidth_eq,List.map_id'] using recover
  let q:=publicInput s (geometry hs)
  have first : Ready q s :=⟨hs,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  have second : Ready q t :=⟨ht,r0.symm,r1.symm,r2.symm,r3.symm,r4.symm,sameBytes.symm,symbol.symm⟩
  exact ((native_ct W M S) _ _ _ _ _ _ ⟨q,first,second,sp⟩ es et).1

end VG.Proof.Ffdh.AArch64.VettedValidation

end

end

/-! Exact standard-group acceptance implements the existing checked-domain API. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.VettedValidation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive
open VG.Impl.Ffdh.AArch64.Cached

theorem implies : contract.Implies (Spec.Ffdh.checkDomainContract (abi.withConsts Policy.tableConsts)) where
  pre:=fun _ h =>shared_pre h
  post:=fun _ _ _ h =>shared_post h
  pub:=by
    rintro s t _ _ h
    obtain ⟨plain,symbols⟩:=pub_consts.mp h
    sig_pub [Spec.Ffdh.checkDomainContract,Spec.Ffdh.checkDomainSig,abi,argRegs] at plain
    obtain ⟨sp,dom,r0,r1,r2,r3,r4⟩:=plain
    exact ⟨⟨sp,dom,r0,r1,r2,r3,r4⟩,symbols _ List.mem_cons_self⟩
  sat:=shared_sat

theorem verified (W : Window) (M : Mont) (S : Selector) :
    Verified target (VG.Impl.Ffdh.AArch64.VettedValidation.code W.code S.code M.mm)
      (Spec.Ffdh.checkDomainContract (abi.withConsts Policy.tableConsts)) := by
  refine Verified.of_correct (k:=contract) ?_ (constantTime W M S) implies
  intro s h
  obtain ⟨trace,t,run,preserved,post⟩:=correct W M S h
  exact ⟨trace,t,run,preserved,post⟩

end VG.Proof.Ffdh.AArch64.VettedValidation
