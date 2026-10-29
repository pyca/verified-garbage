module

public import VerifiedGarbage.Proof.Ffdh.AArch64.VettedValidation.Recognize
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyLoopTiming
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyTableFrame
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SourceSlices

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
    by have :=q.small;omega,by have :=q.large;omega⟩,
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
