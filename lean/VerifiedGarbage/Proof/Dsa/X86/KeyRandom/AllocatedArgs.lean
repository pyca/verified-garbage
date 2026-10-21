module

public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CallPre
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckPre
public import VerifiedGarbage.Proof.Dsa.X86.DerivingABI
public import VerifiedGarbage.Proof.Dsa.X86.CheckingABI
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Entry
import VerifiedGarbage.Proof.Framework.Offset

/-! An inlined cdecl body reserves the return-address slot without a call. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86

theorem allocated_arg {s₀ t : State} (h : Ready s₀ t) {i : Nat} (hi : i<11) (rd wr : List Region) :
    arg ((allocated 4 t).withRegions rd wr) i=slot t.mem (rBase s₀) (4*i) := by
  change t.mem.readW ((t.gpr .esp-4+BitVec.ofNat 32 (4+4*i)).setWidth 64) 32=_
  rw [show t.gpr .esp-4+BitVec.ofNat 32 (4+4*i)=t.gpr .esp+BitVec.ofNat 32 (4*i) by
    rw [BitVec.ofNat_add]
    bv_omega]
  rw [h.rf.ptr (by unfold argOff VG.Impl.Dsa.X86.KeyRandom.frameBytes; omega)]

theorem derivingABI_congr {s t : State} (A : DerivingABI s)
    (sp : t.gpr .esp=s.gpr .esp) (args : ∀ i<9, arg t i=arg s i)
    (rd : t.rd=s.rd) (wr : t.wr=s.wr) : DerivingABI t := by
  constructor
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.stackLow
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.stackBound
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.rd
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.wr
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.outScratch
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.keyOut
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.scalarOut
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.retOut
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.outBound
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.keyScratch
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.scalarScratch
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.scratchArgs
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.retScratch
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.belowScratch
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.belowKey
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.belowScalar
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.keyBound
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.scalarBound
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.scratchBound
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.lengths
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.keyLength
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.outLength
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),args 6 (by decide),args 7 (by decide),args 8 (by decide),rd,wr] using A.scratchLength

theorem checkingABI_congr {s t : State} (A : CheckingABI s)
    (sp : t.gpr .esp=s.gpr .esp) (args : ∀ i<6, arg t i=arg s i)
    (rd : t.rd=s.rd) (wr : t.wr=s.wr) : CheckingABI t := by
  constructor
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),rd,wr] using A.stackLow
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),rd,wr] using A.stackBound
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),rd,wr] using A.rd
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),rd,wr] using A.wr
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),rd,wr] using A.keyScratch
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),rd,wr] using A.scratchArgs
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),rd,wr] using A.retScratch
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),rd,wr] using A.belowScratch
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),rd,wr] using A.belowKey
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),rd,wr] using A.keyBound
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),rd,wr] using A.scratchBound
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),rd,wr] using A.lengths
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),rd,wr] using A.keyLength
  · simpa only [argumentPointer,argAddr,sp,args 0 (by decide),args 1 (by decide),args 2 (by decide),args 3 (by decide),args 4 (by decide),args 5 (by decide),rd,wr] using A.scratchLength

theorem allocated_derivingABI {s₀ t : State} (A : KeyABI s₀) (R : Ready s₀ t) (C : CallSlots s₀ t) :
    DerivingABI ((allocated 4 t).withRegions (callRd s₀) (callWr s₀)) := by
  apply derivingABI_congr (t := (allocated 4 t).withRegions (callRd s₀) (callWr s₀)) (derivingABI_of (call_pre A R C)) rfl ?_ rfl rfl
  intro i hi
  rw [allocated_arg R (by omega),ce_arg A R C _ _ hi]
  exact C i hi

theorem allocated_checkingABI {s₀ t : State} (A : KeyABI s₀) (R : Ready s₀ t) (C : CheckCall.CallSlots s₀ t) :
    CheckingABI ((allocated 4 t).withRegions (CheckCall.callRd s₀) (CheckCall.callWr s₀)) := by
  apply checkingABI_congr (t := (allocated 4 t).withRegions (CheckCall.callRd s₀) (CheckCall.callWr s₀)) (checkingABI_of (CheckCall.call_pre A R C)) rfl ?_ rfl rfl
  intro i hi
  rw [allocated_arg R (by omega),CheckCall.ce_arg A R C _ _ hi]
  exact C i hi

end VG.Proof.Dsa.X86.KeyRandom
