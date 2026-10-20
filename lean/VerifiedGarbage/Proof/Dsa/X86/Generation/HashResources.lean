module
public import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Hash
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # Disjoint hash buffers and call-stack resources -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

structure HashResources {H : Hash} (K : HashOK H) (input output scratch : BitVec 32) (len : Nat)
    (s : State) : Prop where
  lenBound : len < 2 ^ 32
  sp : 48 ≤ (s.gpr .esp).toNat
  src : Covers [⟨input.setWidth 64, len⟩] (s.rd ++ s.wr)
  initWr : Covers [⟨(scratch + 512#32).setWidth 64, H.S⟩] s.wr
  updWr : Covers [⟨(scratch + 512#32).setWidth 64, H.S⟩, ⟨scratch.setWidth 64, K.Wb⟩] s.wr
  finWr : Covers [⟨(scratch + 512#32).setWidth 64, H.S⟩, ⟨output.setWidth 64, H.F⟩,
    ⟨scratch.setWidth 64, K.Wb⟩] s.wr
  stateScratch : Region.Disjoint ⟨(scratch + 512#32).setWidth 64, H.S⟩ ⟨scratch.setWidth 64, K.Wb⟩
  inputState : Region.Disjoint ⟨input.setWidth 64, len⟩ ⟨(scratch + 512#32).setWidth 64, H.S⟩
  inputScratch : Region.Disjoint ⟨input.setWidth 64, len⟩ ⟨scratch.setWidth 64, K.Wb⟩
  stateOutput : Region.Disjoint ⟨(scratch + 512#32).setWidth 64, H.S⟩ ⟨output.setWidth 64, H.F⟩
  outputScratch : Region.Disjoint ⟨output.setWidth 64, H.F⟩ ⟨scratch.setWidth 64, K.Wb⟩
  stackState : (stk s).Disjoint ⟨(scratch + 512#32).setWidth 64, H.S⟩
  stackInput : (stk s).Disjoint ⟨input.setWidth 64, len⟩
  stackOutput : (stk s).Disjoint ⟨output.setWidth 64, H.F⟩
  stackScratch : (stk s).Disjoint ⟨scratch.setWidth 64, K.Wb⟩
  stateBound : (scratch + 512#32).toNat + H.S ≤ 2 ^ 32
  inputBound : input.toNat + len ≤ 2 ^ 32
  outputBound : output.toNat + H.F ≤ 2 ^ 32
  scratchBound : scratch.toNat + K.Wb ≤ 2 ^ 32

theorem HashResources.congr {H : Hash} {K : HashOK H} {input output scratch : BitVec 32} {len : Nat}
    {s t : State} (R : HashResources K input output scratch len s)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) (esp : t.gpr .esp = s.gpr .esp) :
    HashResources K input output scratch len t := by
  rcases R with ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,u⟩
  exact ⟨a, by rw [esp]; exact b, by rw [rd, wr]; exact c, by rw [wr]; exact d,
    by rw [wr]; exact e, by rw [wr]; exact f, g,h,i,j,k,
    by simpa only [stk, esp] using l, by simpa only [stk, esp] using m,
    by simpa only [stk, esp] using n, by simpa only [stk, esp] using o,p,q,r,u⟩

theorem HashResources.after {H : Hash} {K : HashOK H} {input output scratch : BitVec 32} {len : Nat}
    {s t : State} {rs : List Region} (R : HashResources K input output scratch len s) (A : After s rs t) :
    HashResources K input output scratch len t := R.congr A.rd A.wr A.esp

theorem HashResources.keeps {H : Hash} {K : HashOK H} {input output scratch : BitVec 32} {len : Nat}
    {s t : State} {regs : List Reg} (R : HashResources K input output scratch len s)
    (A : Keeps regs s t) (sp : Reg.esp ∉ regs) : HashResources K input output scratch len t :=
  R.congr A.2.1 A.2.2 (A.1 _ sp)

theorem HashResources.init {H : Hash} {K : HashOK H} {input output scratch : BitVec 32} {len : Nat}
    {s : State} (R : HashResources K input output scratch len s)
    (st : s.gpr .ebx = scratch + 512#32) : InitArgs (H := H) s .ebx (scratch + 512#32) :=
  ⟨st, by decide, R.sp, R.initWr, R.stackState, R.stateBound⟩

theorem HashResources.update {H : Hash} {K : HashOK H} {input output scratch : BitVec 32} {len : Nat}
    {s : State} (R : HashResources K input output scratch len s)
    (st : s.gpr .ebx = scratch + 512#32) (ax : s.gpr .eax = 0)
    (cx : s.gpr .ecx = BitVec.ofNat 32 len) (dx : s.gpr .edx = input) (bp : s.gpr .ebp = scratch) :
    UpdArgs K s .eax .ebx (scratch + 512#32) input scratch 0 len :=
  ⟨st, ax, ax, cx, dx, bp, by decide, by decide, R.lenBound, R.sp, R.src, R.updWr,
    R.stateScratch, R.inputState, R.inputScratch, R.stackState, R.stackInput, R.stackScratch,
    R.stateBound, R.inputBound, R.scratchBound⟩

theorem HashResources.finalize {H : Hash} {K : HashOK H} {input output scratch : BitVec 32} {len : Nat}
    {s : State} (R : HashResources K input output scratch len s)
    (st : s.gpr .ebx = scratch + 512#32) (ax : s.gpr .eax = BitVec.ofNat 32 len)
    (cx : s.gpr .ecx = 0) (dx : s.gpr .edx = output) (bp : s.gpr .ebp = scratch) :
    FinArgs K s .ebx (scratch + 512#32) output scratch (BitVec.ofNat 32 len) 0 :=
  ⟨st, ax, cx, dx, bp, by decide, R.sp, R.finWr, R.stateOutput, R.stateScratch, R.outputScratch,
    R.stackState, R.stackOutput, R.stackScratch, R.stateBound, R.outputBound, R.scratchBound⟩
end VG.Proof.Dsa.X86.Generation
