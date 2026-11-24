module

public import VerifiedGarbage.Impl.AesGcm.X86
public import VerifiedGarbage.Impl.StackScratch.X86

/-! # IA-32 direct gather seal

The reserved word at esp supplies CTR32's seventh argument, as in open_to.
Only the destination pointer and piece lengths are passed through scratch.
-/

@[expose] public section

namespace VG.Impl.AesGcm.X86.DirectGather

open VG.X86

def descriptor : List Instr :=
  [.mov .edx (slot rO), .mov .eax (.mem (at_ .edx 0)), .store (at_ .ebp dataO) .eax,
   .mov .ecx (.mem (at_ .edx 4)), .store (at_ .ebp lenO) .ecx, .store (at_ .ebp nO) .ecx,
   .alu .add .edx (imm 8), .store (at_ .ebp rO) .edx]

def setCursors : List Instr :=
  [.mov .eax (slot xlO), .mov .edi (.reg .eax), .alu .add .edi (argOp 6), .store (at_ .esp 0) .edi,
   .alu .add .ecx (.reg .eax), .store (at_ .ebp xlO) .ecx,
   .alu .and .eax (imm 15), .store (at_ .ebp bO) .eax]

def nextPiece : List Instr := descriptor ++ setCursors

def headArgs : List Instr :=
  [.mov .edx (.reg .esi), .alu .add .edx (imm 64), .alu .add .edx (slot bO),
   .mov .esi (slot dataO), .mov .eax (slot lenO), .alu .sub .eax (.reg .ecx),
   .store (at_ .ebp lenO) .eax]

def headDone : List Instr :=
  [.store (at_ .ebp dataO) .esi, .store (at_ .esp 0) .edi,
   .mov .esi (.reg .ebp), .alu .add .esi (imm stO)]

/-- Consume up to the end of the saved keystream block. The two advanced
pointers and the remaining length are then in the layout of Open.decTo. -/
def partialHead : Prog isa :=
  .seq minLen (.seq (.block [.alu .test .ecx (.reg .ecx)]) (.ite .e (.block [])
    (.seq (.block headArgs) (.seq (xorLoopG true) (.block headDone)))))

def pieces (c : Callees) : Prog isa :=
  .seq (.block [.mov .ecx (slot tglO), .alu .test .ecx (.reg .ecx)]) (.ite .e (.block [])
    (.loop (.seq (.block nextPiece) (.seq (.ite .e (.block []) partialHead)
      (.seq (Open.decTo c c.ctr)
        (.block [.mov .ecx (slot tglO), .alu .sub .ecx (imm 1), .store (at_ .ebp tglO) .ecx])))) .ne))

/-- Present the one-shot argument order to the AAD and tag helpers. The
descriptor pointer and count follow the tag in private argument slots. -/
def sourceSlot (i : Nat) : Nat := if i < 6 then i else if i < 9 then i+2 else i-3

def copySlot (f i : Nat) : List Instr :=
  Impl.StackScratch.X86.copyArg (f + 4*sourceSlot i - 4*i) i

def zeroRet : List Instr := [.mov .eax (imm 0), .store (at_ .esp 0) .eax]

def frameArgs (f : Nat) : List Instr :=
  (List.range 11).flatMap (copySlot f) ++
    [.mov .eax (.reg .esp), .alu .add .eax (imm 52), .store (at_ .esp 48) .eax] ++ zeroRet

def loopSetup : List Instr :=
  keep 9 rO ++ keep 10 tglO ++ [.mov .eax (imm 0), .store (at_ .ebp xlO) .eax]

def tagSetup : List Instr := keep 6 dataO ++ keep 7 lenO ++ zeroRet

def body (c : Callees) : Prog isa :=
  .seq (oneEntry 11 (keep 8 tpO))
    (.seq (oneAad c) (.seq (.block loopSetup)
      (.seq (pieces c) (.seq (.block tagSetup)
        (.seq (oneTag c 0) (.seq (tagOut 0) (.block restore)))))))

/-- With a working space of `n` bytes, after the 52 of the frame's own slots. -/
def sealGather (c : Callees) (n : Nat) : Prog isa :=
  .frame (.alloc (n + 52)) (.seq (.block (frameArgs (n + 52))) (body c)) (.free (n + 52))

end VG.Impl.AesGcm.X86.DirectGather
