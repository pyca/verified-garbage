module

public import VerifiedGarbage.Impl.AesGcm.X86_64.Fast
public import VerifiedGarbage.Impl.AesGcm.X86_64.SealGather
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Impl.Gcm.X86_64.Flag

/-! Direct encryption of one or two fragments when at most one block follows
the whole blocks of the first fragment. Each byte is encrypted directly from
its source into the destination. -/
@[expose] public section
namespace VG.Impl.AesGcm.X86_64.DirectGather
open VG.X86_64

abbrev load (r : Reg) (o : Nat) : Instr := .mov r (.mem (at_ .r15 o))
abbrev store (r : Reg) (o : Nat) : Instr := .store (at_ .r15 o) r
def setupG : List Instr :=
  [.mov .rax (.mem (at_ .rsp 8)),store .rax rO,.mov .rax (.mem (at_ .rsp 16)),store .rax tlO,
   .mov .rax (.mem (at_ .rsp 24)),store .rax dataO,.mov .rax (.mem (at_ .rsp 32)),store .rax tlenO,store .rax lenO,
   .mov32 .rax (imm 0),store .rax vO,store .rax 264,load .rax tlO,.alu .test .rax (.reg .rax)]
def bulkTest : List Instr :=
  [load .r10 rO,.mov .rax (.mem (at_ .r10 8)),.shift .shr .rax 8,.alu .test .rax (.reg .rax)]
def bulkWrites : List Instr :=
  [.shift .shl .rax 8,store .rax 264,.mov .r8 (.mem (at_ .r10 0)),
   load .r11 dataO,.alu .add .rax (.reg .r11),store .rax dataO,load .rax lenO,
   .alu .sub .rax (.mem (at_ .r15 264)),store .rax lenO]
def bulkRegs : List Instr :=
  [load .r9 264,.shift .shr .r9 4,
   .mov .r10 (.reg .r9),.mov .rdi (.reg .r13),load .rsi roundsO] ++
   ptr .rdx .r14 48 ++ ptr .rcx .r14 16 ++ ptr .rax .r15 bScrO
def bulkArgs : List Instr := bulkWrites ++ bulkRegs
/-- Call the shared seal kernel with the destination in r10 and scratch on the stack. -/
def callSeal (fn : Fn) : Prog isa :=
  .seq (.block [.mov .r10 (.reg .r11)])
    (.frame (.push [.rax]) (.call fn.name fn.code) (.pop .rax 1))

/-- The largest multiple of 256 bytes in the first slice, encrypted and authenticated in one pass. -/
def bulk (toFn : Fn) : Prog isa :=
  .seq (.block bulkTest) (.ite .e (.block []) (.seq (.block bulkArgs)
    (callSeal toFn)))
/-- Advance to the next descriptor, skipping any prefix already consumed by the fused loop. -/
def loadPiece : List Instr :=
  [load .r10 rO,.mov .rbx (.mem (at_ .r10 0)),.mov .rbp (.mem (at_ .r10 8)),.alu .add .r10 (imm 16),store .r10 rO,
   load .rax 264,.alu .add .rbx (.reg .rax),.alu .sub .rbp (.reg .rax),.mov32 .rax (imm 0),store .rax 264,
   load .rax vO,load .r12 dataO,.alu .add .r12 (.reg .rax),.mov .rsi (.reg .rax),.alu .and .rsi (imm 15),
   .alu .add .rax (.reg .rbp),store .rax vO,.alu .test .rbp (.reg .rbp)]
/-- Finish any partial counter block using saved keystream. -/
def suffix : Prog isa :=
  .seq (.block [.alu .test .rsi (.reg .rsi)]) (.ite .e (.block [])
    (.seq (.block [.mov32 .rcx (imm 16),.alu .sub .rcx (.reg .rsi),.alu .cmp .rbp (.reg .rcx),.cmov .b .rcx (.reg .rbp),
       .alu .add .rsi (.reg .r14),.alu .add .rsi (imm 64),.mov .rdi (.reg .r12)])
      (.seq (xorLoopG true) (.block [.alu .add .rbx (.reg .rcx),.alu .add .r12 (.reg .rcx),.alu .sub .rbp (.reg .rcx)]))))
/-- Apply out-of-place CTR to all whole blocks in this fragment. -/
def whole (ctr : Fn) : Prog isa :=
  .seq (.block [.mov .r8 (.reg .rbp),.shift .shr .r8 4,.alu .test .r8 (.reg .r8)]) (.ite .e (.block [])
    (.seq (.block (([.mov .rcx (.reg .rbx),.mov .r11 (.reg .r12),.mov .rax (.reg .rbp),.alu .and .rbp (imm 15),
      .alu .sub .rax (.reg .rbp),.alu .add .rbx (.reg .rax),.alu .add .r12 (.reg .rax),
      .mov .rdi (.reg .r13),load .rsi roundsO] : List Instr) ++ ptr .rdx .r14 48 ++ ptr .r9 .r15 scrO)) (.call ctr.name ctr.code)))
def pieces (c : Callees) (ctr : Fn) (toFn : Option Fn) : Prog isa :=
  .seq (.block setupG) (.ite .e (.block []) (.seq (toFn.map bulk |>.getD (.block []))
    (.loop (.seq (.block loadPiece) (.seq (.ite .e (.block []) (.seq suffix (.seq (whole ctr)
       (cryptTailG c true)))) (.block [load .r10 tlO,.alu .sub .r10 (imm 1),store .r10 tlO]))) .ne)))
/-- Read the first descriptor and save the destination and total authenticated length. -/
def firstArgs : List Instr :=
  [.mov .r10 (.mem (at_ .rsp 8)), .mov .r8 (.mem (at_ .r10 0)), .mov .rax (.mem (at_ .r10 8)),
   .mov .r9 (.mem (at_ .rsp 24)), .mov .r11 (.mem (at_ .rsp 32)),
   store .r8 tlO, store .r9 dataO, store .r11 tlenO, .shift .shr .rax 4, .alu .test .rax (.reg .rax)]

/-- Encrypt and authenticate all whole blocks of the first fragment into the output. -/
def firstBlocks (toFn : Fn) : Prog isa :=
  .seq (.block firstArgs)
    (.ite .e (.block []) (.seq (.block SealSplit.preArgs)
      (callSeal toFn)))
/-- Finish the remaining bytes from the independent input, writing ciphertext to both destinations. -/
def tailByte : List Instr :=
  [.movzx8 .rax {base:=.rbx,index:=some .r10},.movzx8 .r9 Short.kB,
    .alu .xor .rax (.reg .r9),.store8 {base:=.rsi,index:=some .r10} .rax,.store8 {base:=.rdi,index:=some .r10} .rax,.alu .add .r10 (imm 1),
    .alu .cmp .r10 (.reg .rcx)]

def tailBytes : Prog isa := .loop (.block tailByte) .ne

/-- XOR an eight- or four-byte span from the same source as the byte loop. -/
def word (wide : Bool) : List Instr :=
  let src : MemOp := {base:=.rbx,index:=some .r10}
  let dst : MemOp := {base:=.rsi,index:=some .r10}
  let auth : MemOp := {base:=.rdi,index:=some .r10}
  if wide then [.mov .rax (.mem src),.alu .xor .rax (.mem Short.kB),.store dst .rax,.store auth .rax,.alu .add .r10 (imm 8)]
  else [.mov32 .rax (.mem src),.alu32 .xor .rax (.mem Short.kB),.store32 dst .rax,.store32 auth .rax,.alu .add .r10 (imm 4)]
def tailXor : Prog isa :=
  .seq (.block [.mov .r8 (.reg .rcx),.alu .sub .r8 (.reg .r10),.alu .cmp .r8 (imm 4)])
    (.ite .b tailBytes
      (.seq (.block [.alu .cmp .r8 (imm 8)])
        (.seq (.ite .b (.block []) (.block (word true)))
        (.seq (.block [.mov .r8 (.reg .rcx),.alu .sub .r8 (.reg .r10),.alu .cmp .r8 (imm 4)])
        (.seq (.ite .b (.block []) (.block (word false)))
        (.seq (.block [.alu .cmp .rcx (.reg .r10)]) (.ite .e (.block []) tailBytes)))))))
/-- Complete up to two fragment tails in a single padded GHASH block. -/
def tailArgs : List Instr :=
  [.mov .r11 (.mem (at_ .rsp 8)),.mov .rbx (.mem (at_ .r11 0)),.mov .rcx (.mem (at_ .r11 8)),
    .mov .r8 (.reg .rcx),.alu .and .rcx (imm 15),.alu .sub .r8 (.reg .rcx),.alu .add .rbx (.reg .r8),
    load .rsi dataO,.alu .add .rsi (.reg .r8),load .rbp tlenO,.alu .sub .rbp (.reg .r8),
    .alu .test .rbp (.reg .rbp)]

def tailStart : List Instr :=
  ([.xop (.bin .pxor .xmm7 .xmm7),.movdquStore (at_ .r15 Short.gO) .xmm7] : List Instr) ++
    (ptr .rdi .r15 Short.gO ++ ptr .rdx .r15 (Short.kO+16) ++
      [.mov32 .r10 (imm 0),.alu .test .rcx (.reg .rcx)])

def secondArgs : List Instr :=
  [.mov .rbx (.mem (at_ .r11 16)),.alu .sub .rbx (.reg .r10),.mov .rcx (.reg .rbp)]

def tails : Prog isa :=
  .seq (.ite .e (.block []) tailXor)
    (.seq (.block [.alu .cmp .r10 (.reg .rbp)])
      (.ite .e (.block []) (.seq (.block secondArgs) tailXor)))

def twoTail : Prog isa :=
  .seq (.block tailArgs)
    (.ite .e (.block (Short.finLens ++ Short.finGh1 ++ Short.tagK 0))
      (.seq (.block tailStart) (.seq tails (.block (Short.finLens ++ Short.finGh2 ++ Short.tagK 0)))))
def quick (toFn : Fn) : Prog isa :=
  .seq Fast.aad (.seq (firstBlocks toFn) (.seq (.block Short.finPowP) (.seq Short.finKsA twoTail)))

/-- Gather arbitrary fragments directly, carrying the streaming counter and
authenticating the output as a single message. -/
def general (c : Callees) (ctr : Fn) (toFn : Option Fn) : Prog isa :=
  .seq (oneAad c) (.seq (pieces c ctr toFn) (oneTag c 0))

def enter (p : Prog isa) : Prog isa := .seq (.block (oneEntry 48 24 32)) p

def framed (p : Prog isa) : Prog isa :=
  Impl.StackScratch.X86_64.withStackArgScratch 2616 5
    (.seq p (.block (tagOut (at_ .rsp 40) ++ restore)))

def plain (c : Callees) (ctr : Fn) : Prog isa := framed (enter (general c ctr none))

def dispatch (fast slow : Prog isa) : Prog isa :=
  .seq (SealGather.frontCore false) (.ite .e (enter fast) (enter slow))

def prepared (c : Callees) (ctr toFn : Fn) : Prog isa :=
  framed (dispatch (quick toFn) (general c ctr (some toFn)))

/-- Seal directly from the descriptors and wipe the gather frame. -/
def directBase (lv : Impl.Scrub.X86_64.VecLevel) (c : Callees) (ctr : Fn) : Prog isa :=
  Impl.Scrub.X86_64.scrubAll lv 0 5128 (plain c ctr)

/-- Select the direct path for the publicly advertised number of prepared powers. -/
def directPrepared (lv : Impl.Scrub.X86_64.VecLevel) (n : Nat) (c : Callees) (ctr blockTo : Fn) : Prog isa :=
  Impl.Scrub.X86_64.scrubAll lv 0 5128 (Impl.Gcm.X86_64.Flag.onFlag n (prepared c ctr blockTo) (plain c ctr))

end VG.Impl.AesGcm.X86_64.DirectGather
