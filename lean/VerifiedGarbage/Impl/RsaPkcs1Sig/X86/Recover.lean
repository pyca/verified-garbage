module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Verify

/-! # i686 precomputed signature recovery

The recovered digest is released through the checked RSA byte mask. A bad
precomputation cannot turn a secret-dependent RSA status into a branch.
-/

@[expose] public section
namespace VG.Impl.RsaPkcs1Sig.X86.Recover
open VG VG.X86
open Verify (frameBytes em1Offset em2Offset statusOffset stackAt incoming lea copyArgument localArgument ret0 test0)

def lenCheck : List Instr :=
  [.mov .eax (.mem (incoming 8)), .alu .cmp .eax (.mem (incoming 3))]

def zeroOut : Prog isa :=
  .seq (.block [.mov .esi (.mem (incoming 0)), .mov .ecx (.mem (incoming 1)), .mov .eax (.imm 0)])
    (.loop (.block VG.Impl.Bignum.X86.PublicFn.clearStep) .ne)

def pubArgs : List Instr :=
  localArgument em1Offset 0 ++ copyArgument 3 1 ++ copyArgument 11 2 ++ copyArgument 12 3 ++
    copyArgument 4 4 ++ copyArgument 5 5 ++ copyArgument 7 6 ++ copyArgument 3 7 ++
    copyArgument 9 8 ++ copyArgument 10 9

/-- The trailing digest starts at EM₁ + k - out_len. -/
def digestPtr : List Instr := lea .esi em1Offset ++
  [.alu .add .esi (.mem (incoming 3)), .alu .sub .esi (.mem (incoming 1))]

def encArgs : List Instr := lea .edi em2Offset ++
  [.mov .ecx (.mem (incoming 3)), .mov .edx (.mem (incoming 6)),
    .mov .ebp (.mem (incoming 1))] ++ digestPtr

def cmpArgs : List Instr := lea .esi em1Offset ++ lea .edi em2Offset ++
  [.mov .ecx (.mem (incoming 3))]

def releaseArgs : List Instr := Verify.result ++
  [.mov .ebx (.reg .eax), .mov .edx (.imm 0), .alu .sub .edx (.reg .eax),
    .mov .edi (.mem (incoming 0)), .mov .ecx (.mem (incoming 1))] ++ digestPtr

def release : Prog isa :=
  .seq (.block releaseArgs)
    (.seq VG.Impl.Rsa.X86.PrivChecked.releaseLoop (.block [.mov .eax (.reg .ebx)]))

def tail : Prog isa :=
  .seq (.block test0) (.ite .e zeroOut
    (.seq (.block cmpArgs) (.seq VG.Impl.RsaPkcs1Sig.X86.compare release)))

def afterPub : Prog isa :=
  .seq (.block [.store (stackAt statusOffset) .eax])
    (.seq (.block encArgs) (.seq encode tail))

def body (pubName : String) (pub : Prog isa) : Prog isa :=
  .seq (.block lenCheck) (.ite .ne zeroOut
    (.seq (.block pubArgs) (.seq (.call pubName pub) afterPub)))

def code (pubName : String) (pub : Prog isa) : Prog isa :=
  .frame (.push [.ebx, .ebp, .esi, .edi])
    (.seq (.frame (.alloc frameBytes) (body pubName pub) (.free frameBytes)) (.block Sign.restore)) (.pop .ebx 4)

end VG.Impl.RsaPkcs1Sig.X86.Recover
