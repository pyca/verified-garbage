module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Encode
public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Sign

/-! # i686 verification with a precomputed public key

The public operation and the encoder use separate private buffers. Its
status is saved and masks the final comparison without a branch, including
when a caller supplies an inconsistent precomputed key.
-/

@[expose] public section
namespace VG.Impl.RsaPkcs1Sig.X86.Verify
open VG VG.X86

def frameBytes : Nat := 2112
def em1Offset : Nat := 64
def em2Offset : Nat := 1088
def statusOffset : Nat := 40

def stackAt (d : Nat) : MemOp := ⟨.esp, d⟩
def incoming (i : Nat) : MemOp := stackAt (frameBytes + 20 + 4 * i)
def lea (r : Reg) (d : Nat) : List Instr :=
  [.mov r (.reg .esp), .alu .add r (.imm (BitVec.ofNat 32 d))]
def copyArgument (i j : Nat) : List Instr :=
  [.mov .eax (.mem (incoming i)), .store (stackAt (4 * j)) .eax]
def localArgument (d j : Nat) : List Instr := lea .eax d ++ [.store (stackAt (4 * j)) .eax]

def ret0 : Prog isa := .block [.mov .eax (.imm 0)]
def test0 : List Instr := [.alu .cmp .eax (.imm 0)]
def lenCheck : List Instr :=
  [.mov .eax (.mem (incoming 8)), .alu .cmp .eax (.mem (incoming 1))]

def pubArgs : List Instr :=
  localArgument em1Offset 0 ++ copyArgument 1 1 ++ copyArgument 11 2 ++ copyArgument 12 3 ++
    copyArgument 2 4 ++ copyArgument 3 5 ++ copyArgument 7 6 ++ copyArgument 1 7 ++
    copyArgument 9 8 ++ copyArgument 10 9

def encArgs : List Instr := lea .edi em2Offset ++
  [.mov .ecx (.mem (incoming 1)), .mov .edx (.mem (incoming 4)),
    .mov .esi (.mem (incoming 5)), .mov .ebp (.mem (incoming 6))]

def cmpArgs : List Instr := lea .esi em1Offset ++ lea .edi em2Offset ++
  [.mov .ecx (.mem (incoming 1))]

def result : List Instr :=
  VG.Impl.Rsa.X86.PrivChecked.zeroTest ++
  [.mov .ecx (.mem (stackAt statusOffset)), .alu .and .eax (.reg .ecx)]

def tail : Prog isa :=
  .seq (.block test0) (.ite .e ret0
    (.seq (.block cmpArgs) (.seq VG.Impl.RsaPkcs1Sig.X86.compare (.block result))))

def afterPub : Prog isa :=
  .seq (.block [.store (stackAt statusOffset) .eax])
    (.seq (.block encArgs) (.seq encode tail))

def body (pubName : String) (pub : Prog isa) : Prog isa :=
  .seq (.block lenCheck) (.ite .ne ret0
    (.seq (.block pubArgs) (.seq (.call pubName pub) afterPub)))

def code (pubName : String) (pub : Prog isa) : Prog isa :=
  .frame (.push [.ebx, .ebp, .esi, .edi])
    (.seq (.frame (.alloc frameBytes) (body pubName pub) (.free frameBytes)) (.block Sign.restore)) (.pop .ebx 4)

end VG.Impl.RsaPkcs1Sig.X86.Verify
