module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Encode
public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Sign

/-! # Precomputed RSAES-PKCS1-v1_5 encryption on i686

A private frame holds the encoded message, the padding validity bit, and
all ten arguments to checked precomputed RSA. The output and status are
masked by padding validity; the encoded message is then erased.
-/

@[expose] public section
namespace VG.Impl.RsaPkcs1Enc.X86.Encrypt
open VG VG.X86

def frameBytes : Nat := 1088
def emOffset : Nat := 64
def zeroOffset : Nat := 40

def stackAt (d : Nat) : MemOp := ⟨.esp, d⟩
def incoming (i : Nat) : MemOp := stackAt (frameBytes + 20 + 4 * i)
def lea (r : Reg) (d : Nat) : List Instr :=
  [.mov r (.reg .esp), .alu .add r (.imm (BitVec.ofNat 32 d))]
def copyArgument (i j : Nat) : List Instr :=
  [.mov .eax (.mem (incoming i)), .store (stackAt (4 * j)) .eax]
def localArgument (d j : Nat) : List Instr := lea .eax d ++ [.store (stackAt (4 * j)) .eax]

def start : List Instr := lea .edi emOffset ++
  [.mov .esi (.mem (incoming 8)), .mov .ebp (.mem (incoming 9))]

def messageArgs : List Instr := separator ++
  [.mov .esi (.mem (incoming 6)), .mov .ebp (.mem (incoming 7))]

def callArgs : List Instr := [.store (stackAt zeroOffset) .ebx] ++ copyArgument 0 0 ++ copyArgument 3 1 ++
  copyArgument 12 2 ++ copyArgument 13 3 ++ copyArgument 4 4 ++ copyArgument 5 5 ++
  localArgument emOffset 6 ++ copyArgument 3 7 ++ copyArgument 10 8 ++ copyArgument 11 9

def maskArgs : List Instr :=
  [.mov .edx (.mem (stackAt zeroOffset)), .alu .sub .edx (.imm 1),
    .alu .and .eax (.reg .edx), .alu .and .eax (.imm 1), .mov .ebx (.reg .eax),
    .mov .esi (.mem (incoming 0)), .mov .ecx (.mem (incoming 3))]

def wipeArgs : List Instr := lea .esi emOffset ++ [.mov .ecx (.mem (incoming 3)), .mov .eax (.imm 0)]

def wipe : Prog isa :=
  .seq (.block wipeArgs)
    (.seq (.loop (.block VG.Impl.Bignum.X86.PublicFn.clearStep) .ne) (.block [.mov .eax (.reg .ebx)]))

def afterPub : Prog isa :=
  .seq (.block maskArgs) (.seq maskLoop wipe)

def encoding : Prog isa :=
  .seq (.block head) (.seq psLoop (.seq (.block messageArgs) message))

def body (pubName : String) (pub : Prog isa) : Prog isa :=
  .seq (.block start) (.seq encoding (.seq (.block callArgs) (.seq (.call pubName pub) afterPub)))

def code (pubName : String) (pub : Prog isa) : Prog isa :=
  .frame (.push [.ebx, .ebp, .esi, .edi])
    (.seq (.frame (.alloc frameBytes) (body pubName pub) (.free frameBytes))
      (.block VG.Impl.RsaPkcs1Sig.X86.Sign.restore)) (.pop .ebx 4)

end VG.Impl.RsaPkcs1Enc.X86.Encrypt
