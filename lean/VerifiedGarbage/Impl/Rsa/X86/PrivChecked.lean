module

public import VerifiedGarbage.TCB.X86.Isa

/-! # Private RSA with public re-exponentiation before releasing the result

A fixed stack frame holds the private candidate and public precomputation.
All three calls run regardless of private acceptance. The final loop releases
only a checked candidate, and clears the candidate buffer as it proceeds.
-/

@[expose] public section
namespace VG.Impl.Rsa.X86.PrivChecked
open VG VG.X86

def frameBytes : Nat := 3328
def candidateOffset : Nat := 128
def precomputeOffset : Nat := 1152
def crtStatusOffset : Nat := 80
def precomputeStatusOffset : Nat := 84

def stackAt (d : Nat) : MemOp := ⟨.esp, d⟩
def incoming (i : Nat) : MemOp := stackAt (frameBytes + 20 + 4 * i)

def copyArgument (i j : Nat) : List Instr :=
  [.mov .eax (.mem (incoming i)), .store (stackAt (4 * j)) .eax]

def localArgument (d j : Nat) : List Instr :=
  [.mov .eax (.reg .esp), .alu .add .eax (.imm (BitVec.ofNat 32 d)), .store (stackAt (4 * j)) .eax]

def precomputeLength (j : Nat) : List Instr :=
  [.mov .eax (.mem (incoming 3)), .alu .add .eax (.imm 7), .shift .shr .eax 3,
    .alu .add .eax (.reg .eax), .store (stackAt (4 * j)) .eax]

def crtArgs : List Instr := localArgument candidateOffset 0 ++
  (List.range 17).flatMap (fun j => copyArgument (if j + 1 < 4 then j + 1 else j + 3) (j + 1))

def precomputeArgs : List Instr := [.store (stackAt crtStatusOffset) .eax] ++
  localArgument precomputeOffset 0 ++ precomputeLength 1 ++ copyArgument 2 2 ++ copyArgument 3 3 ++
  copyArgument 18 4 ++ copyArgument 19 5

def publicArgs : List Instr := [.store (stackAt precomputeStatusOffset) .eax] ++
  copyArgument 0 0 ++ copyArgument 1 1 ++ localArgument precomputeOffset 2 ++ precomputeLength 3 ++
  copyArgument 4 4 ++ copyArgument 5 5 ++ localArgument candidateOffset 6 ++ copyArgument 7 7 ++
  copyArgument 18 8 ++ copyArgument 19 9

def compareArgs : List Instr :=
  [.alu .and .eax (.mem (stackAt crtStatusOffset)), .alu .and .eax (.mem (stackAt precomputeStatusOffset)),
    .alu .and .eax (.imm 1), .mov .ebx (.reg .eax),
    .mov .esi (.mem (incoming 0)), .mov .edi (.mem (incoming 6)),
    .mov .ecx (.mem (incoming 3)), .mov .ebp (.imm 0)]

def compareStep : List Instr :=
  [.movzx8 .eax ⟨.esi, 0⟩, .movzx8 .edx ⟨.edi, 0⟩, .alu .xor .eax (.reg .edx),
    .alu .or .ebp (.reg .eax), .alu .add .esi (.imm 1), .alu .add .edi (.imm 1),
    .alu .sub .ecx (.imm 1), .alu .cmp .ecx (.imm 0)]

def compareBytes : Prog isa := .loop (.block compareStep) .ne

/-- EDX becomes the release mask; EBX is zero, success (one), or fault (two). -/
def zeroTest : List Instr :=
  [.mov .eax (.imm 0), .alu .sub .eax (.reg .ebp), .alu .or .eax (.reg .ebp),
    .shift .shr .eax 31, .alu .xor .eax (.imm 1)]

def statusMask : List Instr :=
  [.mov .edx (.reg .ebx), .alu .and .edx (.reg .eax),
    .mov .ebp (.imm 0), .alu .sub .ebp (.reg .edx), .mov .edx (.reg .ebp),
    .mov .ebp (.imm 0), .alu .sub .ebp (.reg .ebx),
    .mov .ebx (.imm 2), .alu .sub .ebx (.reg .eax), .alu .and .ebx (.reg .ebp)]

def masks : List Instr := zeroTest ++ statusMask

def releaseArgs : List Instr :=
  [.mov .edi (.mem (incoming 0)), .mov .esi (.reg .esp),
    .alu .add .esi (.imm (BitVec.ofNat 32 candidateOffset)), .mov .ecx (.mem (incoming 3))]

def releaseStep : List Instr :=
  [.movzx8 .eax ⟨.esi, 0⟩, .alu .and .eax (.reg .edx), .store8 ⟨.edi, 0⟩ .al,
    .mov .eax (.imm 0), .store8 ⟨.esi, 0⟩ .al,
    .alu .add .esi (.imm 1), .alu .add .edi (.imm 1), .alu .sub .ecx (.imm 1), .alu .cmp .ecx (.imm 0)]

def releaseLoop : Prog isa := .loop (.block releaseStep) .ne

def release : Prog isa := .seq (.block masks) (.seq (.block releaseArgs)
  (.seq releaseLoop (.block [.mov .eax (.reg .ebx)])))

def tail : Prog isa := .seq (.block compareArgs) (.seq compareBytes release)

def check (preName : String) (pre : Prog isa) (publicName : String) (publicCode : Prog isa) : Prog isa :=
  .seq (.block precomputeArgs) (.seq (.call preName pre)
    (.seq (.block publicArgs) (.seq (.call publicName publicCode) tail)))

def body (crtName : String) (crt : Prog isa) (preName : String) (pre : Prog isa)
    (publicName : String) (publicCode : Prog isa) : Prog isa :=
  .seq (.block crtArgs) (.seq (.call crtName crt) (check preName pre publicName publicCode))

def restore : List Instr :=
  [.mov .edi (.mem (stackAt 0)), .mov .ebp (.mem (stackAt 8)), .mov .esi (.mem (stackAt 4))]

def code (crtName : String) (crt : Prog isa) (preName : String) (pre : Prog isa)
    (publicName : String) (publicCode : Prog isa) : Prog isa :=
  .frame (.push [.ebx, .ebp, .esi, .edi])
    (.seq (.frame (.alloc frameBytes) (body crtName crt preName pre publicName publicCode) (.free frameBytes))
      (.block restore)) (.pop .ebx 4)

end VG.Impl.Rsa.X86.PrivChecked
