module

public import VerifiedGarbage.Impl.Bignum.X86.ExponentCheck
public import VerifiedGarbage.Impl.Bignum.X86.ModulusCheck
public import VerifiedGarbage.Impl.Bignum.X86.LoadBE
public import VerifiedGarbage.Impl.Bignum.X86.StoreBE
public import VerifiedGarbage.Impl.Bignum.X86.PublicPower
public import VerifiedGarbage.Impl.Bignum.X86.InputCompare
public import VerifiedGarbage.Impl.Bignum.X86.MaskOutput

/-! # Checked public RSA operation using the i686 cdecl ABI

The scratch header saves the four callee-saved registers. Only the public
modulus, exponent and lengths choose branches. Input acceptance is retained
as a mask at offset 144 and applied after the modular exponentiation.
-/

@[expose] public section
namespace VG.Impl.Bignum.X86.PublicFn
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Bignum.X86.PublicContext

def argument (i : Nat) : MemOp := at_ .esp (4 + 4 * i)

def savedRegisters : List (Reg × Nat) := [(.ebx, 0), (.ebp, 4), (.esi, 8), (.edi, 12)]
def save : List Instr := savedRegisters.map fun (r, d) => .store (at_ .eax d) r
def restore : List Instr := savedRegisters.map fun (r, d) => .mov r (.mem (sc d))

def entry : List Instr :=
  [.mov .eax (.mem (argument 8))] ++ save ++ [.mov .edi (.reg .eax)]

def modulusArgs : List Instr :=
  [.mov .esi (.mem (argument 2)), .mov .ecx (.mem (argument 3))]
def exponentArgs : List Instr :=
  [.mov .esi (.mem (argument 4)), .mov .ecx (.mem (argument 5))]
def inputArgs : List Instr :=
  [.mov .esi (.mem (argument 6)), .mov .ecx (.mem (argument 7))]
def outputArgs : List Instr :=
  [.mov .ebx (.mem (argument 0)), .mov .ecx (.mem (argument 1))]

def clearStep : List Instr :=
  [.store8 (at_ .esi 0) .al, .alu .add .esi (.imm 1),
   .alu .sub .ecx (.imm 1)]

def failure : Prog isa :=
  .seq (.block [.mov .esi (.mem (argument 0)), .mov .ecx (.mem (argument 1)), .mov .eax (.imm 0)])
    (.loop (.block clearStep) .ne)

def acceptanceOffset : Nat := 144

def importNumbers (n : Nat) : Prog isa :=
  .seq (.block modulusArgs) (.seq (loadBE n (slot n 0))
    (.seq (.block inputArgs) (loadBE n (slot n 6))))

def acceptAndPower (n : Nat) : Prog isa :=
  .seq (inputCompare n) (.seq (.block [.store (sc acceptanceOffset) .ecx]) (publicPower n))

def maskResult (n : Nat) : Prog isa :=
  .seq (.block [.mov .ecx (.mem (sc acceptanceOffset))]) (maskOutput n)

def writeResult (n : Nat) : Prog isa :=
  .seq (.block outputArgs) (.seq (storeBE (slot n 7))
    (.block [.mov .eax (.mem (sc acceptanceOffset)), .alu .and .eax (.imm 1)]))

def exportResult (n : Nat) : Prog isa := .seq (maskResult n) (writeResult n)

def sized (n : Nat) : Prog isa :=
  .seq (importNumbers n) (.seq (acceptAndPower n) (exportResult n))

def dispatch : List Nat → Prog isa
  | [] => failure
  | n :: rest => .seq (.block [.alu .cmp .eax (.imm (BitVec.ofNat 32 n))])
      (.ite .e (sized n) (dispatch rest))

def widths : List Nat := (List.range 121).map (· + 8)

def saveExponent : List Instr := [.store (sc 128) .ebx, .store (sc 132) .edx]

def widthArgs : List Instr :=
  [.mov .eax (.mem (argument 3)), .alu .add .eax (.imm 7), .shift .shr .eax 3]

def valid : Prog isa :=
  .seq (.block saveExponent) (.seq (.block widthArgs) (dispatch widths))

def scanExponent : Prog isa := .seq (.block exponentArgs) exponentCheck

def checkExponent : Prog isa :=
  .seq scanExponent (.seq (.block [.alu .cmp .eax (.imm 0)]) (.ite .e failure valid))

def body : Prog isa :=
  .seq (.block modulusArgs) (.seq (.block modulusCheck) (.ite .e checkExponent failure))

def code : Prog isa := .seq (.block entry) (.seq body (.block restore))

end VG.Impl.Bignum.X86.PublicFn
