import VerifiedGarbage.Impl.Weierstrass.X86.Jacobian

/-! Width-five NAF recoding of a public 256-bit scalar into 257 bytes.
The nine-word residual lives in scratch memory on the register-limited x86 ISA. -/
namespace VG.Impl.Weierstrass.X86.Naf
open VG VG.X86 VG.Impl.Mont.X86

/-- The ninth word holds the carry when a negative digit rounds up the scalar. -/
def init (src work : Nat) : List Instr :=
  copy 8 work src ++ [.mov .eax (.imm 0), .store (sc (work+32)) .eax,
    .mov .esi (.imm 0)]

def oddDigit : Prog isa :=
  .seq (.block [.mov .ecx (.reg .eax), .alu .and .ecx (.imm 31), .alu .cmp .ecx (.imm 16)])
    (.ite .b (.block []) (.block [.alu .sub .ecx (.imm 32)]))

/-- One word of a sign-extended subtraction; loads and stores preserve the borrow. -/
def subWord (op : AluOp) (work i : Nat) (r : Reg) : List Instr :=
  [.mov .eax (.mem (sc (work+4*i))), .alu op .eax (.reg r),
   .store (sc (work+4*i)) .eax]

def sign : List Instr :=
  [.mov .eax (.reg .ecx), .shift .shr .eax 31, .mov .edx (.imm 0),
   .alu .sub .edx (.reg .eax)]

/-- Subtract the signed digit in ecx, extending its sign through the residual. -/
def subtractDigit (work : Nat) : List Instr :=
  sign ++ subWord .sub work 0 .ecx ++
  (List.range 8).flatMap fun i => subWord .sbb work (i+1) .edx

def adjust (work : Nat) : Prog isa :=
  .seq (.block [.mov .eax (.mem (sc work)), .mov .ecx (.reg .eax),
    .alu .and .ecx (.imm 1), .alu .test .ecx (.reg .ecx)])
    (.ite .e (.block []) (.seq oddDigit (.block (subtractDigit work))))

/-- Shift one word and import the next word's low bit into its high bit. -/
def shiftWord (work i : Nat) : List Instr :=
  [.mov .eax (.mem (sc (work+4*i))), .shift .shr .eax 1,
   .mov .edx (.mem (sc (work+4*(i+1)))), .alu .and .edx (.imm 1),
   .shift .ror .edx 1, .alu .add .eax (.reg .edx), .store (sc (work+4*i)) .eax]

/-- Divide the even residual by two. Low-to-high stores preserve unread words. -/
def shift (work : Nat) : List Instr :=
  (List.range 8).flatMap (shiftWord work) ++
  [.mov .eax (.mem (sc (work+32))), .shift .shr .eax 1, .store (sc (work+32)) .eax]

/-- edi remains the scratch base; ebx addresses this iteration's output byte. -/
def storeDigit (dst : Nat) : List Instr :=
  [.mov .ebx (.reg .edi), .alu .add .ebx (.reg .esi),
   .store8 {base := .ebx, disp := dst} .cl]

def step (dst work : Nat) : Prog isa :=
  .seq (adjust work) (.block (storeDigit dst ++ shift work ++
    [.alu .add .esi (.imm 1), .alu .cmp .esi (.imm 257)]))

def prep (dst src work : Nat) : Prog isa :=
  .seq (.block (init src work)) (.loop (step dst work) .b)

end VG.Impl.Weierstrass.X86.Naf
