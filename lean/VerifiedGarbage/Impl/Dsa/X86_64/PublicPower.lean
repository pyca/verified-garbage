module

public import VerifiedGarbage.Impl.Dsa.X86_64.Arithmetic

/-! # Exponentiation for public DSA subgroup orders

Only public exponents may use this path: table addresses and zero-window
branches depend on their digits. Secret exponents retain the masked path.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.PublicPower
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64

/-- Address one public table entry and the destination array. -/
def selectHead : List Instr :=
  [.mov .r12 (.mem (hdr sW)), .mov .rax (.reg .r12), .alu .add .rax (.imm 2),
    .mov .rdx (.mem (hdr Crt.sNib)), .imul .rax .rdx,
    .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
    .mov .rsi (.mem (hdr Crt.sTab)), .alu .add .rsi (.reg .rax),
    .mov .rbx (.mem (hdr (sArr Crt.aT)))]

def select : Prog isa := .seq (.block selectHead) copyWords

/-- Multiplication by the zeroth power is the identity. -/
def applyWindow (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (.block [.mov .rax (.mem (hdr Crt.sNib)), .alu .test .rax (.reg .rax)])
    (.ite .e (.block []) (.seq select (mul aY aY Crt.aT)))

/-- Reuse the public digit slot as a four-squaring counter. The next
window overwrites this slot with its digit before reading it. -/
def squaresInit : List Instr :=
  [.mov32 .rax (.imm 4), .store (hdr Crt.sNib) .rax]

def squaresNext : List Instr :=
  [.mov .rax (.mem (hdr Crt.sNib)), .alu .sub .rax (.imm 1), .store (hdr Crt.sNib) .rax]

def squares (sq : Prog isa) : Prog isa :=
  .seq (.block squaresInit) (.loop (.seq sq (.block squaresNext)) .ne)

/-- Four squarings, the next public digit, and its optional product. -/
def window (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  [squares sq,
    .block [.mov .rdx (.mem (hdr Crt.sV)), .mov .rax (.reg .rdx), .alu .add .rax (.reg .rax),
      .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
      .store (hdr Crt.sV) .rax, .shift .shr .rdx 4, .alu .and .rdx (.imm 15),
      .store (hdr Crt.sNib) .rdx],
    applyWindow mul,
    .block [.mov .rax (.mem (hdr Crt.sBit)), .alu .sub .rax (.imm 1), .store (hdr Crt.sBit) .rax]]

def byte (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  .block [.mov .rax (.mem (hdr Crt.sExp)), .mov .rcx (.mem (hdr Crt.sI)),
    .movzx8 .rax { base := .rax, index := some .rcx }, .store (hdr Crt.sV) .rax,
    .mov32 .rax (.imm 2), .store (hdr Crt.sBit) .rax],
  .loop (seqs (window sq mul)) .ne,
  .block [.mov .rax (.mem (hdr Crt.sI)), .alu .add .rax (.imm 1), .store (hdr Crt.sI) .rax,
    .alu .cmp .rax (.mem (hdr Crt.sExpLen))]]

def expLoop (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (sp sl : Nat) : Prog isa :=
  .seq (seqs ([.block [.mov .rax (.mem (hdr Crt.sLink)), .mov .rdx (.mem (Crt.ws .rax sp)),
    .store (hdr Crt.sExp) .rdx, .mov .rdx (.mem (Crt.ws .rax sl)), .store (hdr Crt.sExpLen) .rdx,
    .mov32 .rdx (.imm 0), .store (hdr Crt.sI) .rdx]] ++ Crt.tabBuild mul))
    (.loop (byte sq mul) .ne)

def encodedPower (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (sp sl : Nat) : Prog isa :=
  .seq (expLoop sq mul sp sl) (mul aY aY aOne)

def powerCore (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (sp sl : Nat) : Prog isa :=
  .seq (Arithmetic.encodePower mul) (encodedPower sq mul sp sl)

def power (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) (bp bl sp sl : Nat) : Prog isa :=
  .seq (Arithmetic.constants mul) (.seq (Arithmetic.load aX bp bl) (powerCore sq mul sp sl))

end VG.Impl.Dsa.X86_64.PublicPower
