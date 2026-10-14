module

public import VerifiedGarbage.Impl.Dsa.AArch64.Arithmetic
public import VerifiedGarbage.Impl.Dsa.Layout

/-! # Joint two-bit exponentiation for DSA verification

As x86-64's (`Impl/Dsa/X86_64/Joint.lean`): a sixteen-entry table holds
`g^i y^j R` for `i, j < 4`, in the place of RSA's CRT table. Each window
squares the accumulator twice and multiplies it by the entry of the next
two-bit digit of each exponent, read by RSA's masked selection from every
entry (`Crt.tabSelect`). Verification's two scalars `u` and `v` share their
squarings: half as many as two separate exponentiations.
-/

@[expose] public section

namespace VG.Impl.Dsa.AArch64.Joint

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64

/-- The second exponent's pointer. -/
def sExp2 : Nat := Crt.sRem

/-- `sV` holds `256 b + c` for the current bytes `b` of `u` and `c` of `v`,
shifted up two bits a window: the next two-bit digits are bits 14–15 and
6–7, into `sNib` as `4 b' + c'`. -/
def windowIndex : List Instr :=
  [ldh .x3 Crt.sV, .lsl .x .x4 .x3 2, sth .x4 Crt.sV, .lsr .x .x4 .x3 14, movi .x5 3,
    .logic .and .x .x4 .x4 .x5, .lsl .x .x4 .x4 2, .lsr .x .x3 .x3 6, .logic .and .x .x3 .x3 .x5,
    .add .x .x3 .x4 .x3, sth .x3 Crt.sNib]

/-- One window: `Y := Y⁴ T_v R⁻³`, the window count down into `x3`. -/
def window (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  [mul aY aY aY, mul aY aY aY, .block windowIndex] ++ Crt.tabSelect ++
  [mul aY aY Crt.aT, .block [ldh .x3 Crt.sBit, .subImm .x .x3 .x3 1, sth .x3 Crt.sBit]]

/-- Both bytes at index `sI` into `sV`, and the window count 4. -/
def byteHead : List Instr :=
  [ldh .x3 Crt.sExp, ldh .x4 Crt.sI, .add .x .x3 .x3 .x4, ldh .x5 sExp2, .add .x .x5 .x5 .x4,
    .ldrb .x3 .x3 0, .ldrb .x5 .x5 0, .lsl .x .x3 .x3 8, .add .x .x3 .x3 .x5, sth .x3 Crt.sV, movi .x3 4,
    sth .x3 Crt.sBit]

/-- The next byte index, and the bytes left into `x3`. -/
def byteNext : List Instr :=
  [ldh .x3 Crt.sI, .addImm .x .x3 .x3 1, sth .x3 Crt.sI, ldh .x4 Crt.sExpLen, .sub .x .x3 .x4 .x3]

def bytes (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .loop (seqs [.block byteHead, .loop (seqs (window mul)) (.nonzero .x .x3), .block byteNext]) (.nonzero .x .x3)

/-- Store the current `g^i y^j` entry, advance, and prepare the next entry.
The row/column choice is resolved while constructing the instruction list. -/
def advance (mul : Nat → Nat → Nat → Prog isa) (j : Nat) : Prog isa :=
  if j % 4 = 3 then .seq (mul aX aX aR2) (seqs (Crt.copyArr aY aX))
  else mul aY aY aXm

def buildStep (mul : Nat → Nat → Nat → Prog isa) (j : Nat) : Prog isa :=
  .seq (.seq (seqs (Crt.toEnt aY)) Crt.nextEnt) (advance mul j)

def buildSteps (mul : Nat → Nat → Nat → Prog isa) : Nat → Nat → Prog isa
  | _, 0 => .block []
  | j, count + 1 => .seq (buildStep mul j) (buildSteps mul (j + 1) count)

/-- The table after the workspace's last array, as RSA's (`Crt.tabBuild`). -/
def tableInit : List Instr :=
  [ldh .x3 (sArr aOne), ldh .x4 sW, .addImm .x .x4 .x4 2, .lsl .x .x4 .x4 3, .add .x .x3 .x3 .x4,
    sth .x3 Crt.sTab, sth .x3 Crt.sEnt]

/-- Inputs: gR in aR2, yR in aXm, R in aX/aY/aOne. The ordinary
one is restored after the table and accumulator have been initialized. -/
def build (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  .block tableInit,
  buildSteps mul 0 16, seqs (Crt.copyArr aY aOne), Arithmetic.small aOne 1]

/-- Encode both ordinary bases before reusing R²'s array for gR. -/
def encode (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  mul aY aR2 aOne, mul aX aX aR2, mul aXm aXm aR2,
  seqs (Crt.copyArr aR2 aX), seqs (Crt.copyArr aOne aY), seqs (Crt.copyArr aX aY)]

/-- Verification's two scalars, `u` and `v` in the parent workspace, have
the subgroup's public byte length. -/
def expInit : List Instr :=
  [ldh .x5 Crt.sLink, .ldr .x .x3 .x5 VG.Impl.Dsa.Layout.Field.qLen.offset, sth .x3 Crt.sExpLen,
    movi .x4 VG.Impl.Dsa.Layout.u, .add .x .x4 .x5 .x4, sth .x4 Crt.sExp,
    movi .x4 VG.Impl.Dsa.Layout.v, .add .x .x4 .x5 .x4, sth .x4 sExp2, movi .x3 0, sth .x3 Crt.sI]

/-- Load and encode both bases, then construct the joint table. -/
def prepare (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  Arithmetic.constants mul,
  Arithmetic.load aX VG.Impl.Dsa.Layout.arg VG.Impl.Dsa.Layout.argLen,
  Arithmetic.load aXm VG.Impl.Dsa.Layout.arg2 VG.Impl.Dsa.Layout.arg2Len,
  encode mul, build mul]

/-- Consume the two scalar buffers and decode the result. -/
def run (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  seqs [.block expInit, bytes mul, mul aY aY aOne]

/-- Two bases in the parent call header, and verification's u/v scalars. -/
def power (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (prepare mul) (run mul)

end VG.Impl.Dsa.AArch64.Joint
