module

public import VerifiedGarbage.Impl.Rsa.X86.Inverse
public import VerifiedGarbage.Impl.Bignum.X86.PublicFn

/-! # CRT parameter calculation on i686

The public modulus length selects the native-word width. All key arithmetic
uses fixed-address workspace arrays; failed checks mask all three outputs.
-/

@[expose] public section
namespace VG.Impl.Rsa.X86.CrtValues
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Rsa.X86.Keys
open VG.Impl.Bignum.X86

def sPodd : Nat := 116
def sE1 : Nat := 120
def sE2 : Nat := 124
def sE3 : Nat := 128
def sMask : Nat := 132

def aOne : Nat := 15
def aQ : Nat := 16
def aP : Nat := 17
def aDQ : Nat := 18
def aDR : Nat := 19
def aDD : Nat := 20
def aDT : Nat := 21
def aDR2 : Nat := 22
def aDR3 : Nat := 23
def aD : Nat := 24
def nArr : Nat := 25

def div (w r : Nat) : Prog isa :=
  Div.code w (slot w aDQ) (slot w r) (slot w aDD) (slot w aDT)

def invSetup (w : Nat) : List (Prog isa) := [
  copy w 0 aQ, copy w aM aP, .block (orOne w aM), copy w 1 aM,
  .block (setOne w 2 ++ setOne w aOne), sub3 w aNM aZero aM]

def checks (w : Nat) : Prog isa := seqs ([
  eqS w sE1 aDQ aQ aT1, eqS w sE2 aDR aZero aT1] ++ invSetup w ++ [
  inverse w, eqS w sE3 1 aOne aT1,
  .block (andS sMask sPodd sE1 ++ andS sMask sMask sE2 ++ andS sMask sMask sE3),
  copy w aDQ aD, copy w aDD aP, .block (clrLow w aDD)])

def firstDiv (w : Nat) : Prog isa := seqs [
  copy w aDD aP, .block (bitOf w sPodd aP), div w aDR]

def divQ (w : Nat) : Prog isa := seqs [
  copy w aDQ aD, copy w aDD aQ, .block (clrLow w aDD), div w aDR3]

def core (w : Nat) : Prog isa :=
  .seq (firstDiv w) (.seq (checks w) (.seq (div w aDR2) (divQ w)))

def entry : List Instr :=
  [.mov .eax (.mem (PublicFn.argument 14))] ++ PublicFn.save ++ [.mov .edi (.reg .eax)]

def inputArgs (i : Nat) : List Instr :=
  [.mov .esi (.mem (PublicFn.argument i)), .mov .ecx (.mem (PublicFn.argument (i + 1)))]

def load (n arg j : Nat) : Prog isa :=
  .seq (.block (inputArgs arg)) (loadBE n (slot (2 * n) j))

def loads (n : Nat) : Prog isa := seqs [
  Dynamic.zerosW hdr (nArr * (2 * n + 2)),
  load n 6 aDQ, load n 8 aP, load n 10 aQ, load n 12 aD]

def store (n arg j : Nat) : Prog isa := seqs [
  sel (2 * n) j aZero j sMask,
  .block [.mov .ebx (.mem (PublicFn.argument arg)), .mov .ecx (.mem (PublicFn.argument (arg + 1)))],
  storeBE (slot (2 * n) j)]

def stores (n : Nat) : Prog isa := seqs [
  store n 0 aDR2, store n 2 aDR3, store n 4 3,
  .block [.mov .eax (.mem (sc sMask))]]

def clear (arg : Nat) : Prog isa :=
  .seq (.block [.mov .esi (.mem (PublicFn.argument arg)),
    .mov .ecx (.mem (PublicFn.argument (arg + 1))), .mov .eax (.imm 0)])
    (.loop (.block PublicFn.clearStep) .ne)

def failure : Prog isa := seqs [clear 0, clear 2, clear 4]

def sized (n : Nat) : Prog isa := seqs [loads n, core (2 * n), stores n]

def dispatch : List Nat → Prog isa
  | [] => failure
  | n :: rest => .seq (.block [.alu .cmp .eax (.imm (BitVec.ofNat 32 n))])
      (.ite .e (sized n) (dispatch rest))

def valid : Prog isa :=
  .seq (.block [.mov .eax (.mem (PublicFn.argument 7)), .alu .add .eax (.imm 7), .shift .shr .eax 3])
    (dispatch PublicFn.widths)

def body : Prog isa :=
  .seq (.block (inputArgs 6)) (.seq (.block modulusCheck) (.ite .e valid failure))

def code : Prog isa := .seq (.block entry) (.seq body (.block PublicFn.restore))

end VG.Impl.Rsa.X86.CrtValues
