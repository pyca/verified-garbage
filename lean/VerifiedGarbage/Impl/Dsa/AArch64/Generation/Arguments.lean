module

public import VerifiedGarbage.Impl.Dsa.Generation.Layout
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PrimeBytes
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Workspace
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.CandidateArithmetic

/-! Transfer the persistent generation frame into each native operation's header. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum.AArch64

inductive ArgumentValue where
  | ones
  | literal (value : Nat)
  | frame (index offset : Nat)

structure HeaderArgument where
  destination : Nat
  value : ArgumentValue

def headerArgument (a : HeaderArgument) : List Instr :=
  (match a.value with
    | .ones => [movi .x3 0, .subImm .x .x3 .x3 1]
    | .literal n => [movi .x3 n]
    | .frame k offset => [.ldrSp .x3 (8 * k), movi .x4 offset, .add .x .x3 .x3 .x4]) ++
    [sth .x3 a.destination]

def headerArguments (args : List HeaderArgument) : List Instr := args.flatMap headerArgument

def candidateArguments (pLen qLen : Nat) : List HeaderArgument :=
  [⟨16, .frame 5 VG.Impl.Dsa.Generation.Layout.shaped⟩, ⟨17, .literal pLen⟩,
   ⟨18, .frame 5 VG.Impl.Dsa.Generation.Layout.q⟩, ⟨19, .literal qLen⟩,
   ⟨20, .frame 5 VG.Impl.Dsa.Generation.Layout.p⟩,
   ⟨21, .frame 5 VG.Impl.Dsa.Generation.Layout.exponent⟩, ⟨22, .ones⟩]

def candidateFromFrame (pLen qLen : Nat) : Prog isa :=
  .seq (.block (headerArguments (candidateArguments pLen qLen))) candidateBuild

/-- AArch64's actual width is slot 17 and draw width is slot 18. -/
def primeArguments (candidate len draw checks : Nat) : List HeaderArgument :=
  [⟨16, .frame 5 VG.Impl.Dsa.Generation.Layout.witness⟩, ⟨17, .literal len⟩,
   ⟨18, .literal draw⟩, ⟨19, .literal checks⟩,
   ⟨20, .frame 5 candidate⟩, ⟨24, .frame 14 0⟩,
   ⟨25, .frame 15 0⟩, ⟨27, .frame 16 0⟩]

def primeFromFrame (mul : Nat → Nat → Nat → Prog isa) (roundCode : List (Prog isa))
    (candidate len draw checks : Nat) : Prog isa :=
  .seq (.block (headerArguments (primeArguments candidate len draw checks)))
    (primeBytes mul roundCode len draw)

def workspaceBase : List Instr :=
  [.ldrSp .x0 40, movi .x3 VG.Impl.Dsa.Generation.Layout.arithmetic, .add .x .x0 .x0 .x3]

def checkPrime (mul : Nat → Nat → Nat → Prog isa) (roundCode : List (Prog isa))
    (w candidate len draw checks : Nat) : Prog isa :=
  .seq (workspace w) (primeFromFrame mul roundCode candidate len draw checks)

def primeResult : List Instr :=
  [ldh .x3 27, .strSp .x3 128, ldh .x3 31, .strSp .x3 152]

end VG.Impl.Dsa.AArch64.Generation
