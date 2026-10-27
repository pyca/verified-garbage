module

public import VerifiedGarbage.Impl.Dsa.Generation.Layout
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PrimeBytes
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Workspace
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.CandidateArithmetic
public import VerifiedGarbage.Impl.Mgf1.X86_64

/-! # Native argument transfer from the persistent generation frame

The hash helper retains all caller-frame words. Generation uses those
words for the input tapes and their cursors, allowing each arithmetic
operation to initialize its own header without host intervention.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Mgf1.X86_64 (sp)

inductive ArgumentValue where
  | ones
  | literal (value : Nat)
  | frame (index offset : Nat)

structure HeaderArgument where
  destination : Nat
  value : ArgumentValue

def headerArgument (a : HeaderArgument) : List Instr :=
  (match a.value with
    | .ones => [.mov .rax (.imm (-1))]
    | .literal n => [.mov .rax (.imm (BitVec.ofNat 32 n))]
    | .frame k offset => [.mov .rax (.mem (sp (8 * k))),
        .alu .add .rax (.imm (BitVec.ofNat 32 offset))]) ++
    [.store (hdr a.destination) .rax]

def headerArguments (args : List HeaderArgument) : List Instr := args.flatMap headerArgument

/-- Candidate arithmetic uses the saved scratch base and public byte widths. -/
def candidateArguments (pLen qLen : Nat) : List HeaderArgument :=
  [⟨16, .frame 5 VG.Impl.Dsa.Generation.Layout.shaped⟩, ⟨17, .literal pLen⟩,
   ⟨18, .frame 5 VG.Impl.Dsa.Generation.Layout.q⟩, ⟨19, .literal qLen⟩,
   ⟨20, .frame 5 VG.Impl.Dsa.Generation.Layout.p⟩,
   ⟨21, .frame 5 VG.Impl.Dsa.Generation.Layout.exponent⟩, ⟨22, .ones⟩]

def candidateFromFrame (pLen qLen : Nat) : Prog isa :=
  .seq (.block (headerArguments (candidateArguments pLen qLen))) candidateBuild

/-- Select the arithmetic workspace using the saved scratch base. -/
def workspaceBase : List Instr :=
  [.mov .rdi (.mem (sp 40)),
   .alu .add .rdi (.imm (BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.arithmetic))]

end VG.Impl.Dsa.X86_64.Generation
