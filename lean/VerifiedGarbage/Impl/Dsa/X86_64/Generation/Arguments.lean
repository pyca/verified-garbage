module

public import VerifiedGarbage.Impl.Dsa.Generation.Layout
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PrimeBytes
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Workspace
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
  | literal (value : Nat)
  | frame (index offset : Nat)

structure HeaderArgument where
  destination : Nat
  value : ArgumentValue

def headerArgument (a : HeaderArgument) : List Instr :=
  (match a.value with
    | .literal n => [.mov .rax (.imm (BitVec.ofNat 32 n))]
    | .frame k offset => [.mov .rax (.mem (sp (8 * k))),
        .alu .add .rax (.imm (BitVec.ofNat 32 offset))]) ++
    [.store (hdr a.destination) .rax]

def headerArguments (args : List HeaderArgument) : List Instr := args.flatMap headerArgument

/-- Frame words 5, 13, 15 and 16 hold the scratch base, witness tape,
its byte length and consumed-byte count, respectively. -/
def primeArguments (candidate len draw checks : Nat) : List HeaderArgument :=
  [⟨16, .frame 5 VG.Impl.Dsa.Generation.Layout.witness⟩, ⟨17, .literal draw⟩,
   ⟨18, .literal len⟩, ⟨19, .literal checks⟩,
   ⟨20, .frame 5 candidate⟩, ⟨23, .frame 13 0⟩,
   ⟨24, .frame 15 0⟩, ⟨25, .frame 16 0⟩]

def primeFromFrame (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (candidate len draw checks : Nat) : Prog isa :=
  .seq (.block (headerArguments (primeArguments candidate len draw checks)))
    (primeBytes mul round len draw)

def checkPrime (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa)
    (w candidate len draw checks : Nat) : Prog isa :=
  .seq (workspace w) (primeFromFrame mul round candidate len draw checks)

/-- Save the consumed witness count and status for the next search step. -/
def primeResult : List Instr :=
  [.mov .rax (.mem (hdr 25)), .store (sp 128) .rax,
   .mov .rax (.mem (hdr 29)), .store (sp 152) .rax]

end VG.Impl.Dsa.X86_64.Generation
