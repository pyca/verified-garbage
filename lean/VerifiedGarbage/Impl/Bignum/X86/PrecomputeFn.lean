module

public import VerifiedGarbage.Impl.Bignum.X86.PublicFn
public import VerifiedGarbage.Impl.Bignum.X86.PrecomputeOut

/-! # Public RSA modulus precomputation on i686 -/

@[expose] public section
namespace VG.Impl.Bignum.X86.PrecomputeFn
open VG VG.X86 VG.Impl.Bignum.X86.PublicContext

def entry : List Instr :=
  [.mov .eax (.mem (PublicFn.argument 4))] ++ PublicFn.save ++ [.mov .edi (.reg .eax)]

def failure : Prog isa :=
  .seq (.block [.mov .esi (.mem (PublicFn.argument 0)),
    .mov .ecx (.mem (PublicFn.argument 1)), .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx), .mov .eax (.imm 0)])
    (.loop (.block PublicFn.clearStep) .ne)

def importModulus (n : Nat) : Prog isa :=
  .seq (.block PublicFn.modulusArgs) (loadBE n (slot n 0))

def sized (n : Nat) : Prog isa :=
  .seq (importModulus n) (.seq (setup n)
    (.seq (.block [.mov .ebx (.mem (PublicFn.argument 0))]) (precomputeOut n)))

def dispatch : List Nat → Prog isa
  | [] => failure
  | n :: rest => .seq (.block [.alu .cmp .eax (.imm (BitVec.ofNat 32 n))])
      (.ite .e (sized n) (dispatch rest))

def valid : Prog isa := .seq (.block PublicFn.widthArgs) (dispatch PublicFn.widths)

def body : Prog isa :=
  .seq (.block PublicFn.modulusArgs) (.seq (.block modulusCheck) (.ite .e valid failure))

def code : Prog isa := .seq (.block entry) (.seq body (.block PublicFn.restore))

end VG.Impl.Bignum.X86.PrecomputeFn
