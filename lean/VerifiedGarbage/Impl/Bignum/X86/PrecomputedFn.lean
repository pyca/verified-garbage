module

public import VerifiedGarbage.Impl.Bignum.X86.PublicFn
public import VerifiedGarbage.Impl.Bignum.X86.PrecomputedImport
public import VerifiedGarbage.Impl.Bignum.X86.PrecomputedChecks
public import VerifiedGarbage.Impl.Bignum.X86.PrecomputedPower

/-! # Checked i686 public RSA using the key's stored precomputation -/

@[expose] public section
namespace VG.Impl.Bignum.X86.PrecomputedFn
open VG VG.X86 VG.Impl.Bignum.X86.PublicContext VG.Impl.Mont.X86

def importKey (n : Nat) : Prog isa :=
  .seq (.block [.mov .esi (.mem (PublicFn.argument 2))]) (precomputedImport n)

def importInput (n : Nat) : Prog isa :=
  .seq (.block PublicFn.inputArgs) (loadBE n (slot n 6))

def acceptAndPower (n : Nat) : Prog isa :=
  .seq (inputCompare n) (.seq (.block [.store (sc PublicFn.acceptanceOffset) .ecx]) (precomputedPower n))

def applyInput (n : Nat) : Prog isa :=
  .seq (importInput n) (.seq (acceptAndPower n) (PublicFn.exportResult n))

def sized (n : Nat) : Prog isa :=
  .seq (importKey n) (.seq (precomputedChecks n) (.ite .e PublicFn.failure (applyInput n)))

def dispatch : List Nat → Prog isa
  | [] => PublicFn.failure
  | n :: rest => .seq (.block [.alu .cmp .eax (.imm (BitVec.ofNat 32 n))])
      (.ite .e (sized n) (dispatch rest))

def widthArgs : List Instr :=
  [.mov .eax (.mem (PublicFn.argument 1)), .alu .add .eax (.imm 7), .shift .shr .eax 3]

def valid : Prog isa :=
  .seq (.block PublicFn.saveExponent) (.seq (.block widthArgs) (dispatch PublicFn.widths))

def body : Prog isa := .seq PublicFn.scanExponent
  (.seq (.block [.alu .cmp .eax (.imm 0)]) (.ite .e PublicFn.failure valid))

def code : Prog isa := .seq (.block PublicFn.entry) (.seq body (.block PublicFn.restore))

end VG.Impl.Bignum.X86.PrecomputedFn
