module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.FermatExponent
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64Array
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Gcd64Preserve
public import VerifiedGarbage.Impl.Bignum.X86.PublicContext

/-! # Public-exponent coprimality with a whole-word 65537 fast path -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.ExponentFilter
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Bignum.X86.PublicContext

def fastArgs (w : Nat) : List Instr :=
  [.alu .add .edi (.imm (BitVec.ofNat 32 (slot w 5))), .mov .eax (.reg .edi),
    .alu .add .eax (.imm (BitVec.ofNat 32 (8 * w))), .store (at_ .esp 4) .eax]

def fast (w : Nat) : Prog isa :=
  .frame (.alloc 20)
    (.seq (.block (.store (at_ .esp 0) .edi :: fastArgs w))
      (.seq (FermatExponent.code 4) (.block [.mov .edi (.mem (at_ .esp 0))]))) (.free 20)

def general (w : Nat) : Prog isa :=
  .seq (.frame (.alloc 20) (Mod64.array (2 * w) (slot w 5) 128) (.free 20))
    (Gcd64.preserving (2 * w) (slot w 0) (slot w 5) 128)

def parity : List Instr :=
  [.mov .eax (.mem (sc 128)), .alu .and .eax (.imm 1), .alu .cmp .eax (.imm 0)]

def equal (value : Nat) : List Instr :=
  [.mov .eax (.mem (sc 128)), .alu .xor .eax (.imm (BitVec.ofNat 32 value)),
    .alu .or .eax (.mem (sc 132)), .alu .cmp .eax (.imm 0)]

def code (w : Nat) : Prog isa :=
  .seq (.block parity) (.ite .e (.block [.mov .eax (.imm 0)])
    (.seq (.block (equal 1)) (.ite .e (.block [.mov .eax (.imm 1)])
      (.seq (.block (equal 65537)) (.ite .e (fast w) (general w))))))

end VG.Impl.RsaKeyGen.X86.ExponentFilter
