module

public import VerifiedGarbage.Impl.Dsa.X86.Pow
public import VerifiedGarbage.Impl.Dsa.X86.Arithmetic
public import VerifiedGarbage.Spec.Dsa.ModArith

/-! # DSA's products as functions on IA-32

`vg_dsa_mulmod_{n}` (`Spec/Dsa/ModArith.lean`) multiplies the ordinary
integers in slots 5 and 8 modulo the one in slot 0, into slot 6
(`ordinaryMul`), once it has set up the context (`contextSetup`), with the
register saves of `Pow.lean`. The caller loads the operands and passes the
working space as `vg_dsa_pow_{n}_{e}`'s callers do (`Pow.call`), so each
width has one product shared by every DSA function.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86.Arith
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Pow

def mulBody (n : Nat) : Prog isa :=
  .seq (.block Pow.save) (.seq (contextSetup n) (.seq (ordinaryMul n) (.block Pow.restore)))

def mulLayout (n : Nat) : Spec.Dsa.ModArith.MulLayout where
  n := n
  modulus := slot n 0
  a := slot n 5
  b := slot n 8
  result := slot n 6
  scratch := Pow.scratch n
  size := contextBytes n

def mulName (n : Nat) : String := (Spec.Dsa.ModArith.mulApi (mulLayout n)).name

/-- Pass the workspace and its length using cdecl's two stack arguments. -/
def mulCall (n : Nat) : Prog isa :=
  .seq (.block [.mov .eax (.imm (BitVec.ofNat 32 (contextBytes n / 8)))])
    (.frame (.push [.eax, .edi]) (.call (mulName n) (mulBody n)) (.pop .eax 2))

end VG.Impl.Dsa.X86.Arith
