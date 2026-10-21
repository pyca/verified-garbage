module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyIO
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateArgs
public import VerifiedGarbage.Impl.Mont.X86.Compact

/-! # RSA key assembly on the native 32-bit cdecl ABI

Each supported width instantiates native paired-word products, a prime-width
LCM GCD and CRT inverse, and the public-width inverse for an odd exponent.
Only the public width, the public exponent and the released retry status
select different control paths. The working bank is initialized before use.
-/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.Key
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Rsa.X86.Keys

def enter : Prog isa :=
  .seq (.block [.mov .edi (.mem (CandidateArgs.arg 16))]) (CandidateArgs.copies 18)

def sized (n : Nat) : Prog isa := seqs [
  clearArrays n, loadPrime n 16 aPa, loadPrime n 24 aQa,
  primes n, lcmPart n, dPart n, smallMask n,
  .ite .ne retry (keyPart n), writeOutputs n]

def widths : List Nat := (List.range 61).map (· + 4)

def dispatch : List Nat → Prog isa
  | [] => .block [.mov .eax (.imm 0)]
  | w :: rest => .seq (.block [.alu .cmp .eax (.imm (BitVec.ofNat 32 w))])
      (.ite .e (sized (4 * w)) (dispatch rest))

def body : Prog isa := .seq enter
  (.seq (.block [.mov .eax (.mem (sc 4)), .shift .shr .eax 4]) (dispatch widths))

def code : Prog isa :=
  .frame (.push [.ebx, .ebp, .esi, .edi])
    (.seq body (.block Compact.restoreRegs)) (.pop .ebx 4)

end VG.Impl.RsaKeyGen.X86.Key
