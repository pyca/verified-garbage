module

public import VerifiedGarbage.Impl.Weierstrass.X86.Inv
public import VerifiedGarbage.Impl.Weierstrass.X86.InvMemory
import VerifiedGarbage.Impl.Rsa.X86.KeyRt
public import VerifiedGarbage.Impl.Rsa.X86.KeyWs

/-! # Thirty-step GCD batches for RSA recovery on i686

Signed full-width values occupy arrays 4 and 5. Array 3 holds the
low-word transition matrix; arrays 6, 7, 11, 12 and 13 are temporary.
The public batch counter uses the existing header word at byte 100.
-/

@[expose] public section
namespace VG.Impl.Rsa.X86.GcdBatch
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
open VG.Impl.Weierstrass.X86.Inv
open VG.Impl.Rsa.X86.KeyRt

def offset (n j : Nat) := 160+j*(4*n+8)
def seqs := VG.Impl.Rsa.X86.Keys.seqs

def copyExtend (n dst src : Nat) : List Instr :=
 VG.Impl.Weierstrass.X86.copy n dst src ++ zeros (dst+4*n) 1

def evenMask (src : Nat) : List Instr :=
 [.mov .ecx (.mem (sc src)),.alu .and .ecx (.imm 1),.alu .sub .ecx (.imm 1)]

def init (n : Nat) : List Instr :=
 copyExtend n (offset n 4) (offset n 8) ++ copyExtend n (offset n 5) (offset n 0) ++
 evenMask (offset n 0) ++ maskCopy n (offset n 13) (offset n 8) ++ zeros (offset n 13+4*n) 1 ++
 addInPlace (offset n 5) (offset n 13) (n+1) ++
 [.mov .eax (.imm 1),.store (sc (offset n 3)) .eax]

def start (n : Nat) : List Instr :=
 let W:=offset n 3
 VG.Impl.Weierstrass.X86.copy 1 (W+4) (offset n 4) ++ VG.Impl.Weierstrass.X86.copy 1 (W+8) (offset n 5) ++
 VG.Impl.Weierstrass.X86.setConst 2 (W+12) (1+2^96)

def row (n r : Nat) : List Instr :=
 linear (offset n 3+12+8*r) (offset n 3+16+8*r) (offset n 11) (offset n 4) (offset n 5)
   (offset n 13) (n+1) (n-1) ++ shr30 (offset n (6+r)) (offset n 11) (n+1)

def update (n : Nat) : List Instr :=
 row n 0 ++ row n 1 ++
 VG.Impl.Weierstrass.X86.copy (n+1) (offset n 4) (offset n 6) ++
 VG.Impl.Weierstrass.X86.copy (n+1) (offset n 5) (offset n 7)

def finish (n : Nat) : List Instr :=
 zeros (offset n 1) n ++ subInPlace (offset n 1) (offset n 4) n ++
 maskOf (offset n 4+4*n) ++
 VG.Impl.Weierstrass.X86.sel n (offset n 1) (offset n 4) (offset n 1)

def countDown (d : Nat) : List Instr :=
 [.mov .esi (.mem (sc d)),.alu .sub .esi (.imm 1),.store (sc d) .esi,.alu .test .esi (.reg .esi)]

def batch (n : Nat) : Prog isa :=
 .seq (.seq (.block (start n)) (wordSteps (offset n 3) 30))
   (.seq (.block (update n)) (.block (countDown 100)))

def body (n : Nat) : Prog isa := seqs [
 .block (init n ++ [.mov .eax (.imm (BitVec.ofNat 32 (3*(n+1)))),.store (sc 100) .eax]),
 .loop (batch n) .ne,.block (finish n)]

end VG.Impl.Rsa.X86.GcdBatch
