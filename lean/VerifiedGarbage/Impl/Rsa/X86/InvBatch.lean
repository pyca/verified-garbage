module

public import VerifiedGarbage.Impl.Weierstrass.X86.Inv
public import VerifiedGarbage.Impl.Weierstrass.X86.InvMemory
public import VerifiedGarbage.Impl.Rsa.X86.GcdBatch
public import VerifiedGarbage.Impl.Rsa.X86.KeyRt -- shake: keep (argOp occurs in exposed program definitions)

/-! # Batched RSA CRT inversion at the public prime width

Thirty low-word divsteps produce a matrix, then signed full-width rows
update f and g and Montgomery-reduced rows update the coefficients.
The public modulus and prime lengths select balanced 2048/3072/4096-bit
layouts; other inputs retain the general inverse. The working arrays and
header word at byte 100 are the existing inverse's mutable bank.
-/

@[expose] public section
namespace VG.Impl.Rsa.X86.InvBatch
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
open VG.Impl.Weierstrass.X86.Inv
open VG.Impl.Rsa.X86.KeyRt

def offset (w j : Nat) := 160+j*(4*w+8)
def seqs := VG.Impl.Rsa.X86.Keys.seqs
def config (w n : Nat) : Mod := {n:=n/2,mo:=offset w 2,tmp:=offset w 12,minv:=0}
def quo (acc tmp iv : Nat) : List Instr :=
 [.mov .eax (.mem (sc acc)),.mov .ecx (.mem (sc iv)),.mul .ecx,.store (sc tmp) .eax]
def redSum (acc modulus tmp iv n : Nat) : List Instr :=
 maskOf (acc+4*n) ++ [.mov .esi (.reg .ecx)] ++ zeros (acc+4*(n+1)) 1 ++
 quo acc tmp iv ++ rowAdd tmp acc modulus n ++ addSignWord (acc+4*(n+1))

def reduceLoaded (M : Mod) (acc tmp out iv : Nat) : List Instr :=
 redSum acc M.mo tmp iv (words M) ++ addIfNeg (acc+4) M.mo tmp (words M) ++ csub M (acc+4) out

def reduce (w n out : Nat) : List Instr :=
 reduceLoaded (config w n) (offset w 11) (offset w 12) out (offset w 3+28)

def virtualize (n M : Nat) : List Instr :=
 [.mov .eax (.mem (sc M)),.alu .xor .eax (.imm 1)] ++
 (List.range (n-1)).map (fun j => .alu .or .eax (.mem (sc (M+4*(j+1))))) ++
 [.alu .sub .eax (.imm 1),.alu .sbb .eax (.reg .eax),.alu .and .eax (.imm 2),
  .mov .ecx (.mem (sc M)),.alu .or .ecx (.reg .eax),.store (sc M) .ecx]

def operands (w n : Nat) : List Instr :=
 GcdBatch.copyExtend n (offset w 4) (offset w 2) ++
 GcdBatch.copyExtend n (offset w 5) (offset w 0) ++
 GcdBatch.evenMask (offset w 0) ++ maskCopy n (offset w 12) (offset w 2) ++
 zeros (offset w 12+4*n) 1 ++ addInPlace (offset w 5) (offset w 12) (n+1) ++
 [.mov .eax (.imm 1),.store (sc (offset w 3)) .eax]

def coefficients (w n : Nat) : List Instr :=
 zeros (offset w 6) (n+1) ++ zeros (offset w 7) (n+1) ++
 [.mov .eax (.imm 1),.store (sc (offset w 7)) .eax]

def inverseSetup (w : Nat) : List Instr :=
 [.mov .ebx (.mem (sc (offset w 2)))] ++ Dynamic.inverse ++ [.store (sc (offset w 3+28)) .eax]

def init (w n : Nat) : List Instr :=
 VG.Impl.Weierstrass.X86.copy n (offset w 2) (offset w 8) ++ virtualize n (offset w 2) ++
 operands w n ++ coefficients w n ++ inverseSetup w ++
 [.mov .eax (.imm (BitVec.ofNat 32 (3*(n+1)))),.store (sc 100) .eax]

def start (w : Nat) : List Instr :=
 let W:=offset w 3
 VG.Impl.Weierstrass.X86.copy 1 (W+4) (offset w 4) ++ VG.Impl.Weierstrass.X86.copy 1 (W+8) (offset w 5) ++
 setConst 2 (W+12) (1+2^96)

def update (w n : Nat) : List Instr :=
 let F:=offset w 4; let G:=offset w 5; let A:=offset w 6; let B:=offset w 7; let T:=offset w 11; let U:=offset w 12; let W:=offset w 3
 linear (W+12) (W+16) T F G U (n+1) (n-1) ++ shr30 (offset w 0) T (n+1) ++
 linear (W+20) (W+24) T F G U (n+1) (n-1) ++ shr30 (offset w 1) T (n+1) ++
 linear (W+12) (W+16) T A B U n (n-1) ++ reduce w n (offset w 13) ++
 linear (W+20) (W+24) T A B U n (n-1) ++ reduce w n (offset w 14) ++
 VG.Impl.Weierstrass.X86.copy (n+1) F (offset w 0) ++ VG.Impl.Weierstrass.X86.copy (n+1) G (offset w 1) ++
 VG.Impl.Weierstrass.X86.copy n A (offset w 13) ++ VG.Impl.Weierstrass.X86.copy n B (offset w 14)

def normalize (w n : Nat) : List Instr :=
 let F:=offset w 4; let A:=offset w 6; let U:=offset w 12
 VG.Impl.Weierstrass.X86.copy n U (offset w 2) ++ subInPlace U A n ++ maskOf (F+4*n) ++
 VG.Impl.Weierstrass.X86.sel n A A U ++ csub (config w n) A A

def twice (w n : Nat) : List Instr :=
 let A:=offset w 6
 addInPlace A A (n+1) ++ csub (config w n) A A ++ zeros (A+4*n) 1

def absolute (w n : Nat) : List Instr :=
 let F:=offset w 4; let O:=offset w 1
 zeros O w ++ subInPlace O F n ++ maskOf (F+4*n) ++ VG.Impl.Weierstrass.X86.sel n O F O

def finish (w n : Nat) : List Instr :=
 absolute w n ++ zeros (offset w 3) w ++ VG.Impl.Weierstrass.X86.copy n (offset w 3) (offset w 6)

def body (w n : Nat) : Prog isa := seqs [
 .block (init w n),
 .loop (.seq (.seq (.seq (.block (start w)) (wordSteps (offset w 3) 30)) (.block (update w n)))
   (.block [.mov .esi (.mem (sc 100)),decCounter,.store (sc 100) .esi,testCounter])) .ne,
 .block (normalize w n ++ [.mov .esi (.imm (BitVec.ofNat 32 (6*(n+1))))]),
 .loop (.block (twice w n ++ [decCounter,testCounter])) .ne,
 .block (finish w n)]

/-- A rejected public guard clears CF; the inverse fallback is emitted once. -/
def reject : Prog isa := .block [.alu .cmp .eax (.reg .eax)]

def guard (len n : Nat) : Prog isa :=
 .seq (.block [.mov .eax (.mem (argOp 7)),.alu .cmp .eax (.imm (BitVec.ofNat 32 len))])
 (.ite .e (.seq (.block [.mov .eax (.mem (argOp 9)),.alu .cmp .eax (.imm (BitVec.ofNat 32 (4*n+1)))])
   (.ite .b (.block [.mov .eax (.mem (argOp 11)),.alu .cmp .eax (.imm (BitVec.ofNat 32 (4*n+1)))]) reject)) reject)

def choose (len w n : Nat) (fallback : Prog isa) : Prog isa :=
 .seq (guard len n) (.ite .b (body w n) fallback)

def dispatch (fallback : Prog isa) : Prog isa :=
 choose 256 64 32 (choose 384 96 48 (choose 512 128 64 fallback))
end VG.Impl.Rsa.X86.InvBatch
