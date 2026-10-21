module

public import VerifiedGarbage.Impl.Rsa.X86.Recover
public import VerifiedGarbage.Impl.Rsa.X86.KeyRt

/-! # Logarithmic Montgomery bootstrap for RSA recovery

For a normalized `k`-byte modulus, `2^(8k-8)` is below the modulus.
After `8+t` modular doublings this represents `2^t` in Montgomery form.
Each Montgomery square doubles that exponent; `t*2^j=8k` produces R².
The fixed public lengths below need only nine or eleven doublings and
10–12 squares. Other lengths retain the general doubling schedule.
-/

@[expose] public section
namespace VG.Impl.Rsa.X86.Bootstrap
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt
open VG.Impl.Rsa.X86.Recover (mR2 aZ aN mAcc)
open VG.Impl.Rsa.X86.Keys (seqs)

def lay : Lay := {len:=5,ws:=10,shape:=.narrow}

def seed : List Instr :=
 arrPtr lay .eax mR2 .edx ++
 [.alu .add .eax (.reg .edx),.alu .sub .eax (.imm 20),
  .mov .ecx (.imm 0x01000000),.store (at_ .eax 0) .ecx]

def doubles : Nat → Prog isa
 | 0 => .block []
 | j+1 => .seq (seqs (addMod lay mR2 mR2 mR2 aN aZ mAcc)) (doubles j)

def squares (mul : Nat → Nat → Nat → Prog isa) : Nat → Prog isa
 | 0 => .block []
 | j+1 => .seq (mul mR2 mR2 mR2) (squares mul j)

def run (mul : Nat → Nat → Nat → Prog isa) (t j : Nat) : Prog isa :=
 seqs [copy lay mR2 aZ,.block seed,doubles (t+8),squares mul j]

def choose (len t j : Nat) (mul : Nat → Nat → Nat → Prog isa) (fallback : Prog isa) : Prog isa :=
 .seq (.block [.mov .eax (.mem (argOp 5)),.alu .cmp .eax (.imm (BitVec.ofNat 32 len))])
 (.ite .e (run mul t j) fallback)

def setup (mul : Nat → Nat → Nat → Prog isa) (fallback : Prog isa) : Prog isa :=
 choose 256 1 11 mul (choose 384 3 10 mul (choose 512 1 12 mul fallback))

end VG.Impl.Rsa.X86.Bootstrap
