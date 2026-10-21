module

public import VerifiedGarbage.Impl.Bignum.Arm.Fios

/-! Keep one product ahead of reduction, spacing both UMAAL carry chains. -/

@[expose] public section
namespace VG.Impl.Bignum.Arm.FiosPipelined
open VG VG.Arm VG.Impl.Bignum.Arm

def advance (k : Nat) : List Instr :=
  [.dp .add .r0 .r0 (.imm (BitVec.ofNat 32 (4*k))),
   .dp .add .r12 .r12 (.imm (BitVec.ofNat 32 (4*k))),
   .dp .add .r4 .r4 (.imm (BitVec.ofNat 32 (4*k))),
   .subs .lr .lr (.imm (BitVec.ofNat 32 k))]

def productAt (k : Nat) (dst : Reg) : Prog isa :=
  .seq (.block [.ldr .r3 .r12 k, .ldr dst .r0 (k+4)])
    (.block [.umaal dst .r7 .r3 .r1])

def cancelAt (k : Nat) (dst : Reg) : Prog isa :=
  .seq (.block [.ldr .r5 .r4 k])
    (.seq (.block [.umaal dst .r8 .r5 .r2]) (.block [.str dst .r0 k]))

def step (k : Nat) (pending next : Reg) : Prog isa :=
  .seq (productAt (k+4) next) (cancelAt k pending)

def pair (k : Nat) : Prog isa := .seq (step k .r6 .r10) (step (k+4) .r10 .r6)

def pairs : Nat → Nat → Prog isa
  | _, 0 => .block []
  | k, count+1 => .seq (pair k) (pairs (k+8) count)

def code (n : Nat) : Prog isa :=
  .seq Fios.first (.seq Fios.body (.seq (productAt 0 .r6)
    (.seq (pairs 0 ((n-4)/2)) (.seq (step (4*(n-4)) .r6 .r10)
      (.seq (cancelAt (4*(n-3)) .r10) (.seq (.block (advance (n-2))) Fios.top))))))

end VG.Impl.Bignum.Arm.FiosPipelined
