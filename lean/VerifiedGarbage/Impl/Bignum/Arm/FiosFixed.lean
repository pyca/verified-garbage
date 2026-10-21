module

public import VerifiedGarbage.Impl.Bignum.Arm.Fios

/-! Fixed offsets keep the integrated Montgomery scan's pointers in registers. -/

@[expose] public section
namespace VG.Impl.Bignum.Arm.FiosFixed
open VG VG.Arm VG.Impl.Bignum.Arm

def pairAt (k : Nat) : Prog isa :=
  .seq (.block [.ldr .r3 .r12 k, .ldr .r6 .r0 (k+4)]) (.seq Fios.product
    (.seq (.block [.ldr .r3 .r12 (k+4), .ldr .r10 .r0 (k+8)]) (.seq Fios.product1
      (.seq (.block [.ldr .r5 .r4 k]) (.seq Fios.cancel (.seq (.block [.str .r6 .r0 k])
        (.seq (.block [.ldr .r5 .r4 (k+4)]) (.seq Fios.cancel1 (.block [.str .r10 .r0 (k+4)])))))))))

def pairs : Nat → Nat → Prog isa
  | _, 0 => .block []
  | k, count+1 => .seq (pairAt k) (pairs (k+8) count)

def advance (k : Nat) : List Instr :=
  [.dp .add .r0 .r0 (.imm (BitVec.ofNat 32 (4*k))),
   .dp .add .r12 .r12 (.imm (BitVec.ofNat 32 (4*k))),
   .dp .add .r4 .r4 (.imm (BitVec.ofNat 32 (4*k))),
   .subs .lr .lr (.imm (BitVec.ofNat 32 k))]

def code (n : Nat) : Prog isa :=
  .seq Fios.first (.seq Fios.body (.seq (pairs 0 ((n-2)/2))
    (.seq (.block (advance (n-2))) Fios.top)))

def round (n : Nat) : Prog isa :=
  .seq (.block Fios.args) (.seq (code n) (.block roundFinish))

end VG.Impl.Bignum.Arm.FiosFixed
