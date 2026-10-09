import VerifiedGarbage.Impl.X25519.X86.Field32

/-! The shared addition chain for inversion and square-root recovery. -/
namespace VG.Impl.Ed25519.X86
open VG.X86
open VG.Impl.X25519.X86.Field32 (mulCall)

def Z2 : Nat := 128
def T0 : Nat := 512
def T1 : Nat := 544
def T2 : Nat := 576
def T3 : Nat := 608

def sqn (o a n : Nat) : Prog isa :=
  .seq (.seq (mulCall o a a) (.block [.mov .esi (.imm (BitVec.ofNat 32 (n - 1)))]))
    (.loop (.seq (mulCall o o o) (.block [.alu .sub .esi (.imm 1)])) .ne)

/-- From z in Z2, leave z^(2^250 - 1) in T1 and z^11 in T0. -/
def power250 : Prog isa :=
  .seq (mulCall T0 Z2 Z2) <|
  .seq (mulCall T1 T0 T0) <| .seq (mulCall T1 T1 T1) <|
  .seq (mulCall T1 Z2 T1) <| .seq (mulCall T0 T0 T1) <|
  .seq (mulCall T2 T0 T0) <| .seq (mulCall T1 T1 T2) <|
  .seq (sqn T2 T1 5) <| .seq (mulCall T1 T2 T1) <|
  .seq (sqn T2 T1 10) <| .seq (mulCall T2 T2 T1) <|
  .seq (sqn T3 T2 20) <| .seq (mulCall T2 T3 T2) <|
  .seq (sqn T2 T2 10) <| .seq (mulCall T1 T2 T1) <|
  .seq (sqn T2 T1 50) <| .seq (mulCall T2 T2 T1) <|
  .seq (sqn T3 T2 100) <| .seq (mulCall T2 T3 T2) <|
  .seq (sqn T2 T2 50) (mulCall T1 T2 T1)

def invert : Prog isa := .seq power250 (.seq (sqn T1 T1 5) (mulCall T1 T1 T0))

def rootPower : Prog isa := .seq power250 (.seq (sqn T1 T1 2) (mulCall T1 T1 Z2))

end VG.Impl.Ed25519.X86
