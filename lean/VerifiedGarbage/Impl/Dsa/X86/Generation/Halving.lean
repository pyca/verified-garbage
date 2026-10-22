module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.Header
public import VerifiedGarbage.Impl.Rsa.X86.KeyRt.CountEven
public import VerifiedGarbage.Impl.Rsa.X86.Recover

/-! Fixed-schedule extraction of the power of two in a primality exponent. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86

def halvingCount : Nat := 20
def halvingBit : Nat := 28
def halvingRemaining : Nat := Rsa.X86.Recover.sCnt

def halvingNext : List Instr :=
  Rsa.X86.Recover.cntNext ++ [.alu .cmp .eax (.imm 0)]

def halvingInit (L : Rsa.X86.KeyRt.Lay) : List Instr :=
  setHeader halvingCount 0 ++ Rsa.X86.KeyRt.bytesB L .eax ++
  List.replicate 3 (.alu .add .eax (.reg .eax)) ++ [.store (sc halvingRemaining) .eax]

def halvingPrepare (L : Rsa.X86.KeyRt.Lay) : Prog isa :=
  .seq (Rsa.X86.KeyRt.copy L 1 0)
    (.seq (.block [.mov .ebx (.imm 0)]) (Rsa.X86.KeyRt.half L 1))

def halvingStep (L : Rsa.X86.KeyRt.Lay) : Prog isa :=
  .seq (halvingPrepare L)
    (.seq (.block (Rsa.X86.KeyRt.countEven L halvingBit halvingCount 0))
      (.seq (Rsa.X86.KeyRt.sel L 0 0 1 halvingBit) (.block halvingNext)))

def halving (L : Rsa.X86.KeyRt.Lay) : Prog isa :=
  .seq (.block (halvingInit L)) (.loop (halvingStep L) .ne)

end VG.Impl.Dsa.X86.Generation
