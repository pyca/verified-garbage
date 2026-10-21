module

public import VerifiedGarbage.Impl.Bignum.X86_64

/-! Padding that keeps code after a changed loop at its former offsets. -/

@[expose] public section

namespace VG.Impl.Bignum.X86_64
open VG.X86_64

/-- `tens` ten-byte `movabs rax, 0` and `fours` four-byte `add rax, 1`: run
once after a loop whose body got shorter, so that the code after it keeps
the offsets modulo 64 it had (Zen 3's speed depends on them, as #2991
found). It writes only `rax` and the flags, dead where it is placed. -/
def tileFill (tens fours : Nat) : List Instr :=
  List.replicate tens (.movImm64 .rax 0) ++ List.replicate fours (.alu .add .rax (.imm 1))

end VG.Impl.Bignum.X86_64
