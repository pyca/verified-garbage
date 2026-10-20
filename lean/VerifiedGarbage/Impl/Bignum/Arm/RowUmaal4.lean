module

public import VerifiedGarbage.Impl.Bignum.Arm.RowUmaal

/-! Four-word UMAAL rows keep the existing materialized carry convention. -/

@[expose] public section
namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def rowFirstAtU (k : Nat) : List Instr :=
  [.ldr .r2 .r12 k, .ldr .r3 .r0 k, .umaal .r3 .r11 .r2 .r9, .str .r3 .r0 k]

def rowAdvance4 : List Instr :=
  [.dp .add .r0 .r0 (.imm 16), .dp .add .r12 .r12 (.imm 16), .subs .lr .lr (.imm 4)]

/-- Save only the fourth accumulator word, which the common epilogue needs. -/
def rowBodyU4 : List Instr :=
  rowFirstAtU 0 ++ rowFirstAtU 4 ++ rowFirstAtU 8 ++ rowStepU 12 ++ rowAdvance4

def rowParity4 : List Instr := [.dp .and .r3 .lr (.imm 2), .cmp .r3 (.imm 0)]

def rowLoopU4 : Prog isa :=
  .seq (.block rowUJoin) (.seq (.block rowParity4)
    (.seq (.ite .ne (.block rowBodyU) (.block []))
      (.seq (.block [.cmp .lr (.imm 0)])
        (.seq (.ite .ne (.loop (.block rowBodyU4) .ne) (.block [])) (.block rowUEnd)))))

def rowU4 : Prog isa :=
  .seq (.block (rowSplit ++ rowParity)) (.seq (.ite .ne rowBody (.block []))
    (.seq (.block [.cmp .lr (.imm 0)]) (.seq (.ite .ne rowLoopU4 (.block [])) (.block rowJoin))))

end VG.Impl.Bignum.Arm
