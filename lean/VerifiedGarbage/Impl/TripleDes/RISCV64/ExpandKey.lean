module

public import VerifiedGarbage.Impl.TripleDes.RISCV64.Common
public import VerifiedGarbage.Impl.Words64.RISCV64
public import VerifiedGarbage.Impl.Words.RISCV64.Loops
public import VerifiedGarbage.Impl.Words.RISCV64.Word64
public import VerifiedGarbage.Spec.TripleDes

/-!
# Triple DES key expansion on RISC-V

The algorithm of the PPC64LE implementation (`Impl/TripleDes/PPC64LE/ExpandKey.lean`):
`expandKey` (key = a0, key_len = a1, schedule = a2) expands each 8-byte
component key in turn: PC-1 splits it into C (`a3`) and D (`a4`), each round
rotates them and stores PC-2 of them in the round's slot (at `a5`), and
`a6` counts the rounds. The contract states no alignment for the key or the
schedule, so they are accessed a byte at a time; for a 16-byte key the
third schedule is a byte-wise copy of the first. Only temporaries and
argument registers are used, so the function needs no working space. The
round count and the key length are public.
-/

@[expose] public section

namespace VG.Impl.TripleDes.RISCV64.Key

open VG.RISCV64 VG.Impl.TripleDes.RISCV64
open VG.Impl.Words.RISCV64 (loadBE64 copyLoop)
open VG.Impl.Words64.RISCV64 (storeLE64)

def load (offset component : Nat) : List Instr :=
  loadBE64 .t0 .t1 .a0 offset ++ permuteCode Spec.TripleDes.pc1 64 .t2 .t0 .t3 ++
    ([.shift .srl .d .a3 .t2 28, movR .a4 .t2] : List Instr) ++ mask .a4 28 ++
    [.li .a6 0, .addi .a5 .a2 (128 * component : Nat)]

def rotate28 (r : Reg) (n : Nat) : List Instr :=
  ([.shift .srl .d .t0 r (28 - n), .shift .sll .d r r n, .logic .xor r r .t0] : List Instr) ++
    mask r 28

def rotate (n : Nat) : Prog isa := .block (rotate28 .a3 n ++ rotate28 .a4 n)

def rotation : Prog isa :=
  .seq (.block [.shift .srl .d .t0 .a6 1])
    (.ite (.zero .t0) (rotate 1)
      (.seq (.block [.addi .t0 .a6 (-8)])
        (.ite (.zero .t0) (rotate 1)
          (.seq (.block [.addi .t0 .a6 (-15)])
            (.ite (.zero .t0) (rotate 1) (rotate 2))))))

def storeRound : List Instr :=
  ([.shift .sll .d .t0 .a3 28, .logic .xor .t0 .t0 .a4] : List Instr) ++
    permuteCode Spec.TripleDes.pc2 56 .t2 .t0 .t3 ++ storeLE64 .t2 .t1 .t4 .a5 0 ++
    ([.addi .a5 .a5 8, .addi .a6 .a6 1, .addi .t0 .a6 (-16)] : List Instr)

def component (offset index : Nat) : Prog isa :=
  .seq (.block (load offset index)) (.loop (.seq rotation (.block storeRound)) (.nonzero .t0))

/-- The first schedule's 128 bytes copied to the third's. -/
def copyThird : Prog isa :=
  .seq (.block [movR .t0 .a2, .addi .t1 .a2 256, .li .t2 128]) (copyLoop .t3 .t0 .t1 .t2)

def expandKey : Prog isa :=
  .seq (component 0 0)
    (.seq (component 8 1)
      (.seq (.block [.addi .t0 .a1 (-16)])
        (.ite (.zero .t0) copyThird (component 16 2))))

end VG.Impl.TripleDes.RISCV64.Key
