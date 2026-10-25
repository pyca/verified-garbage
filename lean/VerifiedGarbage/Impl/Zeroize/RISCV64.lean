module

public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# Zeroization: RISC-V implementation

`vg_zeroize(p = a0, len = a1)`: byte stores (`sb`) up to the first 8-byte
aligned address (or the end), doubleword stores (`sd`) of the aligned part,
then a byte tail, so that every access is naturally aligned. The head is
`(-p) mod 8` bytes, at most `len`. The loops count down to zero, and only
`p` and `len` decide the branches and addresses.
-/

@[expose] public section

namespace VG.Impl.Zeroize.RISCV64
open VG.RISCV64

def step (word : Bool) : List Instr :=
  [.store (if word then .d else .b) .t0 .a0 0, .addi .a0 .a0 (if word then 8 else 1),
   .addi .t1 .t1 (-1)]

def loop (word : Bool) : Prog isa :=
  .ite (.zero .t1) (.block []) (.loop (.block (step word)) (.nonzero .t1))

/-- `t0 = 0`, and `t1` the bytes before the first aligned address, `(-p) mod
8`, at most `len`, which `a1` loses. -/
def head : Prog isa :=
  .seq (.block [.li .t0 0, .li .t1 0, .sub .t1 .t1 .a0, .logicImm .and .t1 .t1 7,
    .sltu .t2 .a1 .t1])
  (.seq (.ite (.nonzero .t2) (.block [.addi .t1 .a1 0]) (.block []))
    (.block [.sub .a1 .a1 .t1]))

def zeroize : Prog isa :=
  .seq head (.seq (loop false)
    (.seq (.block [.shift .srl .d .t1 .a1 3, .logicImm .and .a1 .a1 7]) (.seq (loop true)
      (.seq (.block [.addi .t1 .a1 0]) (loop false)))))

end VG.Impl.Zeroize.RISCV64
