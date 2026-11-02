module

public import VerifiedGarbage.Impl.Ecdh.RISCV64

/-!
# Numbers of `8 k` bytes in `k + 1` words on RISC-V

P-192's numbers are 24 bytes, kept in four words (`Gen4`'s field) whose
top word is zero: `loadNum0` clears the top word, then reads `k`
doublewords (`loadNum`). Writing one back is `storeNum` of its low `k`
words, as its top word is zero.
-/

@[expose] public section

namespace VG.Impl.Ecdh.RISCV64

open VG.RISCV64 VG.Impl.Weierstrass.RISCV64

/-- `[o] = ` the big-endian number of `8 k` bytes at `p + off`, in `k + 1`
words: the top word zero, then `k` doublewords, through `t0` and `t1`. -/
def loadNum0 (k o : Nat) (p : Reg) (off : Nat) : List Instr :=
  [.li .t0 0, .store .d .t0 wb (o + 8 * k)] ++ loadNum k o p off

end VG.Impl.Ecdh.RISCV64
