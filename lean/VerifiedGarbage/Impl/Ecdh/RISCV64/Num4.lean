module

public import VerifiedGarbage.Impl.Ecdh.RISCV64
public import VerifiedGarbage.Impl.Words.RISCV64

/-!
# Numbers of `8 k + 4` bytes to and from slots on RISC-V

P-224's numbers are 28 bytes, four words with the top one of four bytes:
`loadNum4` reads the top word from four bytes (`loadBE32`), then `k`
doublewords (`loadNum`), and `storeNum4` writes the top word's low four
bytes, then `k` doublewords (`storeNum`).
-/

@[expose] public section

namespace VG.Impl.Ecdh.RISCV64

open VG.RISCV64 VG.Impl.Weierstrass.RISCV64

/-- `[o] = ` the big-endian number of `8 k + 4` bytes at `p + off`: its top
word from the first four bytes, then `k` doublewords, through `t0` and `t1`. -/
def loadNum4 (k o : Nat) (p : Reg) (off : Nat) : List Instr :=
  Impl.Words.RISCV64.loadBE32 .t0 .t1 p off ++ [.store .d .t0 wb (o + 8 * k)] ++ loadNum k o p (off + 4)

/-- The `k + 1`-word number at `a` under the mask `a7`, to `q + off`
big-endian in `8 k + 4` bytes: its top word's low four bytes, then `k`
doublewords, through `t0` and `t1`. -/
def storeNum4 (k a : Nat) (q : Reg) (off : Nat) : List Instr :=
  [.load .d .t0 wb (a + 8 * k), .logic .and .t0 .t0 .a7] ++ Impl.Words.RISCV64.storeBE 4 .t0 .t1 q off ++
    storeNum k a q (off + 4)

end VG.Impl.Ecdh.RISCV64
