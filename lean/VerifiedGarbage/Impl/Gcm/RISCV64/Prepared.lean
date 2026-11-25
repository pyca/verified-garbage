module

public import VerifiedGarbage.Impl.Gcm.RISCV64

/-! # GHASH on RISC-V with the key's words computed before

`vg_ghash_prepared(a0, y = a1, data = a2, n = a3, scratch = a4)`: `vg_ghash`
with the 36 doublewords of the key at `a0`. Its frame holds only the registers
it restores; `scratch` is not used. -/

@[expose] public section

namespace VG.Impl.Gcm.RISCV64.Prepared

open VG.RISCV64

def cachedStart : List Instr :=
  ([.addSp .t0 0] : List Instr) ++ saveAt 0 ++ maskCode ++ loadY

def cachedHash : Prog isa :=
  .frame (.alloc 112) (.seq (.block cachedStart) (.seq loopCode (.block (finish 0)))) (.free 112)

/-- The key's words' address: the buffer's, which the caller keeps at
`sp + 16`, and 960. -/
def loadPrepared : List Instr := [.addSp .t0 0, .load .d .a0 .t0 16, .addi .a0 .a0 960]

def preparedInvocation : Prog isa := .seq (.block loadPrepared) (.call "vg_ghash_prepared" cachedHash)

end VG.Impl.Gcm.RISCV64.Prepared
