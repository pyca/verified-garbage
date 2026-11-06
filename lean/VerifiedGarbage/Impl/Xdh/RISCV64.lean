module

public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# X25519 and X448 exchange, with RFC 7748's check, on RISC-V

`vg_x25519_exchange` and `vg_x448_exchange(out = a0, scalar = a1,
point = a2, scratch = a3) -> u32` call the unchecked function (`vg_x25519`,
`vg_x448`) with the same arguments, then OR together the `n` bytes it wrote
to `out` and return 1 if that is nonzero, 0 otherwise (RFC 7748 §6.1,
§6.2).

The call overwrites our return address, so a frame of 16 bytes (`push`)
keeps it, at `sp + 8` in the frame; `out` waits for the call at `sp`, the
frame's other doubleword, which the callee does not write. The bytes are
loaded one at a time (`lbu`), so no access is misaligned, and no branch
depends on them.
-/

@[expose] public section

namespace VG.Impl.Xdh.RISCV64

open VG.RISCV64

/-- `out` into the frame, at `sp`. -/
def save : List Instr := [.addSp .t0 0, .store .d .a0 .t0 0]

/-- `out` back from the frame, into `t0`. -/
def restore : List Instr := [.addSp .t0 0, .load .d .t0 .t0 0]

/-- ORs the first `i` bytes at `t0` into `t1`, with `t2`. -/
def orBytes : Nat → List Instr
  | 0 => []
  | i + 1 => orBytes i ++ [.load .b .t2 .t0 i, .logic .or .t1 .t1 .t2]

/-- `a0 := 1` if the `n` bytes at `t0` are not all zero, else `0`. -/
def check (n : Nat) : List Instr :=
  .li .t1 0 :: orBytes n ++ [.li .t2 0, .sltu .a0 .t2 .t1]

/-- The call of `name`, whose code is `callee`, then the check of the `n`
bytes it wrote to `out`. -/
def exchange (name : String) (callee : Prog isa) (n : Nat) : Prog isa :=
  .frame (.push .ra)
    (.seq (.block save) (.seq (.call name callee) (.seq (.block restore) (.block (check n)))))
    (.pop .ra)

end VG.Impl.Xdh.RISCV64
