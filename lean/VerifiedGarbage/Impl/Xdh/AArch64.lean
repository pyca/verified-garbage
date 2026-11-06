module

public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# X25519 and X448 exchange, with RFC 7748's check, on AArch64

`vg_x25519_exchange` and `vg_x448_exchange(out = x0, scalar = x1,
point = x2, scratch = x3) -> u32` call the unchecked function (`vg_x25519`,
`vg_x448`) with the same arguments, then OR together the `n` bytes it wrote
to `out` and return 1 if that is nonzero, 0 otherwise (RFC 7748 §6.1,
§6.2).

The call (`bl`) overwrites `x30`, so a frame of 16 bytes (`push`) keeps it,
at `sp`; `out` waits for the call at `sp + 8`, the frame's other
doubleword, which the callee does not write. The bytes are loaded one at a
time (`ldrb`), and no branch depends on them: the result is
`((acc - 1) >> 63) ^ 1`, which is 1 iff the OR `acc`, below 256, is not
zero.
-/

@[expose] public section

namespace VG.Impl.Xdh.AArch64

open VG.AArch64

/-- `out` into the frame, at `sp + 8`. -/
def save : List Instr := [.addSp .x9 0, .str .x .x0 .x9 8]

/-- `out` back from the frame, into `x9`. -/
def restore : List Instr := [.addSp .x9 0, .ldr .x .x9 .x9 8]

/-- ORs the first `i` bytes at `x9` into `x10`, with `x11`. -/
def orBytes : Nat → List Instr
  | 0 => []
  | i + 1 => orBytes i ++ [.ldrb .x11 .x9 i, .logic .orr .x .x10 .x10 .x11]

/-- `x0 := 1` if the `n` bytes at `x9` are not all zero, else `0`. -/
def check (n : Nat) : List Instr :=
  .movz .x .x10 0 0 :: orBytes n ++
    [.subImm .x .x10 .x10 1, .lsr .x .x0 .x10 63, .movz .x .x11 1 0, .logic .eor .x .x0 .x0 .x11]

/-- The call of `name`, whose code is `callee`, then the check of the `n`
bytes it wrote to `out`. -/
def exchange (name : String) (callee : Prog isa) (n : Nat) : Prog isa :=
  .frame (.push .x30)
    (.seq (.block save) (.seq (.call name callee) (.seq (.block restore) (.block (check n)))))
    (.pop .x30)

end VG.Impl.Xdh.AArch64
