module

public import VerifiedGarbage.TCB.Arm.Isa

/-!
# X25519 and X448 exchange, with RFC 7748's check, on ARMv7

`vg_x25519_exchange` and `vg_x448_exchange(out = r0, scalar = r1,
point = r2, scratch = r3) -> u32` call the unchecked function (`vg_x25519`,
`vg_x448`, or a variant) with the same arguments, then OR together the `n`
bytes it wrote to `out` and return 1 if that is nonzero, 0 otherwise
(RFC 7748 §6.1, §6.2).

The call (`bl`) overwrites `lr`, so a frame of 4 bytes (`push {lr}`) keeps
it; `out` waits for the call in a frame of 4 bytes of its own below it
(`push {r0}`), whose pop loads it into `r1`. The bytes are loaded one at a
time (`ldrb`), and no branch depends on them: the result is
`((acc - 1) >> 31) ^ 1`, which is 1 iff the OR `acc`, below 256, is not
zero.
-/

@[expose] public section

namespace VG.Impl.Xdh.Arm

open VG.Arm

/-- ORs the first `i` bytes at `r1` into `r3`, with `r2`. -/
def orBytes : Nat → List Instr
  | 0 => []
  | i + 1 => orBytes i ++ [.ldrb .r2 .r1 i, .dp .orr .r3 .r3 (.reg .r2)]

/-- `r0 := 1` if the `n` bytes at `r1` are not all zero, else `0`. -/
def check (n : Nat) : List Instr :=
  .movw .r3 0 :: orBytes n ++
    [.dp .sub .r3 .r3 (.imm 1), .mov .r0 (.shifted .r3 .lsr 31), .dp .eor .r0 .r0 (.imm 1)]

/-- The call of `name`, whose code is `callee`, then the check of the `n`
bytes it wrote to `out`. -/
def exchange (name : String) (callee : Prog isa) (n : Nat) : Prog isa :=
  .frame (.push [.lr])
    (.seq (.frame (.push [.r0]) (.call name callee) (.pop .r1 4)) (.block (check n)))
    (.pop .lr 4)

end VG.Impl.Xdh.Arm
