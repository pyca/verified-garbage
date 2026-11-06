module

public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# X25519 and X448 exchange, with RFC 7748's check, on PPC64LE

`vg_x25519_exchange` and `vg_x448_exchange(out = r3, scalar = r4,
point = r5, scratch = r6) -> u32` call the unchecked function (`vg_x25519`,
`vg_x448`) with the same arguments, then OR together the `n` bytes it wrote
to `out` and return 1 if that is nonzero, 0 otherwise (RFC 7748 §6.1,
§6.2).

The call (`bl`) overwrites the link register, so it waits in a frame of 48
bytes (`push`, saving `r0`, into which `mflr` moves it), at `sp + 32`; `out`
waits for the call at `sp + 40`, the frame's other doubleword, which the
callee does not write. The bytes are loaded one at a time (`lbz`), and no
branch depends on them: the result is `((acc - 1) >> 63) ^ 1`, which is 1
iff the OR `acc`, below 256, is not zero.
-/

@[expose] public section

namespace VG.Impl.Xdh.PPC64LE

open VG.PPC64LE

/-- `out` into the frame, at `sp + 40`. -/
def save : List Instr := [.addSp .r12 0, .store .d .r3 .r12 40]

/-- `out` back from the frame, into `r12`. -/
def restore : List Instr := [.addSp .r12 0, .load .d .r12 .r12 40]

/-- ORs the first `i` bytes at `r12` into `r11`, with `r10`. -/
def orBytes : Nat → List Instr
  | 0 => []
  | i + 1 => orBytes i ++ [.lbz .r10 .r12 i, .logic .or .r11 .r11 .r10]

/-- `r3 := 1` if the `n` bytes at `r12` are not all zero, else `0`. -/
def check (n : Nat) : List Instr :=
  .li .r11 0 :: orBytes n ++ [.subi .r11 .r11 1, .lsr .d .r3 .r11 63, .li .r10 1, .logic .xor .r3 .r3 .r10]

/-- The call of `name`, whose code is `callee`, then the check of the `n`
bytes it wrote to `out`. -/
def exchange (name : String) (callee : Prog isa) (n : Nat) : Prog isa :=
  .seq (.block [.mflr .r0])
    (.seq (.frame (.push .r0)
      (.seq (.block save) (.seq (.call name callee) (.seq (.block restore) (.block (check n)))))
      (.pop .r0))
    (.block [.mtlr .r0]))

end VG.Impl.Xdh.PPC64LE
