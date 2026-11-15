module

public import VerifiedGarbage.Impl.Sm4.AArch64.Ecb

/-!
# SM4 ECB with the Armv8 SM4 instructions

`ecb dir (schedule = x0, data = x1, n = x2)`: `vg_sm4_ecb_encrypt_sm4` and
`vg_sm4_ecb_decrypt_sm4`, with the contracts of `vg_sm4_ecb_encrypt` and
`vg_sm4_ecb_decrypt` (`Spec/Sm4/Contract.lean`), for CPUs with FEAT_SM4.

`sm4e vd, vn` is four rounds on the state `vd` with the four round keys of
`vn`, the state's words and the round keys each in a 32-bit lane.

* The round keys stay in `v16`–`v23`, four to a register, in the order the
  rounds use them: the schedule's sixteen bytes at `16 i` in `v(16 + i)` for
  encryption; for decryption those at `16 (7 - i)`, with their four words
  reversed (`rev64 .4s` swaps the words of each half, `ext #8` the halves),
  so that the same rounds run with `rk₃₁ … rk₀` (§7.2).
* The blocks go eight at a time (`v0`–`v7`) while eight are left, then one
  at a time (`v0`): each is loaded, its words made big-endian (`rev32
  .16b`), run through the eight `sm4e` (each applied to every block of the
  group), its sixteen bytes reversed (`rev64 .16b`, then `ext #8`), which
  is the final reversal `R` of the words and their big-endian bytes, and
  stored back in place.

`x0` (the schedule), `x1` (the data), `x2` (the blocks left) and `x13` (the
groups of eight left) hold public values; every address and every branch
depends only on them. It uses no stack and writes no callee-saved register.
-/

@[expose] public section

namespace VG.Impl.Sm4.AArch64.Sm4e

open VG.AArch64
open VG.Impl.Sm4.AArch64 (Dir)

/-- The register of the round keys `4 r … 4 r + 3` of the rounds' order. -/
def kreg : Nat → VReg
  | 0 => .v16 | 1 => .v17 | 2 => .v18 | 3 => .v19 | 4 => .v20 | 5 => .v21 | 6 => .v22 | _ => .v23

/-- The registers of a group of eight blocks. -/
def regs8 : List VReg := [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7]

/-- Encryption's round keys. -/
def encKeys : List Instr := (List.range 8).flatMap fun i => [.ldrq (kreg i) .x0 (16 * i)]

/-- The four words of `k` in reverse order. -/
def revWords (k : VReg) : List Instr := [.vop (.rev .rev64s k k), .vop (.ext k k k 8)]

/-- Decryption's round keys: the schedule's in reverse order. -/
def decKeys : List Instr :=
  (List.range 8).flatMap fun i => .ldrq (kreg i) .x0 (16 * (7 - i)) :: revWords (kreg i)

/-- The round keys, and `x13 = n / 8`. -/
def setup (dir : Dir) : List Instr :=
  (match dir with | .encrypt => encKeys | .decrypt => decKeys) ++ ([.lsr .x .x13 .x2 3] : List Instr)

/-- Load the data blocks `x1 + 16 (j + i)` into the registers. -/
def ldData : List VReg → Nat → List Instr
  | [], _ => []
  | b :: bs, j => .ldrq b .x1 (16 * j) :: ldData bs (j + 1)

/-- Store the registers to the data blocks `x1 + 16 (j + i)`. -/
def stData : List VReg → Nat → List Instr
  | [], _ => []
  | b :: bs, j => .strq b .x1 (16 * j) :: stData bs (j + 1)

/-- The words of each block, from their big-endian bytes. -/
def toWords (regs : List VReg) : List Instr := regs.flatMap fun b => [.vop (.rev .rev32b b b)]

/-- Four rounds of each block, with the round keys in `k`. -/
def round4 (regs : List VReg) (k : VReg) : List Instr := regs.flatMap fun b => [.vop (.sm4e b k)]

/-- The 32 rounds of each block. -/
def rounds (regs : List VReg) : List Instr := (List.range 8).flatMap fun r => round4 regs (kreg r)

/-- The sixteen bytes of each block in reverse order. -/
def fromWords (regs : List VReg) : List Instr :=
  regs.flatMap fun b => [.vop (.rev .rev64b b b), .vop (.ext b b b 8)]

/-- SM4 of each block register. -/
def crypt (regs : List VReg) : List Instr := toWords regs ++ rounds regs ++ fromWords regs

/-- Eight blocks; `x13 = n / 8` for the blocks left. -/
def blk8 : Prog isa :=
  .block (ldData regs8 0 ++ crypt regs8 ++ stData regs8 0 ++
    ([.addImm .x .x1 .x1 128, .subImm .x .x2 .x2 8, .lsr .x .x13 .x2 3] : List Instr))

/-- One block. -/
def blk1 : Prog isa :=
  .block (ldData [.v0] 0 ++ crypt [.v0] ++ stData [.v0] 0 ++
    ([.addImm .x .x1 .x1 16, .subImm .x .x2 .x2 1] : List Instr))

/-- The whole function: the round keys, then the blocks, eight and then one
at a time. -/
def ecb (dir : Dir) : Prog isa :=
  .seq (.block (setup dir))
    (.seq (.ite (.zero .x .x13) (.block []) (.loop blk8 (.nonzero .x .x13)))
      (.ite (.zero .x .x2) (.block []) (.loop blk1 (.nonzero .x .x2))))

end VG.Impl.Sm4.AArch64.Sm4e
