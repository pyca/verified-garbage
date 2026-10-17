module

public import VerifiedGarbage.Spec.Sha256
public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# SHA-256 compression with the AArch64 SHA-2 instructions

`vg_sha256_compress_sha2(state = x0, blocks = x1, count = x2, scratch = x3)`.
The working state stays in `v0` and `v1`, four words per register, loaded
before the first block and kept there between blocks. `v4`–`v7` hold the
sixteen-word schedule window. SHA256SU0/SHA256SU1 expand four words at a time;
SHA256H/SHA256H2 perform their four rounds. For the feed-forward, the block's
original state is reloaded from `state` (stored after every block) into `v2`
and `v3`.

The sixteen round-constant vectors are loaded into `v16`–`v31` by the first
block, each two groups ahead of its rounds; later blocks only read them.
The first block puts the address of the table of constants `VG_SHA256_K`
(`adrSym`) in `x4`, and loads each group's four constants from it with one
`ldr q` (`ldrqTbl`, which carries the table: the emitter writes it as a
`static`, and no contract mentions it). Building them in general registers
(`movz`/`movk`) instead took eight instructions and two stores a group, and
moving them into vector registers directly (`dup`, `ins`) took twelve, four
of them general-to-vector transfers, which are slow on some cores (Neoverse
N2; see `Sha512/AArch64/Sha3.lean`). Only caller-saved registers are used,
and no scratch. The count and block pointer control the only branches;
message words never affect addresses or branches.
-/

@[expose] public section

namespace VG.Impl.Sha256.AArch64.Sha2

open VG.AArch64
open VG.Spec.Sha256 (K)

/-- The register holding schedule words `4i` through `4i+3`. -/
def msg (i : Nat) : VReg := [.v4, .v5, .v6, .v7].getD (i % 4) .v4

/-- The register holding the constants of rounds `4i` through `4i+3`. -/
def kreg (i : Nat) : VReg :=
  [.v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23,
   .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31].getD i .v16

/-- The constants of group `k` as two 64-bit words, lane order: `K₄ₖ₊₁ K₄ₖ`
and `K₄ₖ₊₃ K₄ₖ₊₂`. -/
def kWord (k j : Nat) : BitVec 64 := K (4 * k + 2 * j + 1) ++ K (4 * k + 2 * j)

/-- The name of the table of round constants. -/
def kName : String := "VG_SHA256_K"

/-- The table of round constants: group `k`'s as two words, `kWord k 0` and
`kWord k 1`, at bytes `16 k` to `16 k + 15`. -/
def kTable : List (BitVec 64) := (List.range 32).map fun j => kWord (j / 2) (j % 2)

/-- Load group `i`'s constants from the table, whose address is in `x4`. -/
def kld (i : Nat) : Instr := .ldrqTbl (kreg i) .x4 (16 * i) kName kTable

/-- In the first block, in group `i`: load the constants of group `i + 2`, if
any, two groups ahead of their rounds, so that the load is not on the chain of
SHA256H and SHA256H2 that it feeds. -/
def kbuild (i : Nat) : List Instr := if i + 2 < 16 then [kld (i + 2)] else []

/-- Load the first sixteen words, then expand the schedule in registers. -/
def schedule (i : Nat) : List Instr :=
  if i < 4 then
    [.ldrq (msg i) .x1 (16 * i), .vop (.rev .rev32b (msg i) (msg i))]
  else
    [.vop (.sha256su0 (msg i) (msg (i + 1))),
     .vop (.sha256su1 (msg i) (msg (i + 2)) (msg (i + 3)))]

/-- Four rounds, retaining the old ABCD for SHA256H2. -/
def rounds4 (i : Nat) : List Instr :=
  [.vop (.add .s4 .v3 (kreg i) (msg i)),
   .vop (.mov .v2 .v0),
   .vop (.sha256h .v0 .v1 .v3),
   .vop (.sha256h2 .v1 .v2 .v3)]

/-- Group `n`: its schedule, its constants if `c` (the first block), and its rounds. -/
def group (c : Bool) (n : Nat) : List Instr :=
  schedule n ++ ((if c then kbuild n else []) ++ rounds4 n)

def rounds (c : Bool) : Nat → Prog isa
  | 0 => .block (if c then [.adrSym .x4 kName, kld 0, kld 1] else [])
  | n + 1 => .seq (rounds c n) (.block (group c n))

def load : List Instr := [.ldrq .v0 .x0 0, .ldrq .v1 .x0 16]

/-- Add the block's original state (reloaded from `state`) and store the result. -/
def store : List Instr :=
  [.ldrq .v2 .x0 0, .ldrq .v3 .x0 16,
   .vop (.add .s4 .v0 .v0 .v2), .vop (.add .s4 .v1 .v1 .v3),
   .strq .v0 .x0 0, .strq .v1 .x0 16,
   .addImm .x .x1 .x1 64, .subImm .x .x2 .x2 1]

/-- One block, building the constants if `c`. -/
def oneBlock (c : Bool) : Prog isa := .seq (rounds c 16) (.block store)

/-- The alignment of the loop over the later blocks: its head at a multiple
of `2 ^ loopAlign` bytes, wherever the first block leaves it. -/
def loopAlign : Nat := 6

def compress : Prog isa :=
  .ite (.zero .x .x2) (.block [])
    (.seq (.block load) (.seq (oneBlock true)
      (.ite (.zero .x .x2) (.block [])
        (.seq (.block [.align loopAlign]) (.loop (oneBlock false) (.nonzero .x .x2))))))

end VG.Impl.Sha256.AArch64.Sha2
