import VerifiedGarbage.Spec.Sha256
import VerifiedGarbage.TCB.AArch64.Isa

/-!
# SHA-256 compression with the AArch64 SHA-2 instructions

`vg_sha256_compress_sha2(state = x0, blocks = x1, count = x2, scratch = x3)`.
The working state stays in `v0` and `v1`, four words per register, loaded
before the first block and kept there between blocks. `v4`–`v7` hold the
sixteen-word schedule window. SHA256SU0/SHA256SU1 expand four words at a time;
SHA256H/SHA256H2 perform their four rounds. For the feed-forward, the block's
original state is reloaded from `state` (stored after every block) into `v2`
and `v3`.

The sixteen round-constant vectors are built through `w4` into `v16`–`v31`
by the first block, each just before its group of rounds, as each block
used to build them; later blocks only read them. Only caller-saved registers
are used, and scratch is unused. The count and block pointer control the
only branches; message words never affect addresses or branches.
-/

namespace VG.Impl.Sha256.AArch64.Sha2

open VG.AArch64
open VG.Spec.Sha256 (K)

/-- The register holding schedule words `4i` through `4i+3`. -/
def msg (i : Nat) : VReg := [.v4, .v5, .v6, .v7].getD (i % 4) .v4

/-- The register holding the constants of rounds `4i` through `4i+3`. -/
def kreg (i : Nat) : VReg :=
  [.v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23,
   .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31].getD i .v16

/-- Materialize one word of a round-constant vector. The first word uses DUP;
later words replace lanes. -/
def constant (i j : Nat) : List Instr :=
  [.movz .w .x4 ((K (4 * i + j)).extractLsb' 0 16) 0,
   .movk .w .x4 ((K (4 * i + j)).extractLsb' 16 16) 1,
   .vop (if j = 0 then .dup .s4 (kreg i) .x4 else .ins .s4 (kreg i) j .x4)]

/-- Build the constants of rounds `4i` through `4i+3` in `kreg i`. -/
def kbuild (i : Nat) : List Instr := (List.range 4).flatMap (constant i)

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
  | 0 => .block []
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

def compress : Prog isa :=
  .ite (.zero .x .x2) (.block [])
    (.seq (.block load) (.seq (oneBlock true)
      (.ite (.zero .x .x2) (.block []) (.loop (oneBlock false) (.nonzero .x .x2)))))

end VG.Impl.Sha256.AArch64.Sha2
