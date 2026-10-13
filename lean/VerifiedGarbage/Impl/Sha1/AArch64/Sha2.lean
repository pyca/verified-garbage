module

public import VerifiedGarbage.Spec.Sha1
public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# SHA-1 compression with AArch64 SHA instructions

ABCD lives in v0 and E in the low word of v1, loaded before the first block
and kept there between blocks (the state is still stored after every block).
v4–v7 hold the rolling sixteen-word schedule. The four round constants, each
in all four lanes, are built once before the first block, in v18–v21. Each
group executes four rounds with SHA1C/P/M, using SHA1H to retain the next E
before overwriting ABCD. Only caller-saved registers are used. Scratch is
unused; all addresses and branches are public.
-/

@[expose] public section

namespace VG.Impl.Sha1.AArch64.Sha2

open VG.AArch64
open VG.Spec.Sha1 (K)

def msg (i : Nat) : VReg := [.v4, .v5, .v6, .v7].getD (i % 4) .v4

def op (i : Nat) : Sha1Op :=
  if i < 5 then .c else if i < 10 then .p else if i < 15 then .m else .p

def schedule (i : Nat) : List Instr :=
  if i < 4 then
    [.ldrq (msg i) .x1 (16 * i), .vop (.rev .rev32b (msg i) (msg i))]
  else
    [.vop (.sha1su0 (msg i) (msg (i + 1)) (msg (i + 2))),
     .vop (.sha1su1 (msg i) (msg (i + 3)))]

/-- The register holding the constant of rounds `20 j … 20 j + 19` in each lane. -/
def kreg (j : Nat) : VReg := [.v18, .v19, .v20, .v21].getD j .v18

/-- Build the constant of rounds `20 j …` in `kreg j`. -/
def kload (j : Nat) : List Instr :=
  [.movz .w .x4 ((K (20 * j)).extractLsb' 0 16) 0,
   .movk .w .x4 ((K (20 * j)).extractLsb' 16 16) 1,
   .vop (.dup .s4 (kreg j) .x4)]

def rounds4 (i : Nat) : List Instr :=
  [.vop (.add .s4 .v3 (kreg (i / 5)) (msg i)),
   .vop (.sha1h .v2 .v0),
   .vop (.sha1 (op i) .v0 .v1 .v3),
   .vop (.mov .v1 .v2)]

def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block (schedule n ++ rounds4 n))

/-- The four constants. -/
def kloads : List Instr := kload 0 ++ kload 1 ++ kload 2 ++ kload 3

/-- The state. -/
def load : List Instr :=
  [.ldrq .v0 .x0 0, .ldr .w .x4 .x0 16,
   .vop (.dup .s4 .v1 .x4), .vop (.dupS .v1 .v1 0)]

/-- Before the first block: the constants, and the state. -/
def setup : List Instr := kloads ++ load

/-- At the start of a block: keep the state to add it back at the end. -/
def save : List Instr := [.vop (.mov .v16 .v0), .vop (.mov .v17 .v1)]

def store : List Instr :=
  [.vop (.add .s4 .v0 .v0 .v16), .vop (.add .s4 .v1 .v1 .v17),
   .strq .v0 .x0 0, .umov .w .x4 .v1 0, .str .w .x4 .x0 16,
   .addImm .x .x1 .x1 64, .subImm .x .x2 .x2 1]

def body : Prog isa := .seq (.block save) (.seq (rounds 20) (.block store))

def compress : Prog isa :=
  .ite (.zero .x .x2) (.block []) (.seq (.block setup) (.loop body (.nonzero .x .x2)))

end VG.Impl.Sha1.AArch64.Sha2
