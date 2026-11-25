module

public import VerifiedGarbage.Impl.Sha3.AArch64.Neon.X2
public import VerifiedGarbage.Impl.AArch64Weave

/-!
# Keccak-f[1600] on three states

`vg_keccak_f1600_x3(states = x0, state = x1, scratch = x2)`: on the two
interleaved at `states`, and on the one at `state`. Without FEAT_SHA3, one
after another in general registers.

With it, the two in vector registers (as `Neon/X2.lean`) and the third in
general registers, whose rounds then run on units the first two leave idle.
They do ρ's rotations (`Conf.lazy := false`) rather than leave them pending:
it is more instructions, but vector code sets the pace, and some cores run
XORs of rotated operands at half the rate. The instructions of two vector
rounds and of two general rounds are interleaved (`AArch64Weave.weave`); the
loop's 12 iterations do 24 of each.

`x30` points to a window of the memory of the two states, which are in
registers: 24 bytes for the lanes the general rounds spill, and, 32 bytes on,
the iteration's two round constants. It advances by 16 bytes: the table ends
224 bytes in. The frame holds the callee-saved registers, the pointers and the
count of iterations.
-/

@[expose] public section

namespace VG.Impl.Sha3.AArch64.Hybrid.X3

open VG.AArch64
open VG.Impl.AArch64Schedule (schedule)
open VG.Impl.AArch64Weave (weave)
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Impl.Sha3.AArch64.RoundConstants (rcs sym)
open VG.Impl.Sha3.AArch64.Scalar (Conf lreg savedReg)

/-- ι of vector round `r` of the loop's body. -/
def vecIota (r : Nat) : List Instr :=
  [.ldrq .v31 .x30 32, .vop (.perm (if r = 0 then .trn1 else .trn2) .d2 .v31 .v31 .v31), .vop (.logic .eor .v0 .v0 .v31)]

/-- Two vector rounds, in the order written. -/
def vecPlain : List Instr := Sha3.Vector.round 0 0 0 ++ vecIota 0 ++ Sha3.Vector.round 0 0 1 ++ vecIota 1

/-- The order their instructions run in. -/
def order : List Nat := []

def vecBody : List Instr := schedule order vecPlain

/-- The general rounds: lanes spilled to memory at `x30`. -/
def conf : Conf where
  temps := [.x28, .x16, .x17]
  lazy := false
  sp := ⟨fun k r => .str .x r .x30 (8 * k), fun k r => .ldr .x r .x30 (8 * k)⟩

/-- ι of general round `r` of the loop's body. -/
def genIota (r : Nat) : List Instr := [.ldr .x .x16 .x30 (32 + 8 * r), .logic .eor .x .x0 .x0 .x16]

/-- Two general rounds. -/
def genBody : List Instr := conf.round 0 ++ genIota 0 ++ conf.round 1 ++ genIota 1

/-- Two rounds of all three states. -/
def rounds : List Instr := weave vecBody genBody

def frameBytes : Nat := 128

/-- The frame: the callee-saved registers, then the pointers, then the count. -/
def saveG : List Instr := (List.range 11).map fun i => .strSp (savedReg i) (8 * i)
def restoreG : List Instr := (List.range 11).map fun i => .ldrSp (savedReg i) (8 * i)
def ptrs : List Instr := [.strSp .x0 88, .strSp .x1 96, .strSp .x2 104]

/-- The table of round constants, 32 bytes into the window's memory. -/
def rcStore : List Instr :=
  ([.adrSym .x16 sym] : List Instr) ++
  (List.range 12).flatMap fun k => [.ldrqTbl .v31 .x16 (16 * k) sym rcs, .strq .v31 .x0 (32 + 16 * k)]

/-- Load the third state: lane 1's register is its pointer's, so it is last. -/
def loadThird : List Instr :=
  ((List.range 25).filter (· != 1)).map (fun i => .ldr .x (lreg i) .x1 (8 * i)) ++ ([.ldr .x .x1 .x1 8] : List Instr)

def storeThird : List Instr :=
  ([.ldrSp .x16 96] : List Instr) ++ (List.range 25).map fun i => .str .x (lreg i) .x16 (8 * i)

/-- What follows the rounds in an iteration. -/
def next : List Instr :=
  [.addImm .x .x30 .x30 16, .ldrSp .x16 112, .subImm .x .x16 .x16 1, .strSp .x16 112]

def enter : List Instr :=
  Sha3.Vector.save .x2 0 ++ saveG ++ ptrs ++ Neon.Pair.load .x0 ++ rcStore ++
  ([.movz .x .x16 12 0, .strSp .x16 112, .addImm .x .x30 .x0 0] : List Instr) ++ loadThird

def leave : List Instr :=
  storeThird ++ ([.ldrSp .x0 88] : List Instr) ++ Neon.Pair.store .x0 ++
  ([.ldrSp .x2 104] : List Instr) ++ Sha3.Vector.restore .x2 0 ++ restoreG

def vector : Prog isa :=
  .frame (.alloc frameBytes)
    (.seq (.block enter) (.seq (.loop (.seq (.block rounds) (.block next)) (.nonzero .x .x16)) (.block leave)))
    (.free frameBytes)

open VG.Impl.Sha3.AArch64.Scalar (save restore load store callCore)

/-- One state after another: `v29`, `v30` and `v31` hold `states`, `scratch` and `state`. -/
def scalar : Prog isa :=
  .seq (.block (save ++ [.vop (.dup .d2 .v29 .x0), .vop (.dup .d2 .v30 .x2), .vop (.dup .d2 .v31 .x1),
    .umov .x .x16 .v29 0] ++ load .x16 16 0 ++ ([.umov .x .x28 .v30 0] : List Instr)))
  (.seq callCore
  (.seq (.block (([.umov .x .x16 .v29 0] : List Instr) ++ store .x16 16 0 ++ load .x16 16 8 ++
    ([.umov .x .x28 .v30 0] : List Instr)))
  (.seq callCore
  (.seq (.block (([.umov .x .x16 .v29 0] : List Instr) ++ store .x16 16 8 ++ ([.umov .x .x16 .v31 0] : List Instr) ++
    load .x16 8 0 ++ ([.umov .x .x28 .v30 0] : List Instr)))
  (.seq callCore (.block (([.umov .x .x16 .v31 0] : List Instr) ++ store .x16 8 0 ++ restore)))))))

def code (sha3 : Bool) : Prog isa := if sha3 then vector else scalar

def name (sha3 : Bool) : String := if sha3 then "vg_keccak_f1600_x3_sha3" else "vg_keccak_f1600_x3"

end VG.Impl.Sha3.AArch64.Hybrid.X3
