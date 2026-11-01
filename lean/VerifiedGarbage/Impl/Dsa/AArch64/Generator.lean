module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.SeedSearch
public import VerifiedGarbage.Impl.Dsa.HelperLayout

/-! # DSA's generator search and domain check as a function of its own (AArch64)

`vg_dsa_generator_{bits}` runs the last stage of a parameter-generation
attempt, once p and q are found: the generator search over the h tape, then
packing p ‖ q ‖ g and the domain check (`generatorSearch`, then
`finishDomain`), so that every hash backend's generator calls one copy of
it. Its working space is the generation's scratch space: p, q, the exponent,
the arithmetic workspace and the packed domain sit at the offsets
`Generation.Layout` gives them.

Its 272-byte frame holds the generation's frame words: the stage reads its
arguments (the working space, the h tape and its length, and the hash
workspace the frame's layout names) from the slots where the generation keeps
them, so that the stage is the generation's own code, and leaves its status
(1 for parameters, 3 to go on) in the generation's status slot. It saves the
callee-saved registers in the working space's control area, which the stage
does not use, so that a caller's stack holds no more than the frame. -/

@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generator
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Impl.Dsa.AArch64.Generation

/-- q's bytes for p's. -/
def qLen (pLen : Nat) : Nat := if pLen = 128 then 20 else 32

/-- The offset of the saved registers: the control area. -/
def spill : Nat := Generation.Layout.control

/-- The callee-saved registers and their slots. -/
def gprSlots : List (Reg × Nat) :=
  [(.x19, spill), (.x20, spill + 8), (.x21, spill + 16), (.x22, spill + 24), (.x23, spill + 32),
   (.x24, spill + 40), (.x25, spill + 48), (.x26, spill + 56), (.x27, spill + 64), (.x28, spill + 72),
   (.x30, spill + 80)]

/-- The callee-saved vector registers' low halves and their slots. -/
def vectorSlots : List (VReg × Nat) :=
  [(.v8, spill + 88), (.v9, spill + 96), (.v10, spill + 104), (.v11, spill + 112), (.v12, spill + 120),
   (.v13, spill + 128), (.v14, spill + 136), (.v15, spill + 144)]

/-- The saved registers' bytes. -/
def spillBytes : Nat := 152

/-- The ranges of the scratch space the stage writes: the DSA workspace the
exponentiation uses, g, the packed domain, the saved registers, the
arithmetic workspace and the domain check's workspace. -/
def scratch (pLen : Nat) : List (Nat × Nat) :=
  [(Generation.Layout.parent, Dsa.Layout.activeBytes), (Generation.Layout.g, pLen),
   (Generation.Layout.packed, 2 * pLen + qLen pLen), (spill, spillBytes),
   (Generation.Layout.arithmetic, Generation.Layout.arithmeticBytes),
   (Generation.Layout.domainCheck, Dsa.Layout.usedBytes)]

/-- Save the callee-saved registers at their slots of the working space. -/
def save : List Instr :=
  gprSlots.map (fun (r, d) => .str .x r .x0 d) ++
    vectorSlots.flatMap fun (v, d) => [.umov .x .x9 v 0, .str .x .x9 .x0 d]

/-- Restore them, from the working space in frame word 5. -/
def restore : List Instr :=
  [.ldrSp .x9 40] ++ vectorSlots.flatMap (fun (v, d) => [.ldr .x .x10 .x9 d, .vop (.ins .d2 v 0 .x10)]) ++
    gprSlots.map fun (r, d) => .ldr .x r .x9 d

/-- The stage's place in the generation's scratch space. -/
def layout (pLen : Nat) : Impl.Dsa.GeneratorStage.Layout where
  pLen := pLen
  qLen := qLen pLen
  p := Generation.Layout.p
  q := Generation.Layout.q
  exponent := Generation.Layout.exponent
  packed := Generation.Layout.packed
  scratch := scratch pLen
  size := Generation.Layout.usedBytes pLen

/-- The frame words the generation's search keeps that the stage does not
set from its arguments: zero, so that what the stage keeps does not depend
on the stack's contents. -/
def zeroSlots : List Nat := [1, 3, 4, 6, 7, 8, 9, 10, 14, 15, 16, 17, 18, 26]

/-- The arguments in the generation's frame slots: the working space (word
5), the h tape (word 11) and its length (word 13), and the hash workspace
(word 12); the other words the search keeps are zero. -/
def entry : List Instr :=
  [.strSp .x0 40, .strSp .x2 88, .strSp .x3 104, movi .x4 Generation.Layout.hash,
   .add .x .x4 .x0 .x4, .strSp .x4 96, movi .x4 0] ++ zeroSlots.map fun k => .strSp .x4 (8 * k)

/-- The generation's status, 1 or 3, returned as 1 or 0. -/
def exit : List Instr :=
  [.ldrSp .x3 152, movi .x0 3, .sub .x .x0 .x0 .x3, .lsr .x .x0 .x0 1]

/-- The stage the generation runs once p is accepted. -/
def stage (mul : Nat → Nat → Nat → Prog isa) (pLen : Nat) : Prog isa :=
  .seq (generatorSearch mul pLen) (onSuccess (finishDomain mul pLen (qLen pLen)))

def code (mul : Nat → Nat → Nat → Prog isa) (pLen : Nat) : Prog isa :=
  .frame (.alloc 272) (seqs [.block save, .block entry, stage mul pLen, .block exit, .block restore]) (.free 272)

end VG.Impl.Dsa.AArch64.Generator
