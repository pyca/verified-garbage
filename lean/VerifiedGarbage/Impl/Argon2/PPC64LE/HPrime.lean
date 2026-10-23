module

public import VerifiedGarbage.Impl.Blake2.PPC64LE.Stream

/-!
# Argon2 H′ on PPC64LE

`vg_argon2_hprime(input = r3, input_len = r4, out = r5, out_len = r6,
scratch = r7)`: the AArch64 implementation (`Impl/Argon2/AArch64/HPrime.lean`)
with its registers renamed, calling the PPC64LE BLAKE2b streaming functions
(`vg_blake2b_init`, `_update_scratch`, `_finalize_scratch`). The caller's 16
KiB scratch holds the 192-byte hash state at offset 0, 576 bytes of BLAKE2b
scratch at 192, the digest at 768, the four-byte length prefix at 832, and the
saved `r27`–`r31` and return address at 840–895. `r27` and `r28` hold the
input and its length, `r29` where the next output byte goes, `r30` how many
are left, and `r31` `scratch`; the streaming functions preserve them. The
return address, which each call replaces, is saved in `scratch` (through
`r0`), so H′ needs no stack frame of its own. Only the pointers and the
lengths affect branches and addresses.
-/

@[expose] public section

namespace VG.Impl.Argon2.PPC64LE.HPrime

open VG.PPC64LE

/-- `mr d, n` (as `addi d, n, 0`; `n` is not `r0`). -/
def mov (d n : Reg) : Instr := .addi d n 0

def initName : String := "vg_blake2b_init"
def updateName : String := "vg_blake2b_update_scratch"
def finalizeName : String := "vg_blake2b_finalize_scratch"

def initCode : Prog isa := Impl.Blake2.PPC64LE.Stream.init Spec.Blake2.b
def updateCode : Prog isa := Impl.Blake2.PPC64LE.Stream.update Spec.Blake2.b
def finalizeCode : Prog isa := Impl.Blake2.PPC64LE.Stream.finalize Spec.Blake2.b

/-- The nonvolatile registers we use, and where they are saved. -/
def saved : List (Reg × Nat) :=
  [(.r27, 840), (.r28, 848), (.r29, 856), (.r30, 864), (.r31, 872)]

/-- Save the caller's registers and return address in `scratch`, and keep the
arguments in `r27`–`r31` and the length prefix in `scratch`. -/
def setup : List Instr :=
  saved.map (fun (r, d) => .store .d r .r7 d) ++
    ([.mflr .r0, .store .d .r0 .r7 880, mov .r31 .r7, mov .r27 .r3, mov .r28 .r4, mov .r29 .r5,
      mov .r30 .r6, .store .w .r6 .r31 832] : List Instr)

/-- Restore the return address and the caller's registers, `r31` last. -/
def restore : List Instr :=
  [.load .d .r0 .r31 880, .mtlr .r0, .load .d .r27 .r31 840, .load .d .r28 .r31 848,
    .load .d .r29 .r31 856, .load .d .r30 .r31 864, .load .d .r31 .r31 872]

/-- Point the empty key into the workspace, keeping the digest length. -/
def initArgs : List Instr := [mov .r3 .r31, .addi .r5 .r31 832, .li .r6 0]

/-- Initialize an unkeyed hash with the digest length in `r4`. -/
def init : Prog isa := .seq (.block initArgs) (.call initName initCode)

/-- The hash state and the streaming functions' scratch. -/
def updateArgs : List Instr := [mov .r3 .r31, .addi .r7 .r31 192]

/-- Update from `r5`, `r6` with the byte count in `r4`. -/
def update : Prog isa := .seq (.block updateArgs) (.call updateName updateCode)

/-- The hash state, the digest and the streaming functions' scratch. -/
def finalizeArgs : List Instr := [mov .r3 .r31, .addi .r5 .r31 768, .addi .r6 .r31 192]

/-- Finalize the hash with the byte count in `r4`. -/
def finalize : Prog isa := .seq (.block finalizeArgs) (.call finalizeName finalizeCode)

/-- A fixed workspace buffer, with a fresh byte count. -/
def fixedArgs (offset size : Nat) : List Instr := [.li .r4 0, .addi .r5 .r31 offset, .li .r6 size]

/-- Absorb `size` bytes of `scratch` at `offset` into an empty hash state. -/
def absorbFixed (offset size : Nat) : Prog isa := .seq (.block (fixedArgs offset size)) update

/-- The first digest has `min(out_len, 64)` bytes, in `r4`. -/
def chooseLength : Prog isa :=
  .seq (.block [mov .r4 .r30, .subi .r10 .r4 65, .lsr .d .r10 .r10 63])
    (.ite (.nonzero .d .r10) (.block []) (.block [.li .r4 64]))

/-- Absorb the caller's input after the four-byte length prefix. -/
def inputArgs : List Instr := [.li .r4 4, mov .r5 .r27, mov .r6 .r28]

def absorbInput : Prog isa := .seq (.block inputArgs) update

/-- Finish the hash after the four-byte prefix and the caller's input. -/
def finishInput : Prog isa :=
  .seq (.block [.addi .r4 .r28 4]) finalize

/-- H(min(out_len, 64), LE32(out_len) || input). -/
def first : Prog isa :=
  .seq chooseLength (.seq init (.seq (absorbFixed 832 4) (.seq absorbInput finishInput)))

/-- Hash the 64-byte previous digest, with the new digest length in `r4`. -/
def next : Prog isa :=
  .seq init (.seq (absorbFixed 768 64) (.seq (.block [.li .r4 64]) finalize))

/-- Copy one byte and advance the source, destination and countdown. -/
def copyByte : List Instr :=
  [.lbz .r6 .r5 0, .stb .r6 .r29 0, .addi .r5 .r5 1, .addi .r29 .r29 1, .subi .r9 .r9 1]

/-- Copy `r9 > 0` digest bytes to `r29`, advancing that output pointer. -/
def copy : Prog isa :=
  .seq (.block [.addi .r5 .r31 768]) (.loop (.block copyByte) (.nonzero .d .r9))

/-- Emit one 32-byte prefix and reduce the remaining output length. -/
def emitPrefix : Prog isa :=
  .seq (.block [.li .r9 32]) (.seq copy (.block [.subi .r30 .r30 32]))

/-- `r10 = 0` exactly when more than 64 output bytes are left. -/
def cmpLeft : List Instr := [.subi .r10 .r30 65, .lsr .d .r10 .r10 63]

/-- Emit further prefixes while more than 64 output bytes remain. -/
def chain : Prog isa :=
  .loop (.seq (.block [.li .r4 64]) (.seq next (.seq emitPrefix (.block cmpLeft)))) (.zero .d .r10)

/-- Produce the final digest after the 32-byte prefixes of a long output. -/
def extendDigest : Prog isa :=
  .seq emitPrefix
  (.seq (.block cmpLeft)
  (.seq (.ite (.nonzero .d .r10) (.block []) chain)
  (.seq (.block [mov .r4 .r30]) next)))

def copyRemaining : Prog isa := .seq (.block [mov .r9 .r30]) copy

/-- Emit H′ from its first digest, extending it for outputs over 64 bytes. -/
def finishOutput : Prog isa :=
  .seq (.block cmpLeft) (.seq (.ite (.nonzero .d .r10) (.block []) extendDigest) copyRemaining)

/-- H′, including the short-output case and the final 33–64-byte hash. -/
def code : Prog isa :=
  .seq (.block setup) (.seq first (.seq finishOutput (.block restore)))

end VG.Impl.Argon2.PPC64LE.HPrime
