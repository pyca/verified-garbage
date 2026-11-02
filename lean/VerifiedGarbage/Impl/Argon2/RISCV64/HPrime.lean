module

public import VerifiedGarbage.Impl.Blake2.RISCV64.Stream

/-!
# Argon2 H′ on RISC-V

`vg_argon2_hprime(input = a0, input_len = a1, out = a2, out_len = a3,
scratch = a4)`: the PPC64LE implementation (`Impl/Argon2/PPC64LE/HPrime.lean`)
with its registers renamed, calling the RISC-V BLAKE2b streaming functions
(`vg_blake2b_init`, `_update_scratch`, `_finalize_scratch`). Its caller's
scratch is 8-byte aligned (an array of `u64`), and holds the 192-byte hash state at offset 0, 576
bytes of BLAKE2b scratch at 192, the digest at 768, the four-byte length
prefix at 832, and the saved `s0`–`s4` and return address at 840–887. `s0`
and `s1` hold the input and its length, `s2` where the next output byte goes,
`s3` how many are left, and `s4` `scratch`; the streaming functions preserve
them. The return address, which each call replaces, is saved in `scratch`,
so H′ needs no stack frame of its own. The output is written a byte at a
time. Only the pointers and the lengths affect branches and addresses.
-/

@[expose] public section

namespace VG.Impl.Argon2.RISCV64.HPrime

open VG.RISCV64

/-- `mv d, n` (`addi d, n, 0`). -/
def mov (d n : Reg) : Instr := .addi d n 0

def initName : String := "vg_blake2b_init"
def updateName : String := "vg_blake2b_update_scratch"
def finalizeName : String := "vg_blake2b_finalize_scratch"

def initCode : Prog isa := Impl.Blake2.RISCV64.Stream.init Spec.Blake2.b
def updateCode : Prog isa := Impl.Blake2.RISCV64.Stream.updateScratch Spec.Blake2.b
def finalizeCode : Prog isa := Impl.Blake2.RISCV64.Stream.finalizeScratch Spec.Blake2.b

/-- The return address and the callee-saved registers we use, and where
they are saved: `s4`, the base of the restores, last. -/
def saved : List (Reg × Nat) :=
  [(.ra, 880), (.s0, 840), (.s1, 848), (.s2, 856), (.s3, 864), (.s4, 872)]

/-- Save the return address and the caller's registers in `scratch`, and
keep the arguments in `s0`–`s4` and the length prefix in `scratch`. -/
def setup : List Instr :=
  saved.map (fun (r, d) => .store .d r .a4 d) ++
    ([mov .s4 .a4, mov .s0 .a0, mov .s1 .a1, mov .s2 .a2, mov .s3 .a3, .store .w .a3 .s4 832] :
      List Instr)

/-- Restore the return address and the caller's registers, `s4` last. -/
def restore : List Instr := saved.map fun (r, d) => .load .d r .s4 d

/-- Point the empty key into the workspace, keeping the digest length. -/
def initArgs : List Instr := [mov .a0 .s4, .addi .a2 .s4 832, .li .a3 0]

/-- Initialize an unkeyed hash with the digest length in `a1`. -/
def init : Prog isa := .seq (.block initArgs) (.call initName initCode)

/-- The hash state and the streaming functions' scratch. -/
def updateArgs : List Instr := [mov .a0 .s4, .addi .a4 .s4 192]

/-- Update from `a2`, `a3` with the byte count in `a1`. -/
def update : Prog isa := .seq (.block updateArgs) (.call updateName updateCode)

/-- The hash state, the digest and the streaming functions' scratch. -/
def finalizeArgs : List Instr := [mov .a0 .s4, .addi .a2 .s4 768, .addi .a3 .s4 192]

/-- Finalize the hash with the byte count in `a1`. -/
def finalize : Prog isa := .seq (.block finalizeArgs) (.call finalizeName finalizeCode)

/-- A fixed workspace buffer, with a fresh byte count. -/
def fixedArgs (offset size : Nat) : List Instr := [.li .a1 0, .addi .a2 .s4 offset, .li .a3 size]

/-- Absorb `size` bytes of `scratch` at `offset` into an empty hash state. -/
def absorbFixed (offset size : Nat) : Prog isa := .seq (.block (fixedArgs offset size)) update

/-- The first digest has `min(out_len, 64)` bytes, in `a1`. -/
def chooseLength : Prog isa :=
  .seq (.block [mov .a1 .s3, .addi .a7 .a1 (-65), .shift .srl .d .a7 .a7 63])
    (.ite (.nonzero .a7) (.block []) (.block [.li .a1 64]))

/-- Absorb the caller's input after the four-byte length prefix. -/
def inputArgs : List Instr := [.li .a1 4, mov .a2 .s0, mov .a3 .s1]

def absorbInput : Prog isa := .seq (.block inputArgs) update

/-- Finish the hash after the four-byte prefix and the caller's input. -/
def finishInput : Prog isa :=
  .seq (.block [.addi .a1 .s1 4]) finalize

/-- H(min(out_len, 64), LE32(out_len) || input). -/
def first : Prog isa :=
  .seq chooseLength (.seq init (.seq (absorbFixed 832 4) (.seq absorbInput finishInput)))

/-- Hash the 64-byte previous digest, with the new digest length in `a1`. -/
def next : Prog isa :=
  .seq init (.seq (absorbFixed 768 64) (.seq (.block [.li .a1 64]) finalize))

/-- Copy one byte and advance the source, destination and countdown. -/
def copyByte : List Instr :=
  [.load .b .a3 .a2 0, .store .b .a3 .s2 0, .addi .a2 .a2 1, .addi .s2 .s2 1, .addi .a6 .a6 (-1)]

/-- Copy `a6 > 0` digest bytes to `s2`, advancing that output pointer. -/
def copy : Prog isa :=
  .seq (.block [.addi .a2 .s4 768]) (.loop (.block copyByte) (.nonzero .a6))

/-- Emit one 32-byte prefix and reduce the remaining output length. -/
def emitPrefix : Prog isa :=
  .seq (.block [.li .a6 32]) (.seq copy (.block [.addi .s3 .s3 (-32)]))

/-- `a7 = 0` exactly when more than 64 output bytes are left. -/
def cmpLeft : List Instr := [.addi .a7 .s3 (-65), .shift .srl .d .a7 .a7 63]

/-- Emit further prefixes while more than 64 output bytes remain. -/
def chain : Prog isa :=
  .loop (.seq (.block [.li .a1 64]) (.seq next (.seq emitPrefix (.block cmpLeft)))) (.zero .a7)

/-- Produce the final digest after the 32-byte prefixes of a long output. -/
def extendDigest : Prog isa :=
  .seq emitPrefix
  (.seq (.block cmpLeft)
  (.seq (.ite (.nonzero .a7) (.block []) chain)
  (.seq (.block [mov .a1 .s3]) next)))

def copyRemaining : Prog isa := .seq (.block [mov .a6 .s3]) copy

/-- Emit H′ from its first digest, extending it for outputs over 64 bytes. -/
def finishOutput : Prog isa :=
  .seq (.block cmpLeft) (.seq (.ite (.nonzero .a7) (.block []) extendDigest) copyRemaining)

/-- H′, including the short-output case and the final 33–64-byte hash. -/
def code : Prog isa :=
  .seq (.block setup) (.seq first (.seq finishOutput (.block restore)))

end VG.Impl.Argon2.RISCV64.HPrime
