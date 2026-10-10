import VerifiedGarbage.Impl.Blake2.Arm.Stream
import VerifiedGarbage.Impl.Blake2.Arm.CompressB

/-!
# Argon2 H′ on ARMv7

`vg_argon2_hprime(input = r0, input_len = r1, out = r2, out_len = r3,
scratch = [sp])`. Every hash is computed by the ARMv7 BLAKE2b streaming
functions (`vg_blake2b_init`, `_update_scratch`, `_finalize_scratch`), each called with its
stack arguments pushed in a frame of their own (`update`: `push {r9, r10,
r12, lr}`, the data, its length and the functions' scratch, and a word that
keeps the stack pointer 8-byte aligned; `finalize`: `push {r9, r12}`, the
digest's address and the functions' scratch).

`r4` holds `scratch` throughout; its first bytes are laid out as:
* `[0, 192)`: the BLAKE2b state;
* `[192, 768)`: the BLAKE2b functions' scratch;
* `[768, 832)`: the digest;
* `[832, 836)`: the length prefix LE32(`out_len`);
* `[840, 876)`: the caller's `r4`–`r11` and our return address.
`r5` and `r6` hold the input and its length, `r7` where the next output byte
goes and `r8` how many are left. The streaming functions preserve `r4`–`r11`;
H′'s macros (`init`, `update`, `finalize`) write only `r0`–`r3`, `r9`, `r10`,
`r12` and `lr`, so a caller may keep `r5`–`r8` and `r11` across them.
The rest of `scratch` is not used. Only `sp`, the pointers and the lengths
affect branches and addresses.
-/

namespace VG.Impl.Argon2.Arm.HPrime

open VG.Arm

/-- Where the caller's registers are saved. -/
def saved : List (Reg × Nat) :=
  [(.r5, 844), (.r6, 848), (.r7, 852), (.r8, 856), (.r9, 860), (.r10, 864), (.r11, 868), (.lr, 872)]

/-- The base register, saved (and restored) last. -/
def baseSlot : Nat := 840

/-- Where the length prefix is. -/
def pfxOff : Nat := 832

def initName : String := "vg_blake2b_init"
def updateName : String := "vg_blake2b_update_scratch"
def finalizeName : String := "vg_blake2b_finalize_scratch"

def initCode : Prog isa := Impl.Blake2.Arm.Stream.init Spec.Blake2.b
def updateCode : Prog isa :=
  Impl.Blake2.Arm.Stream.update (w := 64) "vg_blake2b_compress" Impl.Blake2.Arm.B.compress
def finalizeCode : Prog isa :=
  Impl.Blake2.Arm.Stream.finalize (w := 64) "vg_blake2b_compress" Impl.Blake2.Arm.B.compress

/-- Save the caller's registers in `scratch`, point `r4` to it, keep the
input, the output pointer and length in `r5`–`r8`, and the length prefix in
`scratch`. -/
def setup : List Instr :=
  ([.ldrSp .r12 0] : List Instr) ++ ((Reg.r4, baseSlot) :: saved).map (fun p => .str p.1 .r12 p.2) ++
  ([.mov .r4 (.reg .r12), .mov .r5 (.reg .r0), .mov .r6 (.reg .r1), .mov .r7 (.reg .r2),
    .mov .r8 (.reg .r3), .str .r3 .r4 pfxOff] : List Instr)

/-- Restore the caller's registers, `r4` last. -/
def restore : List Instr := (saved ++ [(Reg.r4, baseSlot)]).map fun p => .ldr p.1 .r4 p.2

/-- `init(r4, r1, r4, 0)`: an unkeyed hash with the digest length in `r1`. -/
def init : Prog isa :=
  .seq (.block [.mov .r0 (.reg .r4), .mov .r2 (.reg .r4), .mov .r3 (.imm 0)]) (.call initName initCode)

/-- `update(r4, r3:r2, r9, r10, r4 + 192)`: the byte count in `r2` (low) and
`r3` (high), the data at `r9`, its length in `r10`. -/
def update : Prog isa :=
  .seq (.block [.mov .r0 (.reg .r4), .dp .add .r12 .r4 (.imm 192)])
    (.frame (.push [.r9, .r10, .r12, .lr]) (.call updateName updateCode) (.pop .r0 16))

/-- `finalize(r4, r3:r2, r4 + 768, r4 + 192)`: the byte count in `r2` (low)
and `r3` (high); the digest goes to `scratch[768, 832)`. -/
def finalize : Prog isa :=
  .seq (.block [.mov .r0 (.reg .r4), .dp .add .r1 .r4 (.imm 768), .dp .add .r12 .r4 (.imm 192)])
    (.frame (.push [.r1, .r12]) (.call finalizeName finalizeCode) (.pop .r0 8))

/-- Absorb `size` bytes of `scratch` at `offset` into an empty hash state. -/
def absorbFixed (offset size : Nat) : Prog isa :=
  .seq (.block [.mov .r2 (.imm 0), .mov .r3 (.imm 0), .dp .add .r9 .r4 (.imm (BitVec.ofNat 32 offset)),
      .mov .r10 (.imm (BitVec.ofNat 32 size))])
    update

/-- The first digest has `min(out_len, 64)` bytes, in `r1`: `out_len` (in
`r8`) if `(out_len - 1) / 64 = 0`. -/
def chooseLength : Prog isa :=
  .seq (.block [.dp .sub .r1 .r8 (.imm 1), .mov .r1 (.shifted .r1 .lsr 6), .cmp .r1 (.imm 0)])
    (.ite .eq (.block [.mov .r1 (.reg .r8)]) (.block [.mov .r1 (.imm 64)]))

/-- Absorb the caller's input after the four-byte length prefix. -/
def absorbInput : Prog isa :=
  .seq (.block [.mov .r2 (.imm 4), .mov .r3 (.imm 0), .mov .r9 (.reg .r5), .mov .r10 (.reg .r6)]) update

/-- Finish the hash of the prefix and the input: `4 + input_len` bytes, a
64-bit count. -/
def finishInput : Prog isa :=
  .seq (.block [.mov .r3 (.imm 0), .adds .r2 .r6 (.imm 4), .adc .r3 .r3 (.imm 0)]) finalize

/-- H(min(out_len, 64), LE32(out_len) || input). -/
def first : Prog isa :=
  .seq chooseLength (.seq init (.seq (absorbFixed pfxOff 4) (.seq absorbInput finishInput)))

/-- Hash the 64-byte digest, with the new digest length in `r1`. -/
def next : Prog isa :=
  .seq init (.seq (absorbFixed 768 64) (.seq (.block [.mov .r2 (.imm 64), .mov .r3 (.imm 0)]) finalize))

/-- The loop copying `r10 ≥ 1` digest bytes (from `r9`) to the output (at `r7`). -/
def copyLoop : Prog isa :=
  .loop (.block [.ldrb .r12 .r9 0, .strb .r12 .r7 0, .dp .add .r9 .r9 (.imm 1), .dp .add .r7 .r7 (.imm 1),
    .subs .r10 .r10 (.imm 1)]) .ne

/-- Copy `r10 > 0` digest bytes to the output, advancing the output pointer. -/
def copy : Prog isa := .seq (.block [.dp .add .r9 .r4 (.imm 768)]) copyLoop

/-- Emit one 32-byte prefix, and take it off the bytes left. -/
def emitPrefix : Prog isa :=
  .seq (.block [.mov .r10 (.imm 32)]) (.seq copy (.block [.dp .sub .r8 .r8 (.imm 32)]))

/-- Z if at most 64 bytes are left (`(left - 1) / 64 = 0`; `left ≥ 1`). -/
def cmpLeft : List Instr := [.dp .sub .r0 .r8 (.imm 1), .mov .r0 (.shifted .r0 .lsr 6), .cmp .r0 (.imm 0)]

/-- Emit further prefixes while more than 64 output bytes are left. -/
def chain : Prog isa :=
  .loop (.seq (.block [.mov .r1 (.imm 64)]) (.seq next (.seq emitPrefix (.block cmpLeft)))) .ne

/-- The prefixes of a long output and the digest after them. -/
def extendDigest : Prog isa :=
  .seq emitPrefix
  (.seq (.block cmpLeft)
  (.seq (.ite .eq (.block []) chain)
  (.seq (.block [.mov .r1 (.reg .r8)]) next)))

def copyRemaining : Prog isa := .seq (.block [.mov .r10 (.reg .r8)]) copy

/-- Emit H′ from its first digest, extending it for outputs over 64 bytes. -/
def finishOutput : Prog isa :=
  .seq (.block cmpLeft) (.seq (.ite .eq (.block []) extendDigest) copyRemaining)

/-- H′, including the short-output case and the final 33–64-byte hash. -/
def code : Prog isa :=
  .seq (.block setup) (.seq first (.seq finishOutput (.block restore)))

end VG.Impl.Argon2.Arm.HPrime
