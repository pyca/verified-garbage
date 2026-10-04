import VerifiedGarbage.Impl.Argon2.Arm.Layout
import VerifiedGarbage.Impl.Argon2.Arm.Divide

/-!
# Argon2 on ARMv7: the parameters and H₀

`r11` points to the derivation's locals (`Impl/Argon2/Arm/Layout.lean`).

* `parameters`: the segment length `⌊memory_cost / (4 · lanes)⌋`, by the
  fixed-time division, the lane length (four segments) and its size in
  bytes.
* `code`: H₀ (RFC 9106 §3.2), with H′'s macros (`Impl/Argon2/Arm/HPrime.lean`)
  and `r4` pointing to `scratch`: the six public parameters at
  `scratch + 768`, then LE32 of each input's length (at `scratch + 792`)
  and the input itself; the byte count (64 bits) is kept in the locals. The
  digest is copied to the first 64 bytes of the locals.
-/

namespace VG.Impl.Argon2.Arm.Derive

open VG.Arm

/-- `r := [r11, #d]` -/
def ld (r : Reg) (d : Nat) : Instr := .ldr r .r11 d

/-- `[r11, #d] := r` -/
def st (d : Nat) (r : Reg) : Instr := .str r .r11 d

/-! ## The parameters -/

def parameters : List Instr :=
  [ld .r0 (argOff lanesArg), .mov .r2 (.shifted .r0 .lsl 2), st divisorOff .r2,
    ld .r1 (argOff memoryCostArg)] ++
  Divide.code ++
  [st segLenOff .r1, .mov .r1 (.shifted .r1 .lsl 2), st laneLenOff .r1, .mov .r1 (.shifted .r1 .lsl 10),
    st strideOff .r1]

/-! ## H₀ -/

/-- The argument whose low 32 bits are word `j` of H₀'s header (but the
version, word 4): lanes, tag length, memory, passes, version, variant. -/
def headerArg (j : Nat) : Nat :=
  if j = 0 then lanesArg else if j = 1 then outLenArg else if j = 2 then memoryCostArg
  else if j = 3 then iterationsArg else kindArg

def headerSlot (j : Nat) : List Instr :=
  if j = 4 then [.mov .r0 (.imm 0x13), .str .r0 .r4 (768 + 4 * j)]
  else [ld .r0 (argOff (headerArg j)), .str .r0 .r4 (768 + 4 * j)]

def header : List Instr := (List.range 6).flatMap headerSlot

/-- Point `r4` to `scratch`, start an unkeyed 64-byte hash, and absorb the
header; the byte count is 24. -/
def start : Prog isa :=
  .seq (.block [ld .r4 (argOff scratchArg), .mov .r1 (.imm 64)])
  (.seq HPrime.init
  (.seq (.block header)
  (.seq (HPrime.absorbFixed 768 24)
    (.block [.mov .r0 (.imm 24), st countLoOff .r0, .mov .r0 (.imm 0), st countHiOff .r0]))))

/-- Add `y` to the 64-bit byte count. -/
def addCount (y : Op2) : List Instr :=
  [ld .r2 countLoOff, ld .r3 countHiOff, .adds .r2 .r2 y, .adc .r3 .r3 (.imm 0), st countLoOff .r2,
    st countHiOff .r3]

/-- Absorb LE32(length) and the input (`ptr`, `len` are its arguments). -/
def absorb (ptr len : Nat) : Prog isa :=
  .seq (.block [ld .r0 (argOff len), .str .r0 .r4 792, ld .r2 countLoOff, ld .r3 countHiOff,
      .dp .add .r9 .r4 (.imm 792), .mov .r10 (.imm 4)])
  (.seq HPrime.update
  (.seq (.block (addCount (.imm 4) ++ [ld .r9 (argOff ptr), ld .r10 (argOff len)]))
  (.seq HPrime.update (.block (ld .r0 (argOff len) :: addCount (.reg .r0))))))

/-- Copy the digest's word `j` to the locals. -/
def copyWord (j : Nat) : List Instr := [.ldr .r0 .r4 (768 + 4 * j), st (4 * j) .r0]

/-- Finalize, and copy H₀ to the locals. -/
def finish : Prog isa :=
  .seq (.block [ld .r2 countLoOff, ld .r3 countHiOff])
    (.seq HPrime.finalize (.block ((List.range 16).flatMap copyWord)))

def code : Prog isa :=
  .seq start
  (.seq (absorb passwordArg passwordLenArg)
  (.seq (absorb saltArg saltLenArg)
  (.seq (absorb secretArg secretLenArg)
  (.seq (absorb adArg adLenArg) finish))))

end VG.Impl.Argon2.Arm.Derive
