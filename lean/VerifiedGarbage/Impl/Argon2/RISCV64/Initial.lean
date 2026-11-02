module

public import VerifiedGarbage.Impl.Argon2.RISCV64.Layout
public import VerifiedGarbage.Impl.Argon2.RISCV64.Divide
public import VerifiedGarbage.Impl.Argon2.RISCV64.HPrime

/-!
# Argon2 on RISC-V: the parameters and H₀

`s3` points to the derivation's frame (`Impl/Argon2/RISCV64/Layout.lean`)
and `s4` to the rounded `scratch`, as `r30` and `r31` on PPC64LE
(`Impl/Argon2/PPC64LE/Initial.lean`):

* `parameters`: the segment length `⌊memory_cost / (4 · lanes)⌋`, by the
  fixed-time division, the lane length (four segments) and its size in
  bytes.
* `code`: H₀ (RFC 9106 §3.2), with H′'s calls of the BLAKE2b streaming
  functions (`Impl/Argon2/RISCV64/HPrime.lean`), whose state and scratch are
  at the start of `scratch`: the six public parameters at `scratch + 896`,
  then LE32 of each input's length (at `scratch + 920`) and the input
  itself; the byte count is kept in the frame. The digest is copied to H₀'s
  place in the frame.
-/

@[expose] public section

namespace VG.Impl.Argon2.RISCV64.Derive

open VG.RISCV64

/-- `r := [s3 + d]` -/
def ld (r : Reg) (d : Nat) : Instr := .load .d r .s3 d

/-- `[s3 + d] := r` -/
def st (d : Nat) (r : Reg) : Instr := .store .d r .s3 d

/-- `r :=` the 32-bit argument `i` (its low half). -/
def ldw (r : Reg) (i : Nat) : Instr := .load .w r .s3 (argOff i)

/-- `r :=` the 64-bit argument `i`. -/
def lda (r : Reg) (i : Nat) : Instr := .load .d r .s3 (argOff i)

/-! ## The parameters -/

def parameters : List Instr :=
  [ldw .a0 lanesArg, .shift .sll .d .a2 .a0 2, ldw .a1 memoryCostArg] ++ Divide.code ++
  [st segLenOff .a3, .shift .sll .d .a3 .a3 2, st laneLenOff .a3, .shift .sll .d .a3 .a3 10,
    st strideOff .a3]

/-! ## H₀ -/

/-- The argument whose low 32 bits are word `j` of H₀'s header (but the
version, word 4): lanes, tag length, memory, passes, version, variant. -/
def headerArg (j : Nat) : Nat :=
  if j = 0 then lanesArg else if j = 1 then outLenArg else if j = 2 then memoryCostArg
  else if j = 3 then iterationsArg else kindArg

def headerSlot (j : Nat) : List Instr :=
  if j = 4 then [.li .a0 0x13, .store .w .a0 .s4 (896 + 4 * j)]
  else [ldw .a0 (headerArg j), .store .w .a0 .s4 (896 + 4 * j)]

def header : List Instr := (List.range 6).flatMap headerSlot

/-- Start an unkeyed 64-byte hash and absorb the header; the byte count is
24. -/
def start : Prog isa :=
  .seq (.block [.li .a1 64])
  (.seq HPrime.init
  (.seq (.block header)
  (.seq (HPrime.absorbFixed 896 24) (.block [.li .a0 24, st countOff .a0]))))

/-- Absorb LE32(length) and the input (`ptr`, `len` are its arguments). -/
def absorb (ptr len : Nat) : Prog isa :=
  .seq (.block [lda .a0 len, .store .w .a0 .s4 920, ld .a1 countOff, .addi .a2 .s4 920, .li .a3 4])
  (.seq HPrime.update
  (.seq (.block [ld .a1 countOff, .addi .a1 .a1 4, st countOff .a1, lda .a2 ptr, lda .a3 len])
  (.seq HPrime.update (.block [ld .a1 countOff, lda .a0 len, .add .a1 .a1 .a0, st countOff .a1]))))

/-- Copy the digest's doubleword `j` to H₀'s place. -/
def copyWord (j : Nat) : List Instr := [.load .d .a0 .s4 (768 + 8 * j), st (h0Off + 8 * j) .a0]

/-- Finalize, and copy H₀ to the frame. -/
def finish : Prog isa :=
  .seq (.block [ld .a1 countOff]) (.seq HPrime.finalize (.block ((List.range 8).flatMap copyWord)))

def code : Prog isa :=
  .seq start
  (.seq (absorb passwordArg passwordLenArg)
  (.seq (absorb saltArg saltLenArg)
  (.seq (absorb secretArg secretLenArg)
  (.seq (absorb adArg adLenArg) finish))))

end VG.Impl.Argon2.RISCV64.Derive
