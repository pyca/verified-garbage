module

public import VerifiedGarbage.Impl.Argon2.PPC64LE.Layout
public import VerifiedGarbage.Impl.Argon2.PPC64LE.Divide
public import VerifiedGarbage.Impl.Argon2.PPC64LE.HPrime

/-!
# Argon2 on PPC64LE: the parameters and H₀

`r30` points to the derivation's frame (`Impl/Argon2/PPC64LE/Layout.lean`)
and `r31` to `scratch`.

* `parameters`: the segment length `⌊memory_cost / (4 · lanes)⌋`, by the
  fixed-time division, the lane length (four segments) and its size in
  bytes.
* `code`: H₀ (RFC 9106 §3.2), with H′'s calls of the BLAKE2b streaming
  functions (`Impl/Argon2/PPC64LE/HPrime.lean`), whose state and scratch are
  at the start of `scratch`: the six public parameters at `scratch + 896`,
  then LE32 of each input's length (at `scratch + 920`) and the input
  itself; the byte count is kept in the frame. The digest is copied to H₀'s
  place in the frame.
-/

@[expose] public section

namespace VG.Impl.Argon2.PPC64LE.Derive

open VG.PPC64LE

/-- `r := [r30 + d]` -/
def ld (r : Reg) (d : Nat) : Instr := .load .d r .r30 d

/-- `[r30 + d] := r` -/
def st (d : Nat) (r : Reg) : Instr := .store .d r .r30 d

/-- `r :=` the 32-bit argument `i`. -/
def ldw (r : Reg) (i : Nat) : Instr := .load .w r .r30 (argOff i)

/-- `r :=` the 64-bit argument `i`. -/
def lda (r : Reg) (i : Nat) : Instr := .load .d r .r30 (argOff i)

/-! ## The parameters -/

def parameters : List Instr :=
  [ldw .r3 lanesArg, .lsl .r5 .r3 2, ldw .r4 memoryCostArg] ++ Divide.code ++
  [st segLenOff .r6, .lsl .r6 .r6 2, st laneLenOff .r6, .lsl .r6 .r6 10, st strideOff .r6]

/-! ## H₀ -/

/-- The argument whose low 32 bits are word `j` of H₀'s header (but the
version, word 4): lanes, tag length, memory, passes, version, variant. -/
def headerArg (j : Nat) : Nat :=
  if j = 0 then lanesArg else if j = 1 then outLenArg else if j = 2 then memoryCostArg
  else if j = 3 then iterationsArg else kindArg

def headerSlot (j : Nat) : List Instr :=
  if j = 4 then [.li .r3 0x13, .store .w .r3 .r31 (896 + 4 * j)]
  else [ldw .r3 (headerArg j), .store .w .r3 .r31 (896 + 4 * j)]

def header : List Instr := (List.range 6).flatMap headerSlot

/-- Start an unkeyed 64-byte hash and absorb the header; the byte count is
24. -/
def start : Prog isa :=
  .seq (.block [.li .r4 64])
  (.seq HPrime.init
  (.seq (.block header)
  (.seq (HPrime.absorbFixed 896 24) (.block [.li .r3 24, st countOff .r3]))))

/-- Absorb LE32(length) and the input (`ptr`, `len` are its arguments). -/
def absorb (ptr len : Nat) : Prog isa :=
  .seq (.block [lda .r3 len, .store .w .r3 .r31 920, ld .r4 countOff, .addi .r5 .r31 920, .li .r6 4])
  (.seq HPrime.update
  (.seq (.block [ld .r4 countOff, .addi .r4 .r4 4, st countOff .r4, lda .r5 ptr, lda .r6 len])
  (.seq HPrime.update (.block [ld .r4 countOff, lda .r3 len, .add .r4 .r4 .r3, st countOff .r4]))))

/-- Copy the digest's doubleword `j` to H₀'s place. -/
def copyWord (j : Nat) : List Instr := [.load .d .r3 .r31 (768 + 8 * j), st (h0Off + 8 * j) .r3]

/-- Finalize, and copy H₀ to the frame. -/
def finish : Prog isa :=
  .seq (.block [ld .r4 countOff]) (.seq HPrime.finalize (.block ((List.range 8).flatMap copyWord)))

def code : Prog isa :=
  .seq start
  (.seq (absorb passwordArg passwordLenArg)
  (.seq (absorb saltArg saltLenArg)
  (.seq (absorb secretArg secretLenArg)
  (.seq (absorb adArg adLenArg) finish))))

end VG.Impl.Argon2.PPC64LE.Derive
