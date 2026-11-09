module

public import VerifiedGarbage.Impl.Bignum.AArch64.Core

/-! # RSA key generation over refillable random tapes on AArch64

`vg_rsa_generate(key = x0, key_len = x1, used = x2, rand = x3, rand_len = x4,
scratch = x5, scratch_len = x6, state = x7)` (`VG.Spec.RsaKeyGen.keySearch`),
as on x86-64 (`Impl/RsaKeyGen/X86_64/Generate.lean`): calls the prime search
(`vg_rsa_prime_search`) on the rest of the tape for `p`, then `q` against
`p`, and the key from them (`vg_rsa_keygen_key`), until a key is found, a
check fails, every generation is exhausted, or the tape runs out. The
search's progress is in `state` (the prime search's four words, the phase
and the generations left) and, for `q`'s search, `p` in the key's buffer.
The controller's own working state is in a frame of its own, of 160 bytes,
whose base is kept in the callee-saved `x19` (the caller's `x19` saved in
word 9). The rest runs in a frame saving `x30`, which the calls change; each
call in a frame of its stack arguments, as the prime search does
(`Impl/RsaKeyGen/AArch64/Search.lean`).
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.AArch64.Generate

open VG VG.AArch64 VG.Impl.Bignum.AArch64

/-- Frame word `j`: 0 `key`, 1 `p_len` (the primes' octets, `state[1]`), 2
`used`, 3 `rand`, 4 `rand_len`, 5 `scratch`, 6 `scratch_len`, 7 `state`, 8
the octets consumed, 9 the caller's `x19`, 10 the status (4 while the search
goes on), 11 the counted candidates each prime's search starts with, 12 and
13 a region to zero. -/
def ldf (t : Reg) (j : Nat) : Instr := .ldr .x t .x19 (8 * j)
def stf (t : Reg) (j : Nat) : Instr := .str .x t .x19 (8 * j)

/-- The frame's size: 20 words. -/
def frameBytes : Nat := 160

/-- The frame's base in `x14` and the state's words loaded; the caller's
`x19` saved and the arguments stored; then `p_len`, nothing consumed, and the counted candidates of a
prime's search: `40 p_len`, or `64 p_len` for an exponent of 3 (its eight
octets, most significant first, read as a word: `3 · 2^56`). -/
def entry : List Instr := [
  .addSp .x14 0, ld .x9 .x7 8, ld .x10 .x7 48, .str .x .x19 .x14 72, mov .x19 .x14,
  stf .x0 0, stf .x2 2, stf .x3 3, stf .x4 4, stf .x5 5, stf .x6 6, stf .x7 7,
  stf .x9 1, movi .x17 0, stf .x17 8,
  .lsl .x .x12 .x9 3, .lsl .x .x13 .x9 5, .add .x .x12 .x12 .x13, .lsl .x .x13 .x9 6,
  .movz .x .x15 (BitVec.ofNat 16 0x300) 3, .logic .eor .x .x16 .x10 .x15, .subs .x .x16 .x17 .x16,
  .csel .x .x12 .x13 .x12, stf .x12 11]

/-- Zeros at the region in words 12 and 13 (at least one octet). -/
def clear : Prog isa := .seq (.block [ldf .x1 12, ldf .x2 13, movi .x3 0])
  (countLoop .x2 [.strb .x3 .x1 0, .addImm .x .x1 .x1 1])

/-- The key's buffer but `p`: `4 p_len` octets from `key`, then from
`key + 5 p_len`. -/
def clearAround : Prog isa := seqs [
  .block [ldf .x9 0, ldf .x10 1, stf .x9 12, .lsl .x .x10 .x10 2, stf .x10 13],
  clear,
  .block [ldf .x10 1, .lsl .x .x11 .x10 2, .add .x .x11 .x11 .x10, ldf .x9 0, .add .x .x9 .x9 .x11, stf .x9 12,
    .lsl .x .x10 .x10 2, stf .x10 13],
  clear]

/-- The whole key's buffer, `9 p_len` octets. -/
def clearAll : Prog isa := .seq
  (.block [ldf .x9 0, ldf .x10 1, stf .x9 12, .lsl .x .x11 .x10 3, .add .x .x11 .x11 .x10, stf .x11 13])
  clear

/-- The search's arguments: `out` is `key + 4 p_len` for `p`, `key + 5 p_len`
for `q`; `p` is `key + 4 p_len`, of `p_len` octets for `q` and none for `p`;
`e` is the state's last word, of 8 octets; the tape after the octets
consumed. Its stack arguments at the 32 bytes the call's frame allocates. -/
def searchArgs : List Instr := [
  ldf .x8 7, ld .x10 .x8 32, ldf .x1 1, ldf .x9 0,
  .lsl .x .x5 .x1 2, .add .x .x5 .x5 .x9, .add .x .x0 .x5 .x1, movi .x17 0,
  .subs .x .x16 .x17 .x10, .csel .x .x0 .x5 .x0, .csel .x .x6 .x17 .x1,
  ldf .x2 2, .addImm .x .x3 .x8 48, movi .x4 8,
  ldf .x7 3, ldf .x11 8, .add .x .x7 .x7 .x11, ldf .x12 4, .sub .x .x12 .x12 .x11,
  ldf .x13 5, ldf .x14 6, .addSp .x15 0,
  .str .x .x12 .x15 0, .str .x .x13 .x15 8, .str .x .x14 .x15 16, .str .x .x8 .x15 24]

/-- The key's arguments: `n`, `d`, `p`, `q`, `dP`, `dQ`, `qInv` at `key + j
p_len` for `j = 0, 2, 4, 5, 6, 7, 8`, `e` the state's last word, and the
working space. Its stack arguments at the 80 bytes the call's frame
allocates. -/
def keyArgs : List Instr := [
  ldf .x5 1, ldf .x0 0, ldf .x10 7, ldf .x11 5, ldf .x12 6,
  .lsl .x .x1 .x5 1, .add .x .x2 .x0 .x1, mov .x3 .x1, .add .x .x4 .x2 .x1,
  .add .x .x6 .x4 .x5, mov .x7 .x5, .addSp .x15 0,
  .add .x .x9 .x6 .x5, .str .x .x9 .x15 0, .str .x .x5 .x15 8,
  .add .x .x9 .x9 .x5, .str .x .x9 .x15 16, .str .x .x5 .x15 24,
  .add .x .x9 .x9 .x5, .str .x .x9 .x15 32, .str .x .x5 .x15 40,
  .addImm .x .x10 .x10 48, .str .x .x10 .x15 48, movi .x9 8, .str .x .x9 .x15 56,
  .str .x .x11 .x15 64, .str .x .x12 .x15 72]

variable (search key : Prog isa)

/-- The prime search, in a frame of its stack arguments. -/
def searchRun : Prog isa := .frame (.alloc 32) (.seq (.block searchArgs) search) (.free 32)

/-- The key from the primes, in a frame of its stack arguments. -/
def keyRun : Prog isa := .frame (.alloc 80) (.seq (.block keyArgs) key) (.free 80)

/-- The next prime's search, from all its counted candidates, in `phase`. -/
def nextPrime (phase : Nat) : List Instr := [
  ldf .x8 7, ldf .x11 11, st .x11 .x8 0, movi .x11 phase, st .x11 .x8 32, movi .x11 4, stf .x11 10]

/-- The search ends with `status`: no phase or generations left, and zeros
for the key but its status 1. -/
def finishWith (status : Nat) : List Instr := [
  ldf .x8 7, movi .x11 0, st .x11 .x8 32, st .x11 .x8 40, movi .x11 status, stf .x11 10]

def fail (status : Nat) : Prog isa := .seq clearAll (.block (finishWith status))

/-- A prime's search exhausted: this generation fails; the next, or none
(`x12` is 1 exactly when at least two generations are left). -/
def exhaustedGen : Prog isa := .seq
  (.block [ldf .x8 7, ld .x10 .x8 40, movi .x15 2, movi .x13 1, movi .x17 0, .subs .x .x16 .x10 .x15,
    .csel .x .x12 .x13 .x17])
  (.ite (.zero .x .x12) (fail 3) (.block ([.subImm .x .x10 .x10 1, st .x10 .x8 40] ++ nextPrime 0)))

/-- The key's status, in `w0`. -/
def afterKey : Prog isa := .seq (.block [.addImm .w .x9 .x0 0, .subImm .x .x12 .x9 1])
  (.ite (.zero .x .x12) (.block (finishWith 1)) (.seq (.block [.subImm .x .x12 .x9 2])
    (.ite (.zero .x .x12) (.block (nextPrime 0)) (fail 2))))

/-- A prime accepted: `q` next, or the key. -/
def accepted : Prog isa := .seq (.block [ldf .x8 7, ld .x10 .x8 32])
  (.ite (.zero .x .x10) (.block (nextPrime 1)) (.seq (keyRun key) afterKey))

/-- After the search: its status in `w0`, the octets it consumed at `used`. -/
def classify : Prog isa := seqs [
  .block [.addImm .w .x9 .x0 0, ldf .x11 2, ld .x10 .x11, ldf .x12 8, .add .x .x12 .x12 .x10, stf .x12 8],
  .ite (.zero .x .x9) (.block [stf .x9 10]) (.seq (.block [.subImm .x .x12 .x9 3])
    (.ite (.zero .x .x12) exhaustedGen (.ite (.zero .x .x10) (fail 3) (accepted key))))]

/-- The loop goes on while the status is 4: `x9 := status − 4`. -/
def iteration : Prog isa := seqs [
  searchRun search, classify key, .block [ldf .x9 10, .subImm .x .x9 .x9 4]]

/-- The key's buffer cleared but `p`, then the loop, in a frame saving `x30`,
which the calls change. -/
def body : Prog isa :=
  .frame (.push .x30) (.seq clearAround (.loop (iteration search key) (.zero .x .x9))) (.pop .x30)

/-- All loads before the store of the octets consumed to `used`; the status
returned and the caller's `x19` restored. -/
def finish : List Instr := [ldf .x1 2, ldf .x2 8, ldf .x0 10, ldf .x19 9, st .x2 .x1 0]

def code : Prog isa := .frame (.alloc frameBytes)
  (seqs [.block entry, body search key, .block finish]) (.free frameBytes)

end VG.Impl.RsaKeyGen.AArch64.Generate
