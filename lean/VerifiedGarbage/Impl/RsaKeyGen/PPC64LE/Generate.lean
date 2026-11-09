module

public import VerifiedGarbage.Impl.Bignum.PPC64LE.MontMul

/-! # RSA key generation over refillable random tapes on PPC64LE

`vg_rsa_generate(key = r3, key_len = r4, used = r5, rand = r6,
rand_len = r7, scratch = r8, scratch_len = r9, state = r10)`
(`VG.Spec.RsaKeyGen.keySearch`), as on x86-64
(`Impl/RsaKeyGen/X86_64/Generate.lean`): calls the prime search
(`vg_rsa_prime_search`) on the rest of the tape for `p`, then `q` against
`p`, and the key from them (`vg_rsa_keygen_key`), until a key is found, a
check fails, every generation is exhausted, or the tape runs out. The
search's progress is in `state` (the prime search's four words, the phase
and the generations left) and, for `q`'s search, `p` in the key's buffer.

The controller's own words are in a frame of 144 bytes, whose 112 bytes
above the back chain's 32 hold 14 words, with their base kept in the
callee-saved `r31` (the caller's `r31` saved in word 9), as the prime search
does (`Impl/RsaKeyGen/PPC64LE/Search.lean`). The loop runs in a frame saving
the link register, which the calls change; the search in a frame of 128
bytes holding its four stack arguments at offset 96, the key in one of 176
holding its ten. The comparisons are the sign bits of differences of small
numbers.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.PPC64LE.Generate

open VG VG.PPC64LE VG.Impl.Bignum.PPC64LE

/-- Frame word `j`: 0 `key`, 1 `p_len` (the primes' octets, `state[1]`),
2 `used`, 3 `rand`, 4 `rand_len`, 5 `scratch`, 6 `scratch_len`, 7 `state`,
8 the octets consumed, 9 the caller's `r31`, 10 the status (4 while the
search goes on), 11 the counted candidates each prime's search starts with,
12 and 13 a region to zero. -/
def ldf (t : Reg) (j : Nat) : Instr := .load .d t .r31 (8 * j)
def stf (t : Reg) (j : Nat) : Instr := .store .d t .r31 (8 * j)

/-- `c₁; c₂; …`. -/
def seqs : List (Prog isa) → Prog isa
  | [] => .block []
  | [c] => c
  | c :: cs => .seq c (seqs cs)

/-- The frame's size, with the back chain's 32 bytes: 14 words above them. -/
def frameBytes : Nat := 144

/-- The frame's words' base in `r31`, the caller's `r31` saved in word 9,
and the arguments stored. -/
def entryHead : List Instr := [
  .addSp .r11 32, .store .d .r31 .r11 72, .addi .r31 .r11 0,
  stf .r3 0, stf .r5 2, stf .r6 3, stf .r7 4, stf .r8 5, stf .r9 6, stf .r10 7]

/-- `p_len`, nothing consumed, and the counted candidates of a prime's
search: `40 p_len`, and `24 p_len` more for an exponent of 3 (its eight
octets, most significant first, read as a word: `3 · 2^56`), which `r7`, 1
exactly when the word XOR `3 · 2^56` is zero (the OR of its two halves is
below 1), multiplies. -/
def entryWords : List Instr := [
  .load .d .r4 .r10 8, .load .d .r9 .r10 48, stf .r4 1, .li .r0 0, stf .r0 8,
  .lsl .r5 .r4 3, .lsl .r6 .r4 5, .add .r5 .r5 .r6,
  .lsl .r6 .r4 4, .lsl .r7 .r4 3, .add .r6 .r6 .r7,
  .li .r7 3, .lsl .r7 .r7 56, .logic .xor .r8 .r9 .r7,
  .lsr .d .r7 .r8 32, .lsr .w .r8 .r8 0, .logic .or .r7 .r7 .r8, .li .r8 1, .sub .r7 .r7 .r8, .lsr .d .r7 .r7 63,
  .mul .r6 .r6 .r7, .add .r5 .r5 .r6, stf .r5 11]

/-- Zeros at the region in words 12 and 13, of at least one octet. -/
def clear : Prog isa :=
  .seq (.block [ldf .r3 12, ldf .r4 13, .li .r5 0]) (countLoop .r4 [.stb .r5 .r3 0, .addi .r3 .r3 1])

/-- The key's buffer but `p`: `4 p_len` octets from `key`, then from
`key + 5 p_len`. -/
def clearAround : Prog isa := seqs [
  .block [ldf .r3 0, stf .r3 12, ldf .r4 1, .lsl .r4 .r4 2, stf .r4 13],
  clear,
  .block [ldf .r4 1, .lsl .r5 .r4 2, .add .r4 .r4 .r5, ldf .r3 0, .add .r3 .r3 .r4, stf .r3 12,
    ldf .r4 1, .lsl .r4 .r4 2, stf .r4 13],
  clear]

/-- The whole key's buffer, `9 p_len` octets. -/
def clearAll : Prog isa := .seq
  (.block [ldf .r3 0, stf .r3 12, ldf .r4 1, .lsl .r5 .r4 3, .add .r5 .r5 .r4, stf .r5 13])
  clear

/-- The search's stack arguments, at offset 96 of the frame of 128 bytes the
call allocates: the tape's length after the octets consumed, `scratch`,
`scratch_len` and `state`. -/
def searchStack : List Instr := [
  ldf .r12 7, ldf .r3 4, ldf .r4 8, ldf .r5 5, ldf .r6 6, .sub .r3 .r3 .r4, .addSp .r11 96,
  .store .d .r3 .r11 0, .store .d .r5 .r11 8, .store .d .r6 .r11 16, .store .d .r12 .r11 24]

/-- The search's register arguments: `out` is `key + 4 p_len` for `p` (phase
0), `key + 5 p_len` for `q` (phase 1); `p` is `key + 4 p_len`, of `p_len`
octets for `q` and none for `p` (the phase times `p_len`); `e` the state's
last word, of 8 octets; the tape after the octets consumed. -/
def searchArgs : List Instr := [
  ldf .r12 7, .load .d .r11 .r12 32, ldf .r4 1, .lsl .r8 .r4 2, ldf .r3 0, .add .r8 .r8 .r3,
  .mul .r9 .r4 .r11, .add .r3 .r8 .r9, ldf .r5 2, .addi .r6 .r12 48, .li .r7 8,
  ldf .r10 3, ldf .r0 8, .add .r10 .r10 .r0]

/-- The key's stack arguments, at offset 96 of the frame of 176 bytes the call
allocates: `dP`, `dQ` and `qInv` at `key + j p_len` for `j = 6, 7, 8`, each of
`p_len` octets, `e` the state's last word of 8 octets, and the working
space. -/
def keyStack : List Instr := [
  ldf .r3 0, ldf .r4 1, ldf .r12 7, ldf .r5 5, ldf .r6 6, .lsl .r7 .r4 2, .lsl .r8 .r4 1, .add .r7 .r7 .r8,
  .add .r7 .r3 .r7, .add .r8 .r7 .r4, .add .r9 .r8 .r4, .addi .r10 .r12 48, .li .r0 8, .addSp .r11 96,
  .store .d .r7 .r11 0, .store .d .r4 .r11 8, .store .d .r8 .r11 16, .store .d .r4 .r11 24,
  .store .d .r9 .r11 32, .store .d .r4 .r11 40, .store .d .r10 .r11 48, .store .d .r0 .r11 56,
  .store .d .r5 .r11 64, .store .d .r6 .r11 72]

/-- The key's register arguments: `n`, `d`, `p` and `q` at `key + j p_len`
for `j = 0, 2, 4, 5`, `n` and `d` of `2 p_len` octets, the primes of
`p_len`. -/
def keyArgs : List Instr := [
  ldf .r8 1, ldf .r3 0, .lsl .r4 .r8 1, .add .r5 .r3 .r4, .addi .r6 .r4 0, .add .r7 .r5 .r4,
  .add .r9 .r7 .r8, .addi .r10 .r8 0]

variable (search key : Prog isa)

/-- The prime search, in a frame of its stack arguments. -/
def searchRun : Prog isa :=
  .frame (.alloc 128) (.seq (.block searchStack) (.seq (.block searchArgs) search)) (.free 128)

/-- The key from the primes, in a frame of its stack arguments. -/
def keyRun : Prog isa := .frame (.alloc 176) (.seq (.block keyStack) (.seq (.block keyArgs) key)) (.free 176)

/-- The next prime's search, from all its counted candidates, in `phase`. -/
def nextPrime (phase : Nat) : List Instr := [
  ldf .r12 7, ldf .r11 11, .store .d .r11 .r12 0, .li .r11 phase, .store .d .r11 .r12 32,
  .li .r11 4, stf .r11 10]

/-- The search ends with `status`: no phase or generations left, and zeros
for the key but its status 1. -/
def finishWith (status : Nat) : List Instr := [
  ldf .r12 7, .li .r11 0, .store .d .r11 .r12 32, .store .d .r11 .r12 40, .li .r11 status, stf .r11 10]

def fail (status : Nat) : Prog isa := .seq clearAll (.block (finishWith status))

/-- A prime's search exhausted: this generation fails; the next, or none.
`r10` is `left / 2`: zero exactly for the last generation (`left ≤ 1`). -/
def exhaustedGen : Prog isa := .seq
  (.block [ldf .r12 7, .load .d .r11 .r12 40, .lsr .d .r10 .r11 1])
  (.ite (.zero .d .r10) (fail 3) (.block ([.subi .r11 .r11 1, .store .d .r11 .r12 40] ++ nextPrime 0)))

/-- The key's status, its low 32 bits, in `r3`. -/
def afterKey : Prog isa := .seq (.block [.lsr .w .r3 .r3 0, .subi .r11 .r3 1])
  (.ite (.zero .d .r11) (.block (finishWith 1)) (.seq (.block [.subi .r11 .r3 2])
    (.ite (.zero .d .r11) (.block (nextPrime 0)) (fail 2))))

/-- A prime accepted: `q` next, or the key. -/
def accepted : Prog isa := .seq
  (.block [ldf .r12 7, .load .d .r11 .r12 32])
  (.ite (.zero .d .r11) (.block (nextPrime 1)) (.seq (keyRun key) afterKey))

/-- After the search: its status, its low 32 bits, in `r3`, the octets it
consumed at `used`, into `r11`. -/
def classify : Prog isa := seqs [
  .block [.lsr .w .r3 .r3 0, ldf .r11 2, .load .d .r11 .r11 0, ldf .r12 8, .add .r12 .r12 .r11,
    stf .r12 8],
  .ite (.zero .d .r3) (.block [stf .r3 10]) (.seq (.block [.subi .r12 .r3 3])
    (.ite (.zero .d .r12) exhaustedGen (.ite (.zero .d .r11) (fail 3) (accepted key))))]

/-- The loop goes on while the status is 4: `r9 := status − 4`. -/
def iteration : Prog isa := seqs [
  searchRun search, classify key, .block [ldf .r9 10, .subi .r9 .r9 4]]

/-- The key's buffer cleared but `p`, and the loop, in the frame saving the
link register. -/
def body : Prog isa :=
  .seq (.block [.mflr .r0])
    (.seq (.frame (.push .r0) (.seq clearAround (.loop (iteration search key) (.zero .d .r9))) (.pop .r0))
      (.block [.mtlr .r0]))

/-- The octets consumed to `used`, the status returned and the caller's
`r31` restored. -/
def finish : List Instr := [ldf .r5 2, ldf .r6 8, .store .d .r6 .r5 0, ldf .r3 10, ldf .r31 9]

def code : Prog isa := .frame (.alloc frameBytes)
  (seqs [.block (entryHead ++ entryWords), body search key, .block finish])
  (.free frameBytes)

end VG.Impl.RsaKeyGen.PPC64LE.Generate
