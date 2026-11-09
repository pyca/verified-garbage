module

public import VerifiedGarbage.Impl.Bignum.RISCV64.MontMul

/-! # RSA key generation over refillable random tapes on RISC-V

`vg_rsa_generate(key = a0, key_len = a1, used = a2, rand = a3,
rand_len = a4, scratch = a5, scratch_len = a6, state = a7)`
(`VG.Spec.RsaKeyGen.keySearch`), as on PPC64LE
(`Impl/RsaKeyGen/PPC64LE/Generate.lean`): calls the prime search
(`vg_rsa_prime_search`) on the rest of the tape for `p`, then `q` against
`p`, and the key from them (`vg_rsa_keygen_key`), until a key is found, a
check fails, every generation is exhausted, or the tape runs out. The
search's progress is in `state` (the prime search's four words, the phase
and the generations left) and, for `q`'s search, `p` in the key's buffer.

The controller's own words are in a frame of 112 bytes, 14 words, with their
base kept in the callee-saved `s0` (the caller's `s0` saved in word 9), as
the prime search does (`Impl/RsaKeyGen/RISCV64/Search.lean`). The loop runs
in a frame saving `ra`, which the calls change; the search in a frame of 32
bytes holding its four stack arguments, the key in one of 80 holding its ten.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.RISCV64.Generate

open VG VG.RISCV64 VG.Impl.Bignum.RISCV64

/-- Frame word `j`: 0 `key`, 1 `p_len` (the primes' octets, `state[1]`),
2 `used`, 3 `rand`, 4 `rand_len`, 5 `scratch`, 6 `scratch_len`, 7 `state`,
8 the octets consumed, 9 the caller's `s0`, 10 the status (4 while the
search goes on), 11 the counted candidates each prime's search starts with,
12 and 13 a region to zero. -/
def ldf (t : Reg) (j : Nat) : Instr := .load .d t .s0 (8 * j)
def stf (t : Reg) (j : Nat) : Instr := .store .d t .s0 (8 * j)

/-- `c₁; c₂; …`. -/
def seqs : List (Prog isa) → Prog isa
  | [] => .block []
  | [c] => c
  | c :: cs => .seq c (seqs cs)

/-- The frame's size: 14 words. -/
def frameBytes : Nat := 112

/-- The low 32 bits of `r`. -/
def low32 (r : Reg) : List Instr := [.shift .sll .d r r 32, .shift .srl .d r r 32]

/-- The frame's words' base in `s0`, the caller's `s0` saved in word 9, and
the arguments stored. -/
def entryHead : List Instr := [
  .addSp .t1 0, .store .d .s0 .t1 72, .addi .s0 .t1 0,
  stf .a0 0, stf .a2 2, stf .a3 3, stf .a4 4, stf .a5 5, stf .a6 6, stf .a7 7]

/-- `p_len`, nothing consumed, and the counted candidates of a prime's
search: `40 p_len`, and `24 p_len` more for an exponent of 3 (its eight
octets, most significant first, read as a word: `3 · 2^56`), which `a4`, 1
exactly when the word XOR `3 · 2^56` is below 1, multiplies. -/
def entryWords : List Instr := [
  .load .d .a1 .a7 8, .load .d .a6 .a7 48, stf .a1 1, .li .t0 0, stf .t0 8,
  .shift .sll .d .a2 .a1 3, .shift .sll .d .a3 .a1 5, .add .a2 .a2 .a3,
  .shift .sll .d .a3 .a1 4, .shift .sll .d .a4 .a1 3, .add .a3 .a3 .a4,
  .li .a4 3, .shift .sll .d .a4 .a4 56, .logic .xor .a5 .a6 .a4, .li .a4 1, .sltu .a4 .a5 .a4,
  .mul .a3 .a3 .a4, .add .a2 .a2 .a3, stf .a2 11]

/-- Zeros at the region in words 12 and 13, of at least one octet. -/
def clear : Prog isa :=
  .seq (.block [ldf .a1 12, ldf .a2 13, .li .a3 0]) (countLoop .a2 [.store .b .a3 .a1 0, .addi .a1 .a1 1])

/-- The key's buffer but `p`: `4 p_len` octets from `key`, then from
`key + 5 p_len`. -/
def clearAround : Prog isa := seqs [
  .block [ldf .a0 0, stf .a0 12, ldf .a1 1, .shift .sll .d .a1 .a1 2, stf .a1 13],
  clear,
  .block [ldf .a1 1, .shift .sll .d .a2 .a1 2, .add .a1 .a1 .a2, ldf .a0 0, .add .a0 .a0 .a1, stf .a0 12,
    ldf .a1 1, .shift .sll .d .a1 .a1 2, stf .a1 13],
  clear]

/-- The whole key's buffer, `9 p_len` octets. -/
def clearAll : Prog isa := .seq
  (.block [ldf .a0 0, stf .a0 12, ldf .a1 1, .shift .sll .d .a2 .a1 3, .add .a2 .a2 .a1, stf .a2 13])
  clear

/-- The search's stack arguments, in the frame of 32 bytes the call
allocates: the tape's length after the octets consumed, `scratch`,
`scratch_len` and `state`. -/
def searchStack : List Instr := [
  ldf .t2 7, ldf .a0 4, ldf .a1 8, ldf .a2 5, ldf .a3 6, .sub .a0 .a0 .a1, .addSp .t1 0,
  .store .d .a0 .t1 0, .store .d .a2 .t1 8, .store .d .a3 .t1 16, .store .d .t2 .t1 24]

/-- The search's register arguments: `out` is `key + 4 p_len` for `p` (phase
0), `key + 5 p_len` for `q` (phase 1); `p` is `key + 4 p_len`, of `p_len`
octets for `q` and none for `p` (the phase times `p_len`); `e` the state's
last word, of 8 octets; the tape after the octets consumed. -/
def searchArgs : List Instr := [
  ldf .t2 7, .load .d .t1 .t2 32, ldf .a1 1, .shift .sll .d .a5 .a1 2, ldf .a0 0, .add .a5 .a5 .a0,
  .mul .a6 .a1 .t1, .add .a0 .a5 .a6, ldf .a2 2, .addi .a3 .t2 48, .li .a4 8,
  ldf .a7 3, ldf .t0 8, .add .a7 .a7 .t0]

/-- The key's stack arguments, in the frame of 80 bytes the call allocates:
`dP`, `dQ` and `qInv` at `key + j p_len` for `j = 6, 7, 8`, each of `p_len`
octets, `e` the state's last word of 8 octets, and the working space. -/
def keyStack : List Instr := [
  ldf .a0 0, ldf .a1 1, ldf .t2 7, ldf .a2 5, ldf .a3 6, .shift .sll .d .a4 .a1 2, .shift .sll .d .a5 .a1 1,
  .add .a4 .a4 .a5, .add .a4 .a0 .a4, .add .a5 .a4 .a1, .add .a6 .a5 .a1, .addi .a7 .t2 48, .li .t0 8,
  .addSp .t1 0,
  .store .d .a4 .t1 0, .store .d .a1 .t1 8, .store .d .a5 .t1 16, .store .d .a1 .t1 24,
  .store .d .a6 .t1 32, .store .d .a1 .t1 40, .store .d .a7 .t1 48, .store .d .t0 .t1 56,
  .store .d .a2 .t1 64, .store .d .a3 .t1 72]

/-- The key's register arguments: `n`, `d`, `p` and `q` at `key + j p_len`
for `j = 0, 2, 4, 5`, `n` and `d` of `2 p_len` octets, the primes of
`p_len`. -/
def keyArgs : List Instr := [
  ldf .a5 1, ldf .a0 0, .shift .sll .d .a1 .a5 1, .add .a2 .a0 .a1, .addi .a3 .a1 0, .add .a4 .a2 .a1,
  .add .a6 .a4 .a5, .addi .a7 .a5 0]

variable (search key : Prog isa)

/-- The prime search, in a frame of its stack arguments. -/
def searchRun : Prog isa :=
  .frame (.alloc 32) (.seq (.block searchStack) (.seq (.block searchArgs) search)) (.free 32)

/-- The key from the primes, in a frame of its stack arguments. -/
def keyRun : Prog isa := .frame (.alloc 80) (.seq (.block keyStack) (.seq (.block keyArgs) key)) (.free 80)

/-- The next prime's search, from all its counted candidates, in `phase`. -/
def nextPrime (phase : Nat) : List Instr := [
  ldf .t2 7, ldf .t1 11, .store .d .t1 .t2 0, .li .t1 phase, .store .d .t1 .t2 32,
  .li .t1 4, stf .t1 10]

/-- The search ends with `status`: no phase or generations left, and zeros
for the key but its status 1. -/
def finishWith (status : Nat) : List Instr := [
  ldf .t2 7, .li .t1 0, .store .d .t1 .t2 32, .store .d .t1 .t2 40, .li .t1 status, stf .t1 10]

def fail (status : Nat) : Prog isa := .seq clearAll (.block (finishWith status))

/-- A prime's search exhausted: this generation fails; the next, or none.
`a7` is `left / 2`: zero exactly for the last generation (`left ≤ 1`). -/
def exhaustedGen : Prog isa := .seq
  (.block [ldf .t2 7, .load .d .t1 .t2 40, .shift .srl .d .a7 .t1 1])
  (.ite (.zero .a7) (fail 3) (.block ([.addi .t1 .t1 (-1), .store .d .t1 .t2 40] ++ nextPrime 0)))

/-- The key's status, its low 32 bits, in `a0`. -/
def afterKey : Prog isa := .seq (.block (low32 .a0 ++ [.addi .t1 .a0 (-1)]))
  (.ite (.zero .t1) (.block (finishWith 1)) (.seq (.block [.addi .t1 .a0 (-2)])
    (.ite (.zero .t1) (.block (nextPrime 0)) (fail 2))))

/-- A prime accepted: `q` next, or the key. -/
def accepted : Prog isa := .seq
  (.block [ldf .t2 7, .load .d .t1 .t2 32])
  (.ite (.zero .t1) (.block (nextPrime 1)) (.seq (keyRun key) afterKey))

/-- After the search: its status, its low 32 bits, in `a0`, the octets it
consumed at `used`, into `t1`. -/
def classify : Prog isa := seqs [
  .block (low32 .a0 ++ [ldf .t1 2, .load .d .t1 .t1 0, ldf .t2 8, .add .t2 .t2 .t1, stf .t2 8]),
  .ite (.zero .a0) (.block [stf .a0 10]) (.seq (.block [.addi .t2 .a0 (-3)])
    (.ite (.zero .t2) exhaustedGen (.ite (.zero .t1) (fail 3) (accepted key))))]

/-- The loop goes on while the status is 4: `a6 := status − 4`. -/
def iteration : Prog isa := seqs [
  searchRun search, classify key, .block [ldf .a6 10, .addi .a6 .a6 (-4)]]

/-- The key's buffer cleared but `p`, and the loop, in the frame saving
`ra`. -/
def body : Prog isa :=
  .frame (.push .ra) (.seq clearAround (.loop (iteration search key) (.zero .a6))) (.pop .ra)

/-- The octets consumed to `used`, the status returned and the caller's
`s0` restored. -/
def finish : List Instr := [ldf .a2 2, ldf .a3 8, .store .d .a3 .a2 0, ldf .a0 10, ldf .s0 9]

def code : Prog isa := .frame (.alloc frameBytes)
  (seqs [.block (entryHead ++ entryWords), body search key, .block finish])
  (.free frameBytes)

end VG.Impl.RsaKeyGen.RISCV64.Generate
