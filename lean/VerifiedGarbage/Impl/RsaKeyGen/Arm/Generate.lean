module

public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey

/-! # RSA key generation over refillable random tapes on ARMv7

`vg_rsa_generate(key = r0, key_len = r1, used = r2, rand = r3, rand_len = [sp],
scratch = [sp + 4], scratch_len = [sp + 8], state = [sp + 12])`
(`VG.Spec.RsaKeyGen.keySearch`), as on x86-64
(`Impl/RsaKeyGen/X86_64/Generate.lean`): calls the prime search
(`vg_rsa_prime_search`) on the rest of the tape for `p`, then `q` against
`p`, and the key from them (`vg_rsa_keygen_key`), until a key is found, a
check fails, every generation is exhausted, or the tape runs out. The
search's progress is in `state` (the prime search's four words, the phase
and the generations left) and, for `q`'s search, `p` in the key's buffer.

The controller's own working state is in the callee-saved registers, which
both callees keep, as the prime search's is (`Impl/RsaKeyGen/Arm/Search.lean`):
`r4 = key`, `r5 = p_len` (the primes' octets, the low half of `state[1]`),
`r6 = used`, `r7 = rand`, the octets consumed in `r8`, `r9 = state`, the
counted candidates each prime's search starts with in `r10` and the status
in `r11` (4 while the search goes on). It saves them, `r12` and `lr` in a
frame of 40 bytes; `rand_len`, `scratch` and `scratch_len` it reads from its
own stack arguments. Each call is in a frame of its stack arguments. The
state's `u64` words are read and written as their halves.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.Arm.Generate

open VG VG.Arm

/-- The bytes the controller pushes. -/
def pushBytes : Nat := 40

/-- The stack argument `j` of the controller, below `extra` more bytes of frame. -/
def arg (t : Reg) (extra j : Nat) : Instr := .ldrSp t (pushBytes + extra + 4 * j)

/-- The arguments saved, `p_len`, nothing consumed, the search going on, and
the counted candidates of a prime's search: `40 p_len`, or `64 p_len` for an
exponent of 3 (its eight octets, most significant first: the low word zero
and the high word `3 · 2^24`), `64 p_len - 24 p_len · [e ≠ 3]`. -/
def entryHead : List Instr := [
  arg .r9 0 3, .mov .r4 (.reg .r0), .mov .r6 (.reg .r2), .mov .r7 (.reg .r3), .ldr .r5 .r9 8,
  .mov .r8 (.imm 0), .mov .r11 (.imm 4)]

def entryThree : List Instr := [
  .ldr .r0 .r9 48, .ldr .r1 .r9 52, .dp .eor .r1 .r1 (.imm 0x03000000), .dp .orr .r0 .r0 (.reg .r1),
  .subs .r0 .r0 (.imm 1), .mov .r0 (.imm 0), .adc .r0 .r0 (.imm 0)]

def entryLimit : List Instr := [
  .mov .r1 (.shifted .r5 .lsl 3), .dp .add .r1 .r1 (.shifted .r5 .lsl 4), .mul .r0 .r0 .r1,
  .mov .r10 (.shifted .r5 .lsl 6), .dp .sub .r10 .r10 (.reg .r0)]

def entry : List Instr := entryHead ++ entryThree ++ entryLimit

/-- `lr` zeros from `r0` (at least one). -/
def zeros (setup : List Instr) : Prog isa :=
  .seq (.block (setup ++ [.mov .r2 (.imm 0)])) Impl.Ffdh.Arm.Domain.GenerateKey.zeros

/-- The key's buffer but `p`: `4 p_len` octets from `key`, then from
`key + 5 p_len`. -/
def clearAround : Prog isa := .seq
  (zeros [.mov .r0 (.reg .r4), .mov .lr (.shifted .r5 .lsl 2)])
  (zeros [.dp .add .r0 .r4 (.shifted .r5 .lsl 2), .dp .add .r0 .r0 (.reg .r5), .mov .lr (.shifted .r5 .lsl 2)])

/-- The whole key's buffer, `9 p_len` octets. -/
def clearAll : Prog isa :=
  zeros [.mov .r0 (.reg .r4), .mov .lr (.shifted .r5 .lsl 3), .dp .add .lr .lr (.reg .r5)]

/-- The search's arguments: `out` is `key + 4 p_len` for `p`, `key + 5 p_len`
for `q` (the phase, 0 or 1, times `p_len` more); `p` is `key + 4 p_len`, of
`p_len` octets for `q` and none for `p`; `e` is the state's last word, of 8
octets; the tape after the octets consumed (`randPtr`). Its stack arguments
at the 32 bytes the call's frame allocates (`lr` its base, from which the
controller's own stack arguments are read too, 72 bytes above). -/
def searchRegs : List Instr := [
  .dp .add .r0 .r4 (.shifted .r5 .lsl 2), .str .r0 .lr 4,
  .ldr .r12 .r9 32, .mul .r12 .r12 .r5, .str .r12 .lr 8, .dp .add .r0 .r0 (.reg .r12),
  .mov .r1 (.reg .r5), .mov .r2 (.reg .r6), .dp .add .r3 .r9 (.imm 48)]

/-- The tape's pointer for the search: `rand + used` while octets are left,
`rand` once none are (whose empty tape is then within the controller's, as
`rand + rand_len` may wrap): `rand + used · [used ≤ rand_len - 1]`. -/
def randPtr : List Instr := [
  .ldr .r12 .lr 72, .dp .sub .r12 .r12 (.imm 1), .cmp .r12 (.reg .r8), .mov .r0 (.imm 0), .adc .r0 .r0 (.imm 0),
  .mul .r12 .r0 .r8, .dp .add .r12 .r7 (.reg .r12)]

def stackHead : List Instr := [.mov .r12 (.imm 8), .str .r12 .lr 0]

def stackTail : List Instr := [
  .str .r12 .lr 12,
  .ldr .r12 .lr 72, .dp .sub .r12 .r12 (.reg .r8), .str .r12 .lr 16,
  .ldr .r12 .lr 76, .str .r12 .lr 20,
  .ldr .r12 .lr 80, .str .r12 .lr 24,
  .str .r9 .lr 28]

def searchStack : List Instr := stackHead ++ randPtr ++ stackTail

def searchArgs : List Instr := .addSp .lr 0 :: (searchStack ++ searchRegs)

/-- The key's arguments: `n`, `d` (`2 p_len` octets each), `p`, `q`, `dP`,
`dQ`, `qInv` (`p_len` each) at `key + j p_len` for `j = 0, 2, 4, 5, 6, 7, 8`,
`e` the state's last word, of 8 octets, and the working space. Its stack
arguments at the 56 bytes the call's frame allocates (`lr` its base). -/
def keyRegs : List Instr := [
  .mov .r0 (.reg .r4), .mov .r1 (.shifted .r5 .lsl 1), .dp .add .r2 .r0 (.reg .r1),
  .mov .r3 (.reg .r1), .dp .add .r12 .r2 (.reg .r1)]

def keyPrimes : List Instr := [
  .str .r12 .lr 0, .str .r5 .lr 4,
  .dp .add .r12 .r12 (.reg .r5), .str .r12 .lr 8, .str .r5 .lr 12,
  .dp .add .r12 .r12 (.reg .r5), .str .r12 .lr 16, .str .r5 .lr 20]

def keyCrt : List Instr := [
  .dp .add .r12 .r12 (.reg .r5), .str .r12 .lr 24, .str .r5 .lr 28,
  .dp .add .r12 .r12 (.reg .r5), .str .r12 .lr 32, .str .r5 .lr 36]

def keyRest : List Instr := [
  .dp .add .r12 .r9 (.imm 48), .str .r12 .lr 40, .mov .r12 (.imm 8), .str .r12 .lr 44,
  .ldr .r12 .lr 100, .str .r12 .lr 48,
  .ldr .r12 .lr 104, .str .r12 .lr 52]

def keyArgs : List Instr := .addSp .lr 0 :: (keyRegs ++ keyPrimes ++ keyCrt ++ keyRest)

variable (search key : Prog isa)

/-- The prime search, in a frame of its stack arguments. -/
def searchRun : Prog isa := .frame (.alloc 32) (.seq (.block searchArgs) search) (.free 32)

/-- The key from the primes, in a frame of its stack arguments. -/
def keyRun : Prog isa := .frame (.alloc 56) (.seq (.block keyArgs) key) (.free 56)

/-- The next prime's search, from all its counted candidates, in `phase`. -/
def nextPrime (phase : Nat) : List Instr := [
  .mov .r12 (.imm 0), .str .r10 .r9 0, .str .r12 .r9 4, .str .r12 .r9 36,
  .mov .r12 (.imm (BitVec.ofNat 32 phase)), .str .r12 .r9 32, .mov .r11 (.imm 4)]

/-- The search ends with `status`: no phase or generations left. -/
def finishWith (status : Nat) : List Instr := [
  .mov .r12 (.imm 0), .str .r12 .r9 32, .str .r12 .r9 36, .str .r12 .r9 40, .str .r12 .r9 44,
  .mov .r11 (.imm (BitVec.ofNat 32 status))]

/-- Zeros for the key, and `status`. -/
def fail (status : Nat) : Prog isa := .seq clearAll (.block (finishWith status))

/-- The generations left, a `u64` at `state + 40`, minus one: the low half
less one, and the high half less its borrow. -/
def decLeft : List Instr := [
  .ldr .r0 .r9 40, .ldr .r1 .r9 44, .subs .r0 .r0 (.imm 1), .mov .r2 (.imm 0), .adc .r2 .r2 (.imm 0),
  .dp .add .r1 .r1 (.reg .r2), .dp .sub .r1 .r1 (.imm 1), .str .r0 .r9 40, .str .r1 .r9 44]

/-- A prime's search exhausted: this generation fails, and so does the key
search if it was the last (`Z` iff the generations left are at most 1: the
low half below 2 and the high half zero); otherwise the next generation. -/
def exhaustedGen : Prog isa := .seq
  (.block [.ldr .r0 .r9 40, .ldr .r1 .r9 44, .cmp .r0 (.imm 2), .mov .r0 (.imm 0), .adc .r0 .r0 (.imm 0),
    .dp .orr .r0 .r0 (.reg .r1), .cmp .r0 (.imm 0)])
  (.ite .eq (fail 3) (.block (decLeft ++ nextPrime 0)))

/-- The key's status, in `r0`. -/
def afterKey : Prog isa := .seq (.block [.cmp .r0 (.imm 1)])
  (.ite .eq (.block (finishWith 1)) (.seq (.block [.cmp .r0 (.imm 2)])
    (.ite .eq (.block (nextPrime 0)) (fail 2))))

/-- A prime accepted: `q` next, or the key. -/
def accepted : Prog isa := .seq (.block [.ldr .r12 .r9 32, .cmp .r12 (.imm 0)])
  (.ite .eq (.block (nextPrime 1)) (.seq (keyRun key) afterKey))

/-- After the search: its status in `r0`, the octets it consumed (the low
half of `used`) added to `r8`. -/
def classify : Prog isa := .seq
  (.block [.ldr .r12 .r6 0, .dp .add .r8 .r8 (.reg .r12), .cmp .r0 (.imm 0)])
  (.ite .eq (.block [.mov .r11 (.imm 0)]) (.seq (.block [.cmp .r0 (.imm 3)])
    (.ite .eq exhaustedGen (.seq (.block [.cmp .r12 (.imm 0)]) (.ite .eq (fail 3) (accepted key))))))

/-- The loop goes on while the status is 4. -/
def iteration : Prog isa :=
  .seq (searchRun search) (.seq (classify key) (.block [.cmp .r11 (.imm 4)]))

/-- The octets consumed to `used`, and the status returned. -/
def results : List Instr := [.str .r8 .r6 0, .mov .r0 (.imm 0), .str .r0 .r6 4, .mov .r0 (.reg .r11)]

/-- The callee-saved registers but `r4`, which the frame's pop restores. -/
def restore : List Instr := [
  .ldrSp .r5 4, .ldrSp .r6 8, .ldrSp .r7 12, .ldrSp .r8 16, .ldrSp .r9 20, .ldrSp .r10 24,
  .ldrSp .r11 28, .ldrSp .lr 36]

def finish : List Instr := results ++ restore

def body : Prog isa :=
  .seq (.block entry) (.seq clearAround (.seq (.loop (iteration search key) .eq) (.block finish)))

def code : Prog isa :=
  .frame (.push [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (body search key) (.pop .r4 pushBytes)

end VG.Impl.RsaKeyGen.Arm.Generate
