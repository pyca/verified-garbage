module

public import VerifiedGarbage.Impl.Rsa.X86_64.Keys

/-! # RSA key generation over refillable random tapes on x86-64

`vg_rsa_generate(key, key_len, used, rand, rand_len, scratch, scratch_len,
state)` (`VG.Spec.RsaKeyGen.keySearch`): calls the prime search
(`vg_rsa_prime_search`) on the rest of the tape for `p`, then `q` against
`p`, and the key from them (`vg_rsa_keygen_key`), until a key is found, a
check fails, every generation is exhausted, or the tape runs out. The
search's progress is in `state` (the prime search's four words, the phase
and the generations left) and, for `q`'s search, `p` in the key's buffer;
the controller's own working state is in a frame of its own.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.X86_64.Generate

open VG VG.X86_64 VG.Impl.Bignum.X86_64

/-- The frame's words: 0 `key`, 1 `p_len` (the primes' octets, `state[1]`),
2 `used`, 3 `rand`, 4 `rand_len`, 5 `scratch`, 6 `scratch_len`, 7 `state`,
8 the octets consumed, 9 the caller's r12, 10 the status (4 while the search
goes on), 11 the counted candidates each prime's search starts with, 12 and
13 a region to zero. -/
def field (j : Nat) : MemOp := { base := .r12, disp := (8 * j : Nat) }

/-- The frame's size: 20 words (6 unused, the prime search's frame layout). -/
def frameBytes : Nat := 160

/-- The caller's stack argument `k`, above the frame and the return address. -/
def callerArg (k : Nat) : MemOp := { base := .rsp, disp := (frameBytes + 8 + 8 * k : Nat) }

/-- A word of the state, its pointer in rax. -/
def stw (j : Nat) : MemOp := { base := .rax, disp := (8 * j : Nat) }

def entryHead : List Instr := [
  .store { base := .rsp, disp := 72 } .r12, .mov .r12 (.reg .rsp),
  .store (field 0) .rdi, .store (field 2) .rdx, .store (field 3) .rcx, .store (field 4) .r8,
  .store (field 5) .r9,
  .mov .rax (.mem (callerArg 0)), .store (field 6) .rax,
  .mov .rax (.mem (callerArg 1)), .store (field 7) .rax]

/-- `p_len`, nothing consumed, and the counted candidates of a prime's
search: `40 p_len`, or `64 p_len` for an exponent of 3 (its eight octets,
most significant first, read as a word: `3 · 2^56`). -/
def entryWords : List Instr := [
  .mov .rcx (.mem (stw 1)), .mov .r9 (.mem (stw 6)), .store (field 1) .rcx,
  .mov32 .rdx (.imm 0), .store (field 8) .rdx,
  .mov .rdx (.reg .rcx), .shift .shl .rdx 3, .mov .r11 (.reg .rdx), .shift .shl .rdx 2,
  .alu .add .rdx (.reg .r11), .mov .r11 (.reg .rcx), .shift .shl .r11 6,
  .movImm64 .r8 0x0300000000000000, .alu .cmp .r9 (.reg .r8),
  .cmov .e .rdx (.reg .r11), .store (field 11) .rdx]

/-- Zeros at the region in words 12 and 13. -/
def clear : Prog isa := .seq (.block [.mov .rdi (.reg .r12)]) (VG.Impl.Rsa.X86_64.Keys.zeroOut 12 13)

/-- The key's buffer but `p`: `4 p_len` octets from `key`, then from
`key + 5 p_len`. -/
def clearAround : Prog isa := seqs [
  .block [.mov .rax (.mem (field 0)), .store (field 12) .rax, .mov .rcx (.mem (field 1)),
    .shift .shl .rcx 2, .store (field 13) .rcx],
  clear,
  .block [.mov .rax (.mem (field 1)), .mov .rcx (.reg .rax), .shift .shl .rcx 2, .alu .add .rax (.reg .rcx),
    .mov .rcx (.mem (field 0)), .alu .add .rax (.reg .rcx), .store (field 12) .rax, .mov .rcx (.mem (field 1)),
    .shift .shl .rcx 2, .store (field 13) .rcx],
  clear]

/-- The whole key's buffer, `9 p_len` octets. -/
def clearAll : Prog isa := .seq
  (.block [.mov .rax (.mem (field 0)), .store (field 12) .rax, .mov .rcx (.mem (field 1)),
    .mov .rdx (.reg .rcx), .shift .shl .rcx 3, .alu .add .rcx (.reg .rdx), .store (field 13) .rcx])
  clear

/-- The search's arguments: `out` is `key + 4 p_len` for `p`, `key + 5 p_len`
for `q`; `p` is `key + 4 p_len`, of `p_len` octets for `q` and none for `p`;
`e` is the state's last word, of 8 octets; the tape after the octets
consumed. Its stack arguments at the 48 octets the call's frame allocates. -/
def searchArgs : List Instr := [
  .mov .rax (.mem (field 7)), .mov .r10 (.mem (stw 4)),
  .mov .rsi (.mem (field 1)), .mov .r9 (.reg .rsi), .shift .shl .r9 2, .alu .add .r9 (.mem (field 0)),
  .mov .rdi (.reg .r9), .alu .add .rdi (.reg .rsi), .mov32 .r11 (.imm 0),
  .alu .test .r10 (.reg .r10), .cmov .e .rdi (.reg .r9), .cmov .e .rsi (.reg .r11),
  .store { base := .rsp } .rsi, .mov .rsi (.mem (field 1)),
  .mov .rdx (.mem (field 3)), .alu .add .rdx (.mem (field 8)), .store { base := .rsp, disp := 8 } .rdx,
  .mov .rdx (.mem (field 4)), .alu .sub .rdx (.mem (field 8)), .store { base := .rsp, disp := 16 } .rdx,
  .mov .rdx (.mem (field 5)), .store { base := .rsp, disp := 24 } .rdx,
  .mov .rdx (.mem (field 6)), .store { base := .rsp, disp := 32 } .rdx,
  .store { base := .rsp, disp := 40 } .rax,
  .mov .rdx (.mem (field 2)), .mov .rcx (.reg .rax), .alu .add .rcx (.imm 48), .mov32 .r8 (.imm 8)]

/-- The key's arguments: `n`, `d`, `p`, `q`, `dP`, `dQ`, `qInv` at `key + j
p_len` for `j = 0, 2, 4, 5, 6, 7, 8`, `e` the state's last word, and the
working space. Its stack arguments at the 96 octets the call's frame
allocates. -/
def keyArgs : List Instr := [
  .mov .r9 (.mem (field 1)), .mov .rdi (.mem (field 0)),
  .mov .rsi (.reg .r9), .shift .shl .rsi 1, .mov .rdx (.reg .rdi), .alu .add .rdx (.reg .rsi),
  .mov .rcx (.reg .rsi), .mov .r8 (.reg .rdx), .alu .add .r8 (.reg .rsi),
  .mov .rax (.reg .r8), .alu .add .rax (.reg .r9), .store { base := .rsp } .rax,
  .store { base := .rsp, disp := 8 } .r9,
  .alu .add .rax (.reg .r9), .store { base := .rsp, disp := 16 } .rax,
  .store { base := .rsp, disp := 24 } .r9,
  .alu .add .rax (.reg .r9), .store { base := .rsp, disp := 32 } .rax,
  .store { base := .rsp, disp := 40 } .r9,
  .alu .add .rax (.reg .r9), .store { base := .rsp, disp := 48 } .rax,
  .store { base := .rsp, disp := 56 } .r9,
  .mov .rax (.mem (field 7)), .alu .add .rax (.imm 48), .store { base := .rsp, disp := 64 } .rax,
  .mov32 .rax (.imm 8), .store { base := .rsp, disp := 72 } .rax,
  .mov .rax (.mem (field 5)), .store { base := .rsp, disp := 80 } .rax,
  .mov .rax (.mem (field 6)), .store { base := .rsp, disp := 88 } .rax]

variable (search key : Prog isa)

/-- The prime search, in a frame of its stack arguments. -/
def searchRun : Prog isa := .frame (.alloc 48) (.seq (.block searchArgs) search) (.free 48)

/-- The key from the primes, in a frame of its stack arguments. -/
def keyRun : Prog isa := .frame (.alloc 96) (.seq (.block keyArgs) key) (.free 96)

/-- The next prime's search, from all its counted candidates, in `phase`. -/
def nextPrime (phase : Nat) : List Instr := [
  .mov .rax (.mem (field 7)), .mov .rcx (.mem (field 11)), .store (stw 0) .rcx,
  .mov32 .rcx (.imm (BitVec.ofNat 32 phase)), .store (stw 4) .rcx,
  .mov32 .rcx (.imm 4), .store (field 10) .rcx]

/-- The search ends with `status`: no phase or generations left, and zeros
for the key but its status 1. -/
def finishWith (status : Nat) : List Instr := [
  .mov .rax (.mem (field 7)), .mov32 .rcx (.imm 0), .store (stw 4) .rcx, .store (stw 5) .rcx,
  .mov32 .rcx (.imm (BitVec.ofNat 32 status)), .store (field 10) .rcx]

def fail (status : Nat) : Prog isa := .seq clearAll (.block (finishWith status))

/-- A prime's search exhausted: this generation fails; the next, or none. -/
def exhaustedGen : Prog isa := .seq
  (.block [.mov .rax (.mem (field 7)), .mov .rcx (.mem (stw 5)), .alu .cmp .rcx (.imm 2)])
  (.ite .b (fail 3) (.block ([.alu .sub .rcx (.imm 1), .store (stw 5) .rcx] ++ nextPrime 0)))

/-- The key's status, in rax. -/
def afterKey : Prog isa := .seq (.block [.mov32 .rax (.reg .rax), .alu .cmp .rax (.imm 1)])
  (.ite .e (.block (finishWith 1)) (.seq (.block [.alu .cmp .rax (.imm 2)])
    (.ite .e (.block (nextPrime 0)) (fail 2))))

/-- A prime accepted: `q` next, or the key. -/
def accepted : Prog isa := .seq
  (.block [.mov .rax (.mem (field 7)), .mov .rcx (.mem (stw 4)), .alu .test .rcx (.reg .rcx)])
  (.ite .e (.block (nextPrime 1)) (.seq (keyRun key) afterKey))

/-- After the search: its status in rax, the octets it consumed at `used`. -/
def classify : Prog isa := seqs [
  .block [.mov32 .rax (.reg .rax), .mov .rcx (.mem (field 2)), .mov .rcx (.mem { base := .rcx }),
    .mov .rdx (.mem (field 8)), .alu .add .rdx (.reg .rcx), .store (field 8) .rdx,
    .alu .test .rax (.reg .rax)],
  .ite .e (.block [.store (field 10) .rax]) (.seq (.block [.alu .cmp .rax (.imm 3)])
    (.ite .e exhaustedGen (.seq (.block [.alu .test .rcx (.reg .rcx)])
      (.ite .e (fail 3) (accepted key)))))]

def iteration : Prog isa := seqs [
  searchRun search, classify key, .block [.mov .rax (.mem (field 10)), .alu .cmp .rax (.imm 4)]]

/-- The octets consumed to `used`, the status returned and r12 restored. -/
def finish : List Instr := [
  .mov .rax (.mem (field 2)), .mov .rcx (.mem (field 8)), .store { base := .rax } .rcx,
  .mov .rax (.mem (field 10)), .mov .r12 (.mem (field 9))]

def code : Prog isa := .frame (.alloc frameBytes)
  (seqs [.block (entryHead ++ entryWords), clearAround, .loop (iteration search key) .e, .block finish])
  (.free frameBytes)

end VG.Impl.RsaKeyGen.X86_64.Generate
