module

public import VerifiedGarbage.Impl.Mont.X86.Compact
public import VerifiedGarbage.Impl.Bignum.X86.PublicRt

/-! # RSA key generation over refillable random tapes on i686

`vg_rsa_generate(key, key_len, used, rand, rand_len, scratch, scratch_len,
state)`, all on the stack (`VG.Spec.RsaKeyGen.keySearch`), as on x86-64
(`Impl/RsaKeyGen/X86_64/Generate.lean`) and AArch64: calls the prime search
(`vg_rsa_prime_search`) on the rest of the tape for `p`, then `q` against
`p`, and the key from them (`vg_rsa_keygen_key`), until a key is found, a
check fails, every generation is exhausted, or the tape runs out. The
search's progress is in `state` (the prime search's four words, the phase
and the generations left) and, for `q`'s search, `p` in the key's buffer.

As the prime search does (`Impl/RsaKeyGen/X86/Search.lean`), the controller's
own state is in the callee-saved registers, which both callees keep: the
octets consumed in `esi`, the status in `ebx` (4 while the search goes on),
the counted candidates each prime's search starts with in `edi`, and the
primes' octets `p_len` in `ebp`. It saves them in a frame of 16 bytes; the
pointers and lengths it reads from its own stack arguments each time, and
passes each call's in a frame of its arguments. The state's `u64` words are
read and written as their halves; the generations left, which the caller
may give as any 64-bit value, as both.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.X86.Generate

open VG VG.X86
open VG.Impl.Mont.X86 (at_)
open VG.Impl.Bignum.X86.PublicRt (argAt)

/-- The words the controller pushes. -/
def pushWords : Nat := 4

/-- The words of the prime search's arguments, and of the key's. -/
def searchWords : Nat := 12
def keyWords : Nat := 18

/-- The controller's argument `i` (`key, key_len, used, rand, rand_len,
scratch, scratch_len, state`), below `extra` more words of frame than its
own. -/
def param (extra i : Nat) : MemOp := argAt (pushWords + extra) i

/-- `[eax + d]`: the state's bytes from `d`, its pointer in `eax`. -/
def st (d : Nat) : MemOp := at_ .eax d

/-- `p_len`, nothing consumed, the search goes on, and the counted
candidates of a prime's search: `40 p_len`, or `64 p_len` for an exponent of
3 (its eight octets, most significant first: the low half zero and the high
half `3 · 2^24`), from the mask `ecx` of `e = 3`. -/
def entry : List Instr :=
  [.mov .eax (.mem (param 0 7)), .mov .ebp (.mem (st 8)), .mov .esi (.imm 0), .mov .ebx (.imm 4),
    .mov .ecx (.mem (st 52)), .alu .xor .ecx (.imm 0x03000000), .alu .or .ecx (.mem (st 48)),
    .alu .cmp .ecx (.imm 1), .alu .sbb .ecx (.reg .ecx),
    .mov .edx (.reg .ebp), .alu .add .edx (.reg .edx), .alu .add .edx (.reg .edx), .alu .add .edx (.reg .edx),
    .mov .edi (.reg .edx), .alu .add .edi (.reg .edi), .alu .add .edi (.reg .edx), .alu .and .edi (.reg .ecx),
    .mov .eax (.imm 40), .mul .ebp, .alu .add .edi (.reg .eax)]

/-- `ecx` zeros from `edx` (at least one), `eax` zero. -/
def zeroLoop : Prog isa :=
  .loop (.block [.store8 (at_ .edx 0) .al, .alu .add .edx (.imm 1), .alu .sub .ecx (.imm 1)]) .ne

/-- `ecx := 4 p_len`. -/
def four : List Instr := [.mov .ecx (.reg .ebp), .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx)]

/-- The key's buffer but `p`: `4 p_len` octets from `key`, then from
`key + 5 p_len`. -/
def clearAround : Prog isa :=
  .seq (.seq (.block ([.mov .edx (.mem (param 0 0))] ++ four ++ [.mov .eax (.imm 0)])) zeroLoop)
    (.seq (.block ([.mov .edx (.mem (param 0 0))] ++ four ++ [.alu .add .edx (.reg .ecx),
      .alu .add .edx (.reg .ebp), .mov .eax (.imm 0)])) zeroLoop)

/-- The whole key's buffer, `9 p_len` octets. -/
def clearAll : Prog isa := .seq
  (.block ([.mov .edx (.mem (param 0 0))] ++ four ++ [.alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ebp),
    .mov .eax (.imm 0)]))
  zeroLoop

/-- The search's arguments: `out` is `key + 4 p_len` for `p`, `key + 5 p_len`
for `q` (the phase, the state's word 4, is 0 or 1: its negation masks
`p_len`); `p` is `key + 4 p_len`, of `p_len` octets for `q` and none for `p`;
`e` the state's last word, of 8 octets; the tape after the octets consumed,
at `rand` itself when none are left (`rand + rand_len` may wrap to 0, which
no region holds: `edx` all ones when the length left is 0 masks `used`).
In the call's frame of arguments. -/
def searchArgs : List Instr :=
  [.mov .eax (.mem (param searchWords 7)), .mov .ecx (.mem (st 32)), .mov .edx (.imm 0),
    .alu .sub .edx (.reg .ecx), .alu .and .edx (.reg .ebp), .store (at_ .esp 24) .edx,
    .mov .ecx (.reg .ebp), .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx),
    .alu .add .ecx (.mem (param searchWords 0)), .store (at_ .esp 20) .ecx, .alu .add .ecx (.reg .edx),
    .store (at_ .esp 0) .ecx, .store (at_ .esp 4) .ebp,
    .mov .ecx (.mem (param searchWords 2)), .store (at_ .esp 8) .ecx,
    .mov .ecx (.reg .eax), .alu .add .ecx (.imm 48), .store (at_ .esp 12) .ecx,
    .mov .ecx (.imm 8), .store (at_ .esp 16) .ecx,
    .mov .ecx (.mem (param searchWords 4)), .alu .sub .ecx (.reg .esi), .store (at_ .esp 32) .ecx,
    .alu .cmp .ecx (.imm 1), .alu .sbb .edx (.reg .edx), .alu .and .edx (.reg .esi),
    .mov .ecx (.mem (param searchWords 3)), .alu .add .ecx (.reg .esi), .alu .sub .ecx (.reg .edx),
    .store (at_ .esp 28) .ecx,
    .mov .ecx (.mem (param searchWords 5)), .store (at_ .esp 36) .ecx,
    .mov .ecx (.mem (param searchWords 6)), .store (at_ .esp 40) .ecx,
    .store (at_ .esp 44) .eax]

/-- The key's arguments: `n`, `d`, `p`, `q`, `dP`, `dQ`, `qInv` at `key + j
p_len` for `j = 0, 2, 4, 5, 6, 7, 8`, of `2 p_len` octets for `n` and `d`
and `p_len` for the others; `e` the state's last word, of 8 octets; the
working space. In the call's frame of arguments. -/
def keyArgs : List Instr :=
  [.mov .ecx (.mem (param keyWords 0)), .mov .edx (.reg .ebp), .alu .add .edx (.reg .edx),
    .store (at_ .esp 0) .ecx, .store (at_ .esp 4) .edx, .alu .add .ecx (.reg .edx),
    .store (at_ .esp 8) .ecx, .store (at_ .esp 12) .edx, .alu .add .ecx (.reg .edx),
    .store (at_ .esp 16) .ecx, .store (at_ .esp 20) .ebp, .alu .add .ecx (.reg .ebp),
    .store (at_ .esp 24) .ecx, .store (at_ .esp 28) .ebp, .alu .add .ecx (.reg .ebp),
    .store (at_ .esp 32) .ecx, .store (at_ .esp 36) .ebp, .alu .add .ecx (.reg .ebp),
    .store (at_ .esp 40) .ecx, .store (at_ .esp 44) .ebp, .alu .add .ecx (.reg .ebp),
    .store (at_ .esp 48) .ecx, .store (at_ .esp 52) .ebp,
    .mov .ecx (.mem (param keyWords 7)), .alu .add .ecx (.imm 48), .store (at_ .esp 56) .ecx,
    .mov .ecx (.imm 8), .store (at_ .esp 60) .ecx,
    .mov .ecx (.mem (param keyWords 5)), .store (at_ .esp 64) .ecx,
    .mov .ecx (.mem (param keyWords 6)), .store (at_ .esp 68) .ecx]

variable (search key : Prog isa)

/-- The prime search, in a frame of its arguments. -/
def searchRun : Prog isa :=
  .frame (.alloc (4 * searchWords)) (.seq (.block searchArgs) search) (.free (4 * searchWords))

/-- The key from the primes, in a frame of its arguments. -/
def keyRun : Prog isa :=
  .frame (.alloc (4 * keyWords)) (.seq (.block keyArgs) key) (.free (4 * keyWords))

/-- The next prime's search, from all its counted candidates, in `phase`. -/
def nextPrime (phase : Nat) : List Instr :=
  [.mov .eax (.mem (param 0 7)), .store (st 0) .edi, .mov .ecx (.imm 0), .store (st 4) .ecx,
    .mov .ecx (.imm (BitVec.ofNat 32 phase)), .store (st 32) .ecx, .mov .ebx (.imm 4)]

/-- The search ends with `status`: no phase or generations left. -/
def finishWith (status : Nat) : List Instr :=
  [.mov .eax (.mem (param 0 7)), .mov .ecx (.imm 0), .store (st 32) .ecx, .store (st 36) .ecx,
    .store (st 40) .ecx, .store (st 44) .ecx, .mov .ebx (.imm (BitVec.ofNat 32 status))]

/-- Zeros for the key, and the search ends with `status`. -/
def fail (status : Nat) : Prog isa := .seq clearAll (.block (finishWith status))

/-- A prime's search exhausted: this generation fails; the next one, if at
least two generations are left (the 64-bit word, its halves: `ecx` all ones
when the high half is zero and the low below 2), or none. -/
def exhaustedGen : Prog isa := .seq
  (.block [.mov .eax (.mem (param 0 7)), .mov .ecx (.mem (st 44)), .alu .cmp .ecx (.imm 1),
    .alu .sbb .ecx (.reg .ecx), .mov .edx (.mem (st 40)), .alu .cmp .edx (.imm 2), .alu .sbb .edx (.reg .edx),
    .alu .and .ecx (.reg .edx), .alu .test .ecx (.reg .ecx)])
  (.ite .ne (fail 3)
    (.block ([.mov .ecx (.mem (st 40)), .alu .sub .ecx (.imm 1), .store (st 40) .ecx,
      .mov .ecx (.mem (st 44)), .alu .sbb .ecx (.imm 0), .store (st 44) .ecx] ++ nextPrime 0)))

/-- The key's status, in `eax`: 1 a key, 2 a `d` too small (both primes
again), otherwise a failed check. -/
def afterKey : Prog isa := .seq (.block [.alu .cmp .eax (.imm 1)])
  (.ite .e (.block (finishWith 1)) (.seq (.block [.alu .cmp .eax (.imm 2)])
    (.ite .e (.block (nextPrime 0)) (fail 2))))

/-- A prime accepted: `q` next, or the key. -/
def accepted : Prog isa := .seq (.block [.mov .eax (.mem (param 0 7)), .mov .ecx (.mem (st 32)),
    .alu .cmp .ecx (.imm 0)])
  (.ite .e (.block (nextPrime 1)) (.seq (keyRun key) afterKey))

/-- After the search: its status in `eax`, the octets it consumed (the low
half of `used`) added to `esi`, in `ecx`. Status 0 stops for more entropy;
3, the generation exhausted; otherwise (1) a prime, unless it consumed
nothing. -/
def classify : Prog isa :=
  .seq (.block [.mov .edx (.mem (param 0 2)), .mov .ecx (.mem (at_ .edx 0)), .alu .add .esi (.reg .ecx),
    .alu .cmp .eax (.imm 0)])
  (.ite .e (.block [.mov .ebx (.imm 0)]) (.seq (.block [.alu .cmp .eax (.imm 3)])
    (.ite .e exhaustedGen (.seq (.block [.alu .cmp .ecx (.imm 0)]) (.ite .e (fail 3) (accepted key))))))

/-- The loop goes on while the status is 4. -/
def iteration : Prog isa := .seq (searchRun search) (.seq (classify key) (.block [.alu .cmp .ebx (.imm 4)]))

/-- The octets consumed to `used` (64 bits), the status returned. -/
def results : List Instr :=
  [.mov .edx (.mem (param 0 2)), .store (at_ .edx 0) .esi, .mov .ecx (.imm 0), .store (at_ .edx 4) .ecx,
    .mov .eax (.reg .ebx)]

/-- The results, then the callee-saved registers but `ebx`, which the
frame's pop restores. -/
def finish : List Instr := results ++ Impl.Mont.X86.Compact.restoreRegs

def body : Prog isa :=
  .seq (.block entry) (.seq clearAround (.seq (.loop (iteration search key) .e) (.block finish)))

def code : Prog isa :=
  .frame (.push [.ebx, .ebp, .esi, .edi]) (body search key) (.pop .ebx pushWords)

end VG.Impl.RsaKeyGen.X86.Generate
