module

public import VerifiedGarbage.Impl.MdStream.PPC64LE
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# HMAC over any streaming hash function: PPC64LE implementation

One implementation of HMAC's `init` and `finalize` for every Merkle–Damgård
hash function with verified PPC64LE streaming functions (MD5, SHA-1, the
SHA-256 and SHA-512 families), which only calls them: a `Hash` is a hash
function's streaming `init`, `update` and `finalize`, with their names and
the sizes the code needs (the block `B`, the hash value at the start of the
streaming state `N`, the digest `D`, the bytes `FD` its `finalize` writes,
of which the digest is the first, and the working space `W` of `update`
and `finalize`).

* `init(inner = r3, outer = r4, key = r5, key_len = r6, scratch = r7)`, for a
  key of at most a block, sets each state's hash value with the streaming
  `init`; writes `K₀ ⊕ ipad` into the outer state's buffer (which a state
  representing the empty message does not use) and absorbs it into the inner
  state with `update`; then writes `K₀ ⊕ opad` into the inner state's buffer
  (which a state representing a whole block does not use) and absorbs it
  into the outer state. Each block is the key's bytes XORed with the pad
  byte, then the pad byte up to `B` bytes.
* `finalize(inner = r3, outer = r4, count = r5, out = r6, scratch = r7)`
  finalizes the inner state into `scratch`, copies the outer state's hash
  value over the inner one's (the inner state then represents the outer
  block, whose buffer is empty), absorbs the inner digest with `update`,
  finalizes again into `scratch`, and copies the digest to `out`.
* `initLong`, for a key longer than a block, hashes the key with the
  streaming functions into its scratch space and calls `init` with the
  digest; `initAny` chooses between the two on entry.

`scratch` holds the working space of the functions we call (`W` bytes),
then our caller's `r20`–`r25` (`save`), then what `finalize` writes (`FD`
bytes).
The functions we call save and restore `r26`–`r31` (and SHA-2's `r14`–`r19`),
and a register restored from memory is secret to the analysis of constant
time, so our variables live in `r20`–`r25`, which none of them writes: `r20` = `inner`, `r21` = `scratch`, `r22` = `outer`, and `r23`
and `r24` the key and its length (`init`) or `r23` = `out` (`finalize`).
Each function moves the link register to `r0` and saves it in a frame around
the whole function. Every address and branch depends only on the pointers
and the lengths.
-/

@[expose] public section

namespace VG.Impl.Hmac.Stream.PPC64LE

open VG.PPC64LE
open VG.Impl.MdStream.PPC64LE (mov)

/-- A streaming hash function's PPC64LE functions, as HMAC calls them: the
block size `B`, the size `N` of the hash value at the start of the
streaming state (whose buffer follows it), the size `D` of the digest, the
bytes `FD` that `finalize` writes (SHA-384's and SHA-512/t's are those of
SHA-512's `finalize`, whose first `D` are their digest), the bytes of working space `W` of `update` and
`finalize`, the three functions with their names, and the name of HMAC's
`init` with its working space as an argument (which `initLong` calls). -/
structure Hash where
  B : Nat
  N : Nat
  D : Nat
  FD : Nat
  W : Nat
  initN : String
  initC : Prog isa
  updN : String
  updC : Prog isa
  finN : String
  finC : Prog isa
  hmacInitN : String

namespace Hash

variable (H : Hash)

/-- The size of the streaming state. -/
abbrev S : Nat := H.N + H.B

/-- Where we save our caller's `r20`–`r25`, at `so(b)`. -/
def savedAt (so : Nat) : List (Reg × Nat) :=
  [(.r20, so), (.r21, so + 8), (.r22, so + 16), (.r23, so + 24), (.r24, so + 32), (.r25, so + 40)]

/-- Save them at `so(b)`. -/
def saveAt (so : Nat) (b : Reg) : List Instr := (savedAt so).map fun (r, d) => .store .d r b d

/-- Restore them from `so(r21)` (`r21`, the base, last). -/
def restoreAt (so : Nat) : List Instr :=
  [.load .d .r20 .r21 so, .load .d .r22 .r21 (so + 16), .load .d .r23 .r21 (so + 24),
    .load .d .r24 .r21 (so + 32), .load .d .r25 .r21 (so + 40), .load .d .r21 .r21 (so + 8)]

/-- Save our caller's `r20`–`r25` in `scratch[W..W + 48)`, with `scratch` in `b`. -/
def save (b : Reg) : List Instr := Hash.saveAt H.W b

/-- Restore them from `scratch` in `r21`. -/
def restore : List Instr := Hash.restoreAt H.W

/-- Where `finalize` keeps the inner digest in `scratch`. -/
def dig : Nat := H.W + 48

/-- A call of the streaming `init`. -/
def callInit : Prog isa := .call H.initN H.initC

/-- A call of the streaming `update`. -/
def callUpd : Prog isa := .call H.updN H.updC

/-- A call of the streaming `finalize`. -/
def callFin : Prog isa := .call H.finN H.finC

/-! ## `init` -/

/-- The key bytes (`r9` points at the next, `r10` counts those left), XORed
with the pad byte `r12`, into the buffer of the state at `dst` (byte `r25`
at `N(r11)`, `r11 = dst + r25`). -/
def keyLoop (dst : Reg) : Prog isa :=
  .loop (.block [.lbz .r8 .r9 0, .logic .xor .r8 .r8 .r12, .add .r11 dst .r25, .stb .r8 .r11 H.N,
    .addi .r9 .r9 1, .addi .r25 .r25 1, .subi .r10 .r10 1]) (.nonzero .d .r10)

/-- The pad byte into the rest of the buffer (`r10` bytes). -/
def padLoop (dst : Reg) : Prog isa :=
  .loop (.block [.add .r11 dst .r25, .stb .r12 .r11 H.N, .addi .r25 .r25 1, .subi .r10 .r10 1])
    (.nonzero .d .r10)

/-- `K₀ ⊕ c` into the buffer of the state at `dst`: the key's bytes (at
`r23`, `r24` of them) XORed with `c`, then `c` up to a block. -/
def padKey (dst : Reg) (c : Nat) : Prog isa :=
  .seq (.block [.li .r12 c, .li .r25 0, mov .r9 .r23, mov .r10 .r24])
  (.seq (.ite (.zero .d .r10) (.block []) (H.keyLoop dst))
  (.seq (.block [.li .r10 H.B, .sub .r10 .r10 .r25])
    (.ite (.zero .d .r10) (.block []) (H.padLoop dst))))

/-- `update` of the state at `st` with the block in the buffer of the one at
`src`, from a `count` of 0. -/
def updBlock (st src : Reg) : Prog isa :=
  .seq (.block [mov .r3 st, .li .r4 0, .addi .r5 src H.N, .li .r6 H.B, mov .r7 .r21]) H.callUpd

/-- `init`, but for saving the link register. -/
def initMain : Prog isa :=
  .seq (.block (H.save .r7 ++ [mov .r20 .r3, mov .r21 .r7, mov .r22 .r4, mov .r23 .r5, mov .r24 .r6]))
  (.seq H.callInit
  (.seq (.block [mov .r3 .r22])
  (.seq H.callInit
  (.seq (H.padKey .r22 0x36)
  (.seq (H.updBlock .r20 .r22)
  (.seq (H.padKey .r20 0x5c)
  (.seq (H.updBlock .r22 .r20)
    (.block H.restore))))))))

/-- HMAC's `init` with its working space as an argument. -/
def init : Prog isa :=
  .seq (.block [.mflr .r0]) (.seq (.frame (.push .r0) H.initMain (.pop .r0)) (.block [.mtlr .r0]))

/-! ## `finalize` -/

/-- Copying 32-bit word `k` from `o₁(src)` to `o₂(dst)`. -/
def cp32 (src dst : Reg) (o₁ o₂ k : Nat) : List Instr :=
  [.load .w .r8 src (o₁ + 4 * k), .store .w .r8 dst (o₂ + 4 * k)]

/-- The outer state's hash value over the inner one's. -/
def copyHV : List Instr := (List.range (H.N / 4)).flatMap (cp32 .r22 .r20 0 0)

/-- The digest from `scratch[dig..)` to `out`. -/
def copyOut : List Instr := (List.range (H.D / 4)).flatMap (cp32 .r21 .r23 H.dig 0)

/-- `finalize`, but for saving the link register. -/
def finalizeMain : Prog isa :=
  .seq (.block (H.save .r7 ++ [mov .r20 .r3, mov .r21 .r7, mov .r22 .r4, mov .r23 .r6,
      mov .r4 .r5, .addi .r5 .r7 H.dig, mov .r6 .r7]))
  (.seq H.callFin
  (.seq (.block (H.copyHV ++ [mov .r3 .r20, .li .r4 H.B, .addi .r5 .r21 H.dig, .li .r6 H.D, mov .r7 .r21]))
  (.seq H.callUpd
  (.seq (.block [mov .r3 .r20, .li .r4 (H.B + H.D), .addi .r5 .r21 H.dig, mov .r6 .r21])
  (.seq H.callFin
    (.block (H.copyOut ++ H.restore)))))))

/-- HMAC's `finalize` with its working space as an argument. -/
def finalize : Prog isa :=
  .seq (.block [.mflr .r0]) (.seq (.frame (.push .r0) H.finalizeMain (.pop .r0)) (.block [.mtlr .r0]))

/-! ## `init` for a key of any length

`initLong(inner = r3, outer = r4, key = r5, key_len = r6, scratch = r7)`,
for a key longer than a block. Its scratch space: `scratch[0..W + 48)` is
that of `init`, which it calls, then the streaming state the key is hashed
in (`lst`), its digest (`ldg`), and our caller's `r20`–`r25` (`lsv`). Across
the streaming functions' calls, `r20` = that streaming state, `r21` =
`scratch`, `r22` = `inner`, `r23` = `outer`, `r24` = `key_len` and `r25` =
`key`. It restores our caller's registers before it calls `init` (which
saves and restores them itself), since every register `init` restores is
secret to the analysis of constant time afterwards. -/

/-- Where `initLong` hashes the key in `scratch`. -/
def lst : Nat := H.W + 48

/-- Where the key's digest goes. -/
def ldg : Nat := H.lst + H.S

/-- Where our caller's `r20`–`r25` are saved (8-byte aligned). -/
def lsv : Nat := (H.ldg + H.FD + 7) / 8 * 8

/-- The bytes of `initLong`'s working space. -/
def lbytes : Nat := H.lsv + 48

/-- A call of HMAC's `init` with its working space as an argument. -/
def callHmacInit : Prog isa := .call H.hmacInitN H.init

/-- `initLong`, but for saving the link register. -/
def initLongMain : Prog isa :=
  .seq (.block (Hash.saveAt H.lsv .r7 ++
      [mov .r21 .r7, mov .r22 .r3, mov .r23 .r4, mov .r24 .r6, mov .r25 .r5, .addi .r20 .r7 H.lst,
        mov .r3 .r20]))
  (.seq H.callInit
  (.seq (.block [mov .r3 .r20, .li .r4 0, mov .r5 .r25, mov .r6 .r24, mov .r7 .r21])
  (.seq H.callUpd
  (.seq (.block [mov .r3 .r20, mov .r4 .r24, .addi .r5 .r21 H.ldg, mov .r6 .r21])
  (.seq H.callFin
  (.seq (.block ([mov .r3 .r22, mov .r4 .r23, .addi .r5 .r21 H.ldg, .li .r6 H.D, mov .r7 .r21] ++
      Hash.restoreAt H.lsv))
    H.callHmacInit))))))

def initLong : Prog isa :=
  .seq (.block [.mflr .r0]) (.seq (.frame (.push .r0) H.initLongMain (.pop .r0)) (.block [.mtlr .r0]))

/-- Sets `r12` to a nonzero value exactly when `key_len` (`r6`) is more
than `B = 2 ^ b`: `key_len >> (b + 1)` (nonzero from `2 B`) plus
`((key_len & (2 B - 1)) + B - 1) >> (b + 1)` (1 from `B + 1` to `2 B - 1`).
It writes only `r11` and `r12`, and no memory. -/
def entryCmp (b : Nat) : List Instr :=
  [.lsr .d .r12 .r6 (b + 1), .li .r11 (2 ^ (b + 1) - 1), .logic .and .r11 .r6 .r11,
    .addi .r11 .r11 (2 ^ b - 1), .lsr .d .r11 .r11 (b + 1), .add .r12 .r12 .r11]

/-- Runs `long` for a key longer than a block of `2 ^ b` bytes, out of line,
and `short` otherwise. -/
def initEntry (b : Nat) (short long : Prog isa) : Prog isa :=
  .seq (.block (entryCmp b)) (Code.iteCold (.nonzero .d .r12) long short)

end Hash

end VG.Impl.Hmac.Stream.PPC64LE
