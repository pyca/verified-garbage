module

public import VerifiedGarbage.Impl.MdStream.PPC64LE

/-!
# PBKDF2-HMAC's iteration over a Merkle–Damgård hash function: PPC64LE implementation

`iterate(key = r3, u = r4, n = r5, t = r6, scratch = r7)` runs `n` steps
`U ← HMAC (K₀, U)`, `T ← T ⊕ U` (`VG.Spec.Pbkdf2.iterate`), for the key
whose inner and outer streaming states are at `key` and `key + N + B`.

The same design as on AArch64 (`Impl/Pbkdf2/AArch64.lean`): it serves every
Merkle–Damgård hash function (MD5, SHA-1, SHA-256 and the SHA-512 family),
from the parameters of its streaming code (`MdStream.PPC64LE.Params`: the
sizes of its hash value, block and length field, and the code storing its
length field and writing its `D`-byte digest) and its compression function (`name`, `code`), with `D` the
size of the digest.

The inner and outer states have each absorbed one block, so HMAC of the
`D`-byte `U` is two compressions, each of one block that is `D` bytes of
message followed by the padding of a `B + D`-byte message: the inner hash
value with the block `U ‖ pad`, then the outer hash value with the block
`digest ‖ pad`. The padding is written once, before the loop: the hash
function's code writes only the `D` bytes of the digest (`out`, as the
streaming `finalize`'s).

`scratch` holds the compression function's scratch space (`[0..so)`), our
caller's `r26`–`r31` (`[so..so+48)`, where the streaming code's `save` and
`restore` keep them), our return address (`[so+48..so+56)`), which each
call replaces, the hash value being compressed (`N` bytes from `so + 56`)
and right after it the block (`B` bytes). So the function uses no stack.
The compression function preserves `r14`–`r31`, so our variables live there,
as the streaming code's do: `r26` = the hash value, `r27` = `scratch`, `r28`
= the block, `r29` = `key` (the byte count of the length field before the
loop), `r30` = `t` and `r31` = the steps left. Every address and branch
depends only on the pointers and `n`.

`n` is a 32-bit argument, whose register's upper half is whatever the caller
left there (possibly secret): the first instructions, which also move our
return address to `r0` for the prologue to save, zero-extend it.
-/

@[expose] public section

namespace VG.Impl.Pbkdf2.PPC64LE

open VG.PPC64LE
open VG.Impl.MdStream.PPC64LE (Params mov save restore compressAt)

/-- Copying 32-bit word `k` from `o₁(src)` to `o₂(dst)`, through `r8`. -/
def cp32 (src dst : Reg) (o₁ o₂ k : Nat) : List Instr :=
  [.load .w .r8 src (o₁ + 4 * k), .store .w .r8 dst (o₂ + 4 * k)]

variable (P : Params) (D : Nat)

/-- Where our return address is saved in `scratch`. -/
def raO : Nat := P.so + 48

/-- Where the hash value being compressed is in `scratch`. -/
def hvO : Nat := P.so + 56

/-- Where the block is. -/
def blkO : Nat := P.so + 56 + P.N

/-- The hash value at `o(key)` into `0(r26)`. -/
def loadKey (o : Nat) : List Instr := (List.range (P.N / 4)).flatMap (cp32 .r29 .r26 o 0)

/-- `0x80` then zeros in the block, from byte `a` up to byte `b` (`a < b`,
both multiples of 4). -/
def padFrom (a b : Nat) : List Instr :=
  ([.li .r8 0x80, .store .w .r8 .r28 a, .li .r8 0] : List Instr) ++
    (List.range ((b - a) / 4 - 1)).map fun k => .store .w .r8 .r28 (a + 4 + 4 * k)

/-- The rest of the block after its first `D` bytes, the end of a
`B + D`-byte message: `0x80`, zeros and the length field, which `P.len`
stores from `r29` at `r26 + N + B - L`, the end of the block at
`r28 = r26 + N`. -/
def padLen : List Instr :=
  padFrom D (P.B - P.L) ++ ([.li .r29 (P.B + D)] : List Instr) ++ P.len

/-- `T ← T ⊕ U` for 32-bit word `k`, with `U` the block's first `D` bytes. -/
def xorW (k : Nat) : List Instr :=
  [.load .w .r8 .r28 (4 * k), .load .w .r9 .r30 (4 * k), .logic .xor .r8 .r8 .r9,
    .store .w .r8 .r30 (4 * k)]

/-- One compression of the block into the hash value. -/
def compressBlock (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block [mov .r4 .r28]) (compressAt name code)

/-- One step. -/
def body (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block (loadKey P 0))
  (.seq (compressBlock name code)
  (.seq (.block (P.out ++ loadKey P (P.N + P.B)))
  (.seq (compressBlock name code)
    (.block (P.out ++ (List.range (D / 4)).flatMap xorW ++ ([.subi .r31 .r31 1] : List Instr))))))

/-- Saving our caller's registers and our return address (from `r0`), setting
up our registers, and writing `U` and the padding into the block (`padLen`). -/
def prologue : List Instr :=
  save P .r7 ++
    ([.store .d .r0 .r7 (raO P), .addi .r26 .r7 (hvO P), mov .r27 .r7,
      .addi .r28 .r7 (blkO P), mov .r30 .r6, mov .r31 .r5] : List Instr) ++
    (List.range (D / 4)).flatMap (cp32 .r4 .r28 0 0) ++ padLen P D ++ [mov .r29 .r3]

/-- Restoring our return address and our caller's registers. -/
def epilogue : List Instr := [.load .d .r0 .r27 (raO P)] ++ restore P ++ [.mtlr .r0]

/-- `iterate`, once `n` is zero-extended. -/
def main (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block (prologue P D))
  (.seq (.ite (.zero .d .r31) (.block []) (.loop (body P D name code) (.nonzero .d .r31)))
    (.block (epilogue P)))

/-- Our return address into `r0`, and `n` zero-extended. -/
def entry : List Instr := [.mflr .r0, .lsl .r5 .r5 32, .lsr .d .r5 .r5 32]

def iterate (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block entry) (main P D name code)

end VG.Impl.Pbkdf2.PPC64LE
