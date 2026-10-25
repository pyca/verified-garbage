module

public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# PBKDF2-HMAC's iteration over a Merkle–Damgård hash function: RISC-V implementation

`iterate(key = a0, u = a1, n = a2, t = a3, scratch = a4)` runs `n` steps
`U ← HMAC (K₀, U)`, `T ← T ⊕ U` (`VG.Spec.Pbkdf2.iterate`), for the key
whose inner and outer streaming states are at `key` and `key + N + B`.

The design of PPC64LE's (`Impl/Pbkdf2/PPC64LE.lean`): it serves every
Merkle–Damgård hash function (MD5, SHA-1, SHA-256 and the SHA-512 family),
from the sizes of its hash value `N`, block `B` and digest `D`, its
compression function (`cmpN`, `cmpC`, with `CW` bytes of scratch space), the
code writing its `D`-byte digest (`out`, as its streaming `finalize`'s) and
the padding of a `B + D`-byte message after its last `D` bytes (`pad`).

The inner and outer states have each absorbed one block, so HMAC of the
`D`-byte `U` is two compressions, each of one block that is `D` bytes of
message followed by `pad`: the inner hash value with the block `U ‖ pad`,
then the outer hash value with the block `digest ‖ pad`. The padding is
written once, before the loop: `out` writes only the `D` bytes of the
digest.

`scratch` is rounded up to a multiple of 8 (it has room to spare). It holds
the compression function's scratch space (`[0..CW)`), our caller's `ra` and
`s1`–`s6` (`[CW..CW+56)`), the hash value being compressed (`N` bytes from
`CW + 56`) and right after it the block (`B` bytes), so the function uses no
stack. The compression function preserves `s1`–`s11` (it saves and restores
only `s0`), so our variables live there: `s1` = the hash value, `s2` =
`scratch`, `s3` = the block, `s4` = `key`, `s5` = `t` and `s6` = the steps
left. The key, `U` and `T` are argument buffers, whose alignment the
contract does not state, so they are accessed a byte at a time. Every
address and branch depends only on the pointers and `n`.

`n` is a 32-bit argument, which the calling convention sign-extends: the
entry block zero-extends it, in place, before anything else depends on it.
-/

@[expose] public section

namespace VG.Impl.Pbkdf2.RISCV64

open VG.RISCV64

/-- `mv d, n` (`addi d, n, 0`). -/
def mov (d n : Reg) : Instr := .addi d n 0

/-- What the iteration needs of one hash function. -/
structure It where
  /-- The size of the hash value. -/
  N : Nat
  /-- The size of a block. -/
  B : Nat
  /-- The size of the digest. -/
  D : Nat
  /-- The bytes of scratch space of the compression function. -/
  CW : Nat
  cmpN : String
  cmpC : Prog isa
  /-- Writes the digest, from the hash value at `s1`, to `s3`. -/
  out : List Instr
  /-- The bytes of the block after the first `D`: the padding of a
  `B + D`-byte message. -/
  pad : List Nat

namespace It

variable (P : It)

/-- The size of a streaming state. -/
abbrev S : Nat := P.N + P.B

/-- Where we save our caller's registers in `scratch`. -/
def so : Nat := P.CW

/-- Where the hash value being compressed is. -/
def hvO : Nat := P.CW + 56

/-- Where the block is. -/
def blkO : Nat := P.hvO + P.N

/-- The registers we save, and where. -/
def saved : List (Reg × Nat) :=
  [(.ra, P.so), (.s1, P.so + 8), (.s2, P.so + 16), (.s3, P.so + 24), (.s4, P.so + 32),
    (.s5, P.so + 40), (.s6, P.so + 48)]

/-- Where we restore them from, in order (`s2`, the base, last). -/
def restList : List (Reg × Nat) :=
  [(.ra, P.so), (.s1, P.so + 8), (.s3, P.so + 24), (.s4, P.so + 32), (.s5, P.so + 40),
    (.s6, P.so + 48), (.s2, P.so + 16)]

/-- Save them, at the aligned `scratch` in `a4`. -/
def save : List Instr := P.saved.map fun (r, d) => .store .d r .a4 d

/-- Restore them, from `scratch` in `s2`. -/
def restore : List Instr := P.restList.map fun (r, d) => .load .d r .s2 d

/-- `n` bytes copied from `o₁(src)` to `o₂(dst)`, through `t1`. -/
def cp (src dst : Reg) (o₁ o₂ n : Nat) : List Instr :=
  (List.range n).flatMap fun k => [.load .b .t1 src (o₁ + k), .store .b .t1 dst (o₂ + k)]

/-- The padding into the block after its first `D` bytes. -/
def padCode : List Instr :=
  (List.range P.pad.length).flatMap fun i => [.li .t1 (P.pad.getD i 0), .store .b .t1 .s3 (P.D + i)]

/-- Align `scratch`, save our caller's registers, set up ours, and lay out
the block: `U`, then the padding. -/
def prologue : List Instr :=
  [.addi .a4 .a4 7, .logicImm .and .a4 .a4 (-8)] ++ P.save ++
    [mov .s2 .a4, .addi .s1 .a4 P.hvO, .addi .s3 .a4 P.blkO, mov .s4 .a0, mov .s5 .a3,
      mov .s6 .a2] ++
    cp .a1 .s3 0 0 P.D ++ P.padCode

/-- Compress the block into the hash value. -/
def compressAt : Prog isa :=
  .seq (.block [mov .a0 .s1, mov .a1 .s3, .li .a2 1, mov .a3 .s2]) (.call P.cmpN P.cmpC)

/-- `T ← T ⊕ U`, with `U` the block's first `D` bytes. -/
def xorT : List Instr :=
  (List.range P.D).flatMap fun k =>
    [.load .b .t1 .s5 k, .load .b .t2 .s3 k, .logic .xor .t1 .t1 .t2, .store .b .t1 .s5 k]

/-- One step: the inner hash, then the outer one, each written over the
block's first `D` bytes, then `T ← T ⊕ U`. -/
def body : Prog isa :=
  .seq (.block (cp .s4 .s1 0 0 P.N))
  (.seq P.compressAt
  (.seq (.block (P.out ++ cp .s4 .s1 P.S 0 P.N))
  (.seq P.compressAt
    (.block (P.out ++ P.xorT ++ [.addi .s6 .s6 (-1)])))))

def main : Prog isa :=
  .seq (.block P.prologue)
  (.seq (.ite (.zero .s6) (.block []) (.loop P.body (.nonzero .s6)))
    (.block P.restore))

/-- `n` zero-extended. -/
def entry : List Instr := [.shift .sll .d .a2 .a2 32, .shift .srl .d .a2 .a2 32]

def iterate : Prog isa := .seq (.block entry) P.main

end It

/-- The padding of a `B + D`-byte message after its last `D` bytes, with an
`L`-byte length field: `0x80`, zeros, and the message's length in bits,
big-endian (`padBE`) or little-endian (`padLE`). -/
def padBE (B D L : Nat) : List Nat :=
  0x80 :: List.replicate (B - L - 1 - D) 0 ++ (List.range L).reverse.map fun i => 8 * (B + D) / 256 ^ i % 256

def padLE (B D L : Nat) : List Nat :=
  0x80 :: List.replicate (B - L - 1 - D) 0 ++ (List.range L).map fun i => 8 * (B + D) / 256 ^ i % 256

end VG.Impl.Pbkdf2.RISCV64
