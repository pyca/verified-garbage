module

public import VerifiedGarbage.Impl.Sha256.AArch64
public import VerifiedGarbage.Impl.MdStream.AArch64

/-!
# Streaming SHA-256: AArch64 implementation

The streaming state (96 bytes at `state`) is the hash value followed by a
64-byte buffer (see `VG.Spec.Sha256.Repr`).

* `init(state = x0)` stores `H⁽⁰⁾` (`init224`, SHA-224's).
* `update` and `finalize` are the generic streaming code
  (`Impl/MdStream/AArch64.lean`), calling the compression function
  (`vg_sha256_compress`) with `scratch[0..112)` as its scratch space, and
  saving our caller's `x19`–`x24` in `scratch[112..160)`.

HMAC-SHA-256 and PBKDF2-HMAC-SHA-256 call the compression function the same
way (`saved`, `save`, `restore`, `compressAt`).
-/

@[expose] public section

namespace VG.Impl.Sha256.AArch64.Stream

open VG.AArch64
open VG.Impl.Sha256.AArch64 (compress)

/-- `mov d, n` (as `add d, n, #0`). -/
def mov (d n : Reg) : Instr := .addImm .x d n 0

/-- Stores the initial hash value `iv`. -/
def initWith (iv : Spec.Sha256.HashValue) : Prog isa :=
  .block ((List.range 8).flatMap fun k =>
    [.movz .w .x9 (iv[k]!.extractLsb' 0 16) 0,
     .movk .w .x9 (iv[k]!.extractLsb' 16 16) 1,
     .str .w .x9 .x0 (4 * k)])

/-- `mov d, #v` for a 64-bit constant: a `movz` and three `movk`s. -/
def movImm64 (d : Reg) (v : BitVec 64) : List Instr :=
  [.movz .x d (v.extractLsb' 0 16) 0, .movk .x d (v.extractLsb' 16 16) 1,
   .movk .x d (v.extractLsb' 32 16) 2, .movk .x d (v.extractLsb' 48 16) 3]

/-- `initWith`, storing the hash value sixteen bytes at a time (`stp` of two
words packed in each register), as the SHA-2 compression function loads it
(`ldr q`): for the one-shot digests, whose first compression reads it right
away. -/
def initPairs (iv : Spec.Sha256.HashValue) : Prog isa :=
  .block ((List.range 2).flatMap fun k =>
    movImm64 .x9 (iv[4 * k + 1]! ++ iv[4 * k]!) ++ movImm64 .x10 (iv[4 * k + 3]! ++ iv[4 * k + 2]!) ++
      ([.stp .x9 .x10 .x0 (16 * k)] : List Instr))

/-- `vg_sha256_init`. -/
def init : Prog isa := initWith Spec.Sha256.H0

/-- `vg_sha224_init`. -/
def init224 : Prog isa := initWith Spec.Sha256.H0_224

/-- The callee-saved registers we use, and where they are saved in `scratch`. -/
def saved : List (Reg × Nat) :=
  [(.x19, 112), (.x20, 120), (.x21, 128), (.x22, 136), (.x23, 144), (.x24, 152)]

/-- Save them, with `scratch` in `b`. -/
def save (b : Reg) : List Instr := saved.map fun (r, d) => .str .x r b d

/-- Restore them from `scratch` in `x20` (`x20`, the base, last). -/
def restore : List Instr :=
  (saved.filter (·.1 != .x20)).map (fun (r, d) => .ldr .x r .x20 d) ++ ([.ldr .x .x20 .x20 120] : List Instr)

/-- Compress the block at `x1` into the hash value at `x19`, with scratch
space `x20`. -/
def compressAt : Prog isa :=
  .seq (.block [mov .x0 .x19, .movz .x .x2 1 0, mov .x3 .x20]) (.call "vg_sha256_compress" compress)

/-! ## `update` and `finalize`

The generic streaming code (`Impl/MdStream/AArch64.lean`). -/

def params : MdStream.AArch64.Params where
  N := 32
  B := 64
  L := 8
  so := 112
  len := MdStream.AArch64.len64 88 true
  out := MdStream.AArch64.out32 8 true

def update : Prog isa := MdStream.AArch64.update params "vg_sha256_compress" compress

def finalize : Prog isa := MdStream.AArch64.finalize params "vg_sha256_compress" compress

/-- SHA-224 outputs the first 28 bytes of the final hash value: `params`
with a digest of 7 words. -/
def params224 : MdStream.AArch64.Params := { params with out := MdStream.AArch64.out32 7 true }

end VG.Impl.Sha256.AArch64.Stream
