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

/-- The table of the initial hash value `iv`: its words in pairs, as `ldr q`
loads them, word `0` lowest. -/
def ivTable (iv : Spec.Sha256.HashValue) : List (BitVec 64) :=
  [iv[1] ++ iv[0], iv[3] ++ iv[2], iv[5] ++ iv[4], iv[7] ++ iv[6]]

/-- The name of the table of `iv`: SHA-224's initial hash value's, or SHA-256's. -/
def ivName (iv : Spec.Sha256.HashValue) : String :=
  if iv = Spec.Sha256.H0_224 then "VG_SHA224_H0" else "VG_SHA256_H0"

/-- Stores the initial hash value `iv`, sixteen bytes at a time, loaded from
its table (`ldrqTbl`) through `v0` and `v1`: six instructions, where building
it in general registers took two (`movz`, `movk`) for each word. The SHA-2
compression function loads the hash value the same way (`ldr q`), so the
one-shot digests' first compression finds it right away. -/
def initQ (iv : Spec.Sha256.HashValue) : Prog isa :=
  .block [.adrSym .x9 (ivName iv), .ldrqTbl .v0 .x9 0 (ivName iv) (ivTable iv),
    .ldrqTbl .v1 .x9 16 (ivName iv) (ivTable iv), .strq .v0 .x0 0, .strq .v1 .x0 16]

/-- `vg_sha256_init`. -/
def init : Prog isa := initQ Spec.Sha256.H0

/-- `vg_sha224_init`. -/
def init224 : Prog isa := initQ Spec.Sha256.H0_224

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

/-- The digest: the 8 words of the hash value at `x19`, written to `x21`
big-endian, sixteen bytes at a time through `v0` and `v1` (`ldr q`, `rev32`,
`str q`), where `out32 8 true` takes three instructions a word. -/
def out256 : List Instr :=
  [.ldrq .v0 .x19 0, .ldrq .v1 .x19 16, .vop (.rev .rev32b .v0 .v0), .vop (.rev .rev32b .v1 .v1),
   .strq .v0 .x21 0, .strq .v1 .x21 16]

def params : MdStream.AArch64.Params where
  N := 32
  B := 64
  L := 8
  so := 112
  len := MdStream.AArch64.len64 88 true
  out := out256

def update : Prog isa := MdStream.AArch64.update params "vg_sha256_compress" compress

def finalize : Prog isa := MdStream.AArch64.finalize params "vg_sha256_compress" compress

/-- SHA-224 outputs the first 28 bytes of the final hash value: `params`
with a digest of 7 words. -/
def params224 : MdStream.AArch64.Params := { params with out := MdStream.AArch64.out32 7 true }

end VG.Impl.Sha256.AArch64.Stream
