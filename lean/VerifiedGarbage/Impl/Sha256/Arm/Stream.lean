module

public import VerifiedGarbage.Impl.Sha256.Arm
public import VerifiedGarbage.Impl.MdStream.Arm
public import VerifiedGarbage.Impl.MdStream.Arm.Digest
public import VerifiedGarbage.Impl.Scrub.Arm
public import VerifiedGarbage.Impl.Scrub.Arm.Sel

/-!
# Streaming SHA-256: 32-bit ARM implementation

The streaming state (96 bytes at `state`) is the hash value followed by a
64-byte buffer (see `VG.Spec.Sha256.Repr`).

* `init(state = r0)` stores the initial hash value (`init224`, SHA-224's).
* `update` and `finalize` are the generic streaming code
  (`Impl/MdStream/Arm.lean`), calling the compression function
  (`vg_sha256_compress`) with `scratch[0..112)` as its scratch space, and saving our
  caller's `r4`–`r11` and `lr` in `scratch[112..148)`.

HMAC-SHA-256 and PBKDF2-HMAC-SHA-256 call the compression function the same
way (`saved`, `save`, `restore`, `compressAt`).
-/

@[expose] public section

namespace VG.Impl.Sha256.Arm.Stream

open VG.Arm
open VG.Impl.Sha256.Arm (compress)

/-- Stores the initial hash value `iv`. -/
def initWith (iv : Spec.Sha256.HashValue) : Prog isa :=
  .block ((List.range 8).flatMap fun k =>
    [.movw .r12 (iv[k]!.extractLsb' 0 16),
     .movt .r12 (iv[k]!.extractLsb' 16 16),
     .str .r12 .r0 (4 * k)])

/-- `vg_sha256_init`. -/
def init : Prog isa := initWith Spec.Sha256.H0

/-- `vg_sha224_init`. -/
def init224 : Prog isa := initWith Spec.Sha256.H0_224

/-! ## `update` and `finalize`

The generic streaming code (`Impl/MdStream/Arm.lean`). -/

def params : MdStream.Arm.Params where
  N := 32
  B := 64
  L := 8
  so := 112
  len := MdStream.Arm.len64 88 true
  out := MdStream.Arm.out32 8 true

def update : Prog isa := MdStream.Arm.update params "vg_sha256_compress" compress

def finalize : Prog isa := MdStream.Arm.finalize params "vg_sha256_compress" compress

/-- SHA-224 outputs the first 28 bytes of the final hash value: `params`
with a digest of 7 words. -/
def params224 : MdStream.Arm.Params := { params with out := MdStream.Arm.out32 7 true }

/-- SHA-224's `finalize`, writing its digest. -/
def finalize224 : Prog isa := MdStream.Arm.finalize params224 "vg_sha256_compress" compress

/-- SHA-256's streaming functions as HMAC, PBKDF2 and the one-shot digest call
them (`Impl.Pbkdf2.Stream.Arm.Hash`): a 96-byte streaming state, 20 words of
working space and a 32-byte digest, under internal names. -/
def streamFns : Impl.Pbkdf2.Stream.Arm.Hash := ⟨64, 96, 32, 32, 20, "vg_sha256_init_core", init,
  "vg_sha256_update_scratch", update, "vg_sha256_finalize_scratch", finalize⟩

/-- SHA-224's, as `streamFns` but for its initial hash value and its digest,
the first 28 of the 32 bytes `finalize` writes. -/
def streamFns224 : Impl.Pbkdf2.Stream.Arm.Hash := ⟨64, 96, 28, 32, 20, "vg_sha224_init_core", init224,
  "vg_sha256_update_scratch", update, "vg_sha256_finalize_scratch", finalize⟩

end VG.Impl.Sha256.Arm.Stream

/-! ## The functions as emitted

Each is its code, then its cleanup (`Impl/Scrub/Arm.lean`): the registers
a callee may change set to constants, and first, for `update` and
`finalize`, the 176 bytes of the stack of their contract, their frame
(`withStackScratch`), zeroed. `digest` wipes its own working space
(`withRegScratchWiped`), and its cleanup zeroes only the words of its stack
that the residue analysis (`Arm.rtaint`) finds may differ between two runs
(`Impl/Scrub/Arm/Sel.lean`, `scrubSel`, `digestWords`, offsets in words from
the lowest address of that stack). None returns a value. -/

namespace VG.Impl.Sha256.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm

/-- `vg_sha224_init`. -/
def init224 : Prog isa := scrub 0 Stream.init224

/-- `vg_sha256_init`. -/
def init : Prog isa := scrub 0 Stream.init

/-- `vg_sha256_update`, which SHA-224 shares. -/
def update : Prog isa := scrubAll 0 176 (Impl.StackScratch.Arm.withStackScratch 176 2 Stream.update)

/-- `vg_sha256_finalize`. -/
def finalize : Prog isa := scrubAll 0 176 (Impl.StackScratch.Arm.withStackScratch 176 1 Stream.finalize)

/-- `vg_sha224_finalize`. -/
def finalize224 : Prog isa :=
  scrubAll 0 176 (Impl.StackScratch.Arm.withStackScratch 176 1 Stream.finalize224)

/-- The words `digest` leaves secret, which the residue analysis (`Arm.rtaint`)
finds may differ between two runs. -/
def digestWords : List Nat := List.range' 0 4

/-- `vg_sha224_digest`. -/
def digest224 : Prog isa := scrubSel 0 344 digestWords (Impl.MdStream.Arm.Digest.digest Stream.streamFns224)

/-- `vg_sha256_digest`. -/
def digest : Prog isa := scrubSel 0 344 digestWords (Impl.MdStream.Arm.Digest.digest Stream.streamFns)

end VG.Impl.Sha256.Arm.Fn
