module

public import VerifiedGarbage.Impl.Sha1.Arm
public import VerifiedGarbage.Impl.MdStream.Arm
public import VerifiedGarbage.Impl.MdStream.Arm.Digest
public import VerifiedGarbage.Impl.Scrub.Arm
public import VerifiedGarbage.Impl.Scrub.ArmSel

/-!
# Streaming SHA-1: 32-bit ARM implementation

The streaming state (84 bytes at `state`) is the hash value followed by a
64-byte buffer (see `VG.Spec.Sha1.Repr`).

* `init(state = r0)` stores the initial hash value.
* `update` and `finalize` are the generic streaming code
  (`Impl/MdStream/Arm.lean`), calling the compression function
  (`vg_sha1_compress`) with `scratch[0..112)` as its scratch space, and saving our
  caller's `r4`–`r11` and `lr` in `scratch[112..148)`.
-/

@[expose] public section

namespace VG.Impl.Sha1.Arm.Stream

open VG.Arm
open VG.Impl.Sha1.Arm (compress)

def init : Prog isa :=
  .block ((List.range 5).flatMap fun k =>
    [.movw .r12 (Spec.Sha1.H0[k]!.extractLsb' 0 16),
     .movt .r12 (Spec.Sha1.H0[k]!.extractLsb' 16 16),
     .str .r12 .r0 (4 * k)])

/-! ## `update` and `finalize`

The generic streaming code (`Impl/MdStream/Arm.lean`). -/

def params : MdStream.Arm.Params where
  N := 20
  B := 64
  L := 8
  so := 112
  len := MdStream.Arm.len64 76 true
  out := MdStream.Arm.out32 5 true

def update : Prog isa := MdStream.Arm.update params "vg_sha1_compress" compress

def finalize : Prog isa := MdStream.Arm.finalize params "vg_sha1_compress" compress

/-- SHA-1's streaming functions as HMAC, PBKDF2 and the one-shot digest call
them (`Impl.Pbkdf2.Stream.Arm.Hash`): a 84-byte streaming state, 20 words of
working space and a 20-byte digest, under internal names. -/
def streamFns : Impl.Pbkdf2.Stream.Arm.Hash := ⟨64, 84, 20, 20, 20, "vg_sha1_init_core", init,
  "vg_sha1_update_scratch", update, "vg_sha1_finalize_scratch", finalize⟩

end VG.Impl.Sha1.Arm.Stream

/-! ## The functions as emitted

Each is its code, then its cleanup (`Impl/Scrub/Arm.lean`): the registers
a callee may change set to constants, and first, for `update` and
`finalize`, the 176 bytes of the stack of their contract, their frame
(`withStackScratch`), zeroed. `digest` wipes its own working space
(`withRegScratchWiped`), and its cleanup zeroes only the words of its stack
that the residue analysis (`Arm.rtaint`) finds may differ between two runs
(`Impl/Scrub/ArmSel.lean`, `scrubSel`, `digestWords`, offsets in words from
the lowest address of that stack). None returns a value. -/

namespace VG.Impl.Sha1.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm

/-- `vg_sha1_init`. -/
def init : Prog isa := scrub 0 Stream.init

/-- `vg_sha1_update`. -/
def update : Prog isa := scrubAll 0 176 (Impl.StackScratch.Arm.withStackScratch 176 2 Stream.update)

/-- `vg_sha1_finalize`. -/
def finalize : Prog isa := scrubAll 0 176 (Impl.StackScratch.Arm.withStackScratch 176 1 Stream.finalize)

/-- The words `digest` leaves secret, which the residue analysis (`Arm.rtaint`)
finds may differ between two runs. -/
def digestWords : List Nat := List.range' 0 4

/-- `vg_sha1_digest`. -/
def digest : Prog isa := scrubSel 0 320 digestWords (Impl.MdStream.Arm.Digest.digest Stream.streamFns)

end VG.Impl.Sha1.Arm.Fn
