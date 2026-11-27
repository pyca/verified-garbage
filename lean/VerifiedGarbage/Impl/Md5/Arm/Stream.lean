module

public import VerifiedGarbage.Impl.Md5.Arm
public import VerifiedGarbage.Impl.MdStream.Arm
public import VerifiedGarbage.Impl.Pbkdf2.Stream.Arm
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Impl.Scrub.Arm

/-!
# Streaming MD5: 32-bit ARM implementation

The streaming state (80 bytes at `state`) is the MD buffer followed by a
64-byte buffer (see `VG.Spec.Md5.Repr`).

* `init(state = r0)` stores the initial MD buffer.
* `update` and `finalize` are the generic streaming code
  (`Impl/MdStream/Arm.lean`), calling the compression function
  (`vg_md5_compress`) with `scratch[0..64)` as its scratch space, and saving our
  caller's `r4`–`r11` and `lr` in `scratch[64..100)`.
-/

@[expose] public section

namespace VG.Impl.Md5.Arm.Stream

open VG.Arm
open VG.Impl.Md5.Arm (compress)

def init : Prog isa :=
  .block ((List.range 4).flatMap fun k =>
    [.movw .r12 (Spec.Md5.H0[k]!.extractLsb' 0 16),
     .movt .r12 (Spec.Md5.H0[k]!.extractLsb' 16 16),
     .str .r12 .r0 (4 * k)])

/-! ## `update` and `finalize`

The generic streaming code (`Impl/MdStream/Arm.lean`). -/

def params : MdStream.Arm.Params where
  N := 16
  B := 64
  L := 8
  so := 64
  len := MdStream.Arm.len64 72 false
  out := MdStream.Arm.out32 4 false

def update : Prog isa := MdStream.Arm.update params "vg_md5_compress" compress

def finalize : Prog isa := MdStream.Arm.finalize params "vg_md5_compress" compress

/-- MD5's streaming functions as HMAC and PBKDF2 call them
(`Impl.Pbkdf2.Stream.Arm.Hash`): an 80-byte streaming state, 14 words of
working space and a 16-byte digest, under internal names. -/
def streamFns : Impl.Pbkdf2.Stream.Arm.Hash := ⟨64, 80, 16, 16, 14, "vg_md5_init_core", init,
  "vg_md5_update_scratch", update, "vg_md5_finalize_scratch", finalize⟩

end VG.Impl.Md5.Arm.Stream

/-! ## The functions as emitted

Each is its code, then its cleanup (`Impl/Scrub/Arm.lean`): the registers
a callee may change set to constants, and for `update` and `finalize` first
the 128 bytes of their frame zeroed. None returns a value. -/

namespace VG.Impl.Md5.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm

/-- `vg_md5_init`. -/
def init : Prog isa := scrub 0 Stream.init

/-- `vg_md5_update`: `Stream.update`, its scratch space in a frame of 128
bytes, which is then zeroed. -/
def update : Prog isa := scrubAll 0 128 (Impl.StackScratch.Arm.withStackScratch 128 2 Stream.update)

/-- `vg_md5_finalize`, as `update`. -/
def finalize : Prog isa := scrubAll 0 128 (Impl.StackScratch.Arm.withStackScratch 128 1 Stream.finalize)

end VG.Impl.Md5.Arm.Fn
