module

public import VerifiedGarbage.Impl.Pbkdf2.Whole.X86
public import VerifiedGarbage.Impl.StackScratch.X86

/-!
# The one-shot digest over any streaming hash function: x86 (32-bit) implementation

`digest(data, len, out)`, every argument on the stack (cdecl), hashes the
`len` bytes at `data` with a hash function's streaming `init`, `update` and
`finalize` (`Hash`, as HMAC's and PBKDF2's code calls them,
`VG.Impl.Pbkdf2.Stream.X86`), as HMAC's `init` hashes a long key
(`Fns.anyHashKey`, `Impl/Pbkdf2/Md/AnyKey/X86.lean`).

Its working space, `scratch`, is in a frame of its own (`dbytes` bytes),
which `withStackScratchWiped` passes as a fourth argument and zeroes after
the code. `scratch` holds the working space of the functions we call (`8 W`
bytes), then our caller's `ebx`, `esi`, `edi` and `ebp` (`Hash.saved`), then
the streaming state (at `stO`) and what `finalize` writes (at `dgO`), whose
first `D` bytes, the digest, are copied to `out` last. Across the calls `ebp`
is `scratch` and `edi` the streaming state; our arguments are read from the
stack whenever they are needed. Every call passes its arguments in a frame of
their own, pushed last to first. Every address and branch depends only on the
pointers and `len`.
-/

@[expose] public section

namespace VG.Impl.MdStream.X86.Digest

open VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash scr copy)
open VG.Impl.Pbkdf2.Whole.X86.Fns (argM)

variable (H : Hash)

/-- Where the streaming state is in `scratch`. -/
def stO : Nat := H.buf

/-- Where `finalize` writes in `scratch`. -/
def dgO : Nat := H.buf + H.S

/-- The bytes of `scratch` (a multiple of 8). -/
def dbytes : Nat := (H.buf + H.S + H.F + 7) / 8 * 8

/-- The bytes of the frame `withStackScratchWiped` allocates: a word for the
return address, a copy of our three argument slots, the address of
`scratch`, and `scratch`. -/
def dframe : Nat := 20 + dbytes H

/-- Our caller's registers into `scratch` (argument 3), which `ebp` then
holds, and the streaming state's address in `edi`. -/
def prologue : List Instr :=
  ([.mov .eax (argM 3)] : List Instr) ++ H.save ++ ([.mov .ebp (.reg .eax)] : List Instr) ++ scr .edi (stO H)

/-- `update`'s arguments: the count (0), and `len` bytes at `data`. -/
def updArgs : List Instr := [.mov .eax (.imm 0), .mov .esi (.imm 0), .mov .ecx (argM 1), .mov .edx (argM 0)]

/-- `finalize`'s arguments: `len` as the count, and its output into `scratch`. -/
def finArgs : List Instr := ([.mov .eax (argM 1), .mov .ecx (.imm 0)] : List Instr) ++ scr .edx (dgO H)

/-- `out`, for the copy. -/
def outArg : List Instr := [.mov .esi (argM 2)]

/-- `digest`, with `scratch` as a fourth argument. -/
def digestMain : Prog isa :=
  .seq (.block (prologue H))
  (.seq (H.callInit .edi)
  (.seq (.block updArgs)
  (.seq (.frame (.push [.ebp, .ecx, .edx, .eax, .esi, .edi]) (.call H.updN H.updC) (.pop .eax 6))
  (.seq (.block (finArgs H))
  (.seq (.frame (.push [.ebp, .edx, .ecx, .eax, .edi]) (.call H.finN H.finC) (.pop .eax 5))
  (.seq (.block outArg)
  (.seq (copy .ebp (dgO H) .esi 0 H.D)
    (.block H.restore))))))))

/-- `vg_<hash>_digest`: `digestMain` with `scratch` in a frame of its own,
zeroed after it. -/
def digest : Prog isa :=
  Impl.StackScratch.X86.withStackScratchWiped (dframe H) 3 (dbytes H / 4) (digestMain H)

end VG.Impl.MdStream.X86.Digest
