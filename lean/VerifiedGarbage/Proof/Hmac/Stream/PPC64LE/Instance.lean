module

import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Shared
public import VerifiedGarbage.Impl.Hmac.Stream.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
public import VerifiedGarbage.Proof.Hmac.Generic.Implies
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Hash
public import VerifiedGarbage.Spec.Hmac.Generic

/-!
# HMAC over any streaming hash function on PPC64LE: an instance

The functions emitted for each hash function `H` of instance `I`
(`Spec/Hmac/Generic.lean`): `init` and `finalize` with their working space as
an argument (`vg_hmac_<hash>_init_scratch`, `…_finalize_scratch`), and with
it in a frame of `hmacFrame I` bytes of their own; `init` for a key of any
length (`initCode`) runs `init` in that frame for a key of at most a block,
and `initLong` in a frame of 48 bytes fewer (so that both take the same
stack), which it wipes, for a longer one. The states satisfying the shared
contracts' preconditions, at each instance's sizes, are built here too.
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.PPC64LE

open VG.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)

/-- The bytes of the frame holding the working space of `init` and
`finalize` (of instance `I`) and its 32-byte header. -/
def hmacFrame (I : Spec.Hmac.Instance) : Nat := 8 * I.scratch + 32

/-- The bytes of the frame holding `initLong`'s working space: 48 bytes fewer
than `hmacFrame`, since `initLong` and the `init` it calls push one frame
more. -/
def longFrame (I : Spec.Hmac.Instance) : Nat := hmacFrame I - 48

/-- `vg_hmac_<hash>_init`, for a key of any length, with `B = 2 ^ b`. -/
def initCode (H : Hash) (I : Spec.Hmac.Instance) (b : Nat) : Prog isa :=
  Hash.initEntry b (Impl.StackScratch.PPC64LE.withStackScratch (hmacFrame I) .r7 H.init)
    (Impl.StackScratch.PPC64LE.withStackScratchWiped (longFrame I) .r7 (H.lbytes / 8) H.initLong)

/-- A state satisfying `init`'s precondition, with states of `S` bytes and a
one-byte key, and `sc` bytes of scratch space (none: the frame holds it). -/
def initSat (S sc : Nat) : State where
  gpr r := match r with
    | .r3 => 0x10000 | .r4 => 0x20000 | .r5 => 0x30000 | .r6 => 1 | .r7 => 0x40000
    | _ => 0
  lr := 0
  sp := 0x90000
  mem _ := 0
  rd := [⟨0x30000, 1⟩]
  wr := [⟨0x10000, S⟩, ⟨0x20000, S⟩] ++ (if sc = 0 then [] else [⟨0x40000, sc⟩])

/-- A state satisfying `initLong`'s precondition: a 200-byte key. -/
def longSat (S sc : Nat) : State where
  gpr r := match r with
    | .r3 => 0x10000 | .r4 => 0x20000 | .r5 => 0x30000 | .r6 => 200 | .r7 => 0x40000
    | _ => 0
  lr := 0
  sp := 0x90000
  mem _ := 0
  rd := [⟨0x30000, 200⟩]
  wr := [⟨0x10000, S⟩, ⟨0x20000, S⟩] ++ (if sc = 0 then [] else [⟨0x40000, sc⟩])

/-- A state satisfying `finalize`'s precondition, with states of `S` bytes, a
digest of `D` bytes, and `sc` bytes of scratch space. -/
def finSat (S D sc : Nat) : State where
  gpr r := match r with
    | .r3 => 0x10000 | .r4 => 0x20000 | .r6 => 0x30000 | .r7 => 0x40000
    | _ => 0
  lr := 0
  sp := 0x90000
  mem _ := 0
  rd := [⟨0x20000, S⟩]
  wr := [⟨0x10000, S⟩, ⟨0x30000, D⟩] ++ (if sc = 0 then [] else [⟨0x40000, sc⟩])

end VG.Proof.Hmac.Stream.PPC64LE
