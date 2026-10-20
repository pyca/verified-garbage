module

public import VerifiedGarbage.Impl.Pbkdf2.Whole.X86

/-!
# HMAC's `init` for a key of any length over any streaming hash function: x86 (32-bit) implementation

As on x86-64 (`Impl/Pbkdf2/Md/AnyKey/X86_64.lean`):
`initAny(inner, outer, key, key_len, scratch)`, every argument on the stack
(cdecl), does FIPS 198-1 §4's steps 1–3 for a key of any length: a key
longer than a block is hashed with the hash function's streaming functions,
as `pbkdf2` hashes a long password (`Fns.hashKey`, here with the key and its
length as arguments 2 and 3), and HMAC's `init` (`init_scratch`, which takes a
key of at most a block) is called with the key or its digest.

`scratch` has `pbkdf2`'s working space, `W + S` words, laid out as its
(`Impl/Pbkdf2/Whole/X86.lean`): the working space of the functions we call
(`8 W` bytes), our caller's `ebx`, `esi`, `edi` and `ebp`, and for a long key
the working state (at `stWO`) and its digest (at `hkO`). `ebp` is always
`scratch`; our arguments are read from the stack whenever they are needed.
Every call passes its arguments in a frame of their own, pushed last to
first. The only branch is on `key_len`, which is public.

The digest stays in `scratch`, which the function that allocates it wipes
(`withStackScratchWiped`). `vg_hmac_<hash>_init` runs that only for a key
longer than a block (`initEntry`, which compares `key_len` on entry): a key
of at most a block goes to `init` in a frame of its own as before, smaller
and not wiped.
-/

@[expose] public section

namespace VG.Impl.Pbkdf2.Whole.X86

open VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (scr)

namespace Fns

variable (F : Fns)

/-- Our caller's registers into `scratch` (argument 4), which `ebp` then
holds. -/
def anyPrologue : List Instr :=
  ([.mov .eax (argM 4)] : List Instr) ++ F.L.save ++ ([.mov .ebp (.reg .eax)] : List Instr)

/-- `key_len`, compared with `B + 1`. -/
def anyCmp : List Instr := [.mov .ecx (argM 3), .alu .cmp .ecx (.imm (BitVec.ofNat 32 (F.H.B + 1)))]

/-- `update`'s arguments: the key. -/
def anyHk3 : List Instr := [.mov .eax (.imm 0), .mov .esi (.imm 0), .mov .ecx (argM 3), .mov .edx (argM 2)]

/-- `finalize`'s arguments: the key's length as the count, and the digest into
`scratch`. -/
def anyHk5 : List Instr := ([.mov .eax (argM 3), .mov .ecx (.imm 0)] : List Instr) ++ scr .edx F.hkO

/-- A key longer than a block: its digest is the key. -/
def anyHashKey : Prog isa :=
  .seq (.block (scr .edi F.stWO))
  (.seq (F.H.callInit .edi)
  (.seq (.block anyHk3)
  (.seq (.frame (.push [.ebp, .ecx, .edx, .eax, .esi, .edi]) (.call F.H.updN F.H.updC) (.pop .eax 6))
  (.seq (.block F.anyHk5)
  (.seq (.frame (.push [.ebp, .edx, .ecx, .eax, .edi]) (.call F.H.finN F.H.finC) (.pop .eax 5))
    (.block (scr .edx F.hkO ++ ([.mov .ecx (.imm (BitVec.ofNat 32 F.H.D))] : List Instr))))))))

/-- The key at most a block long. -/
def anyShort : List Instr := [.mov .edx (argM 2)]

/-- The key, at `edx`, of `ecx` bytes. -/
def anyKey : Prog isa :=
  .seq (.block F.anyCmp) (.ite .ae F.anyHashKey (.block anyShort))

/-- HMAC's `init`'s states (its key is in `edx`, `ecx`, and its working space
in `ebp`). -/
def anyArgs : List Instr := [.mov .edi (argM 0), .mov .esi (argM 1)]

def hmacInitAny : Prog isa :=
  .seq (.block F.anyPrologue)
  (.seq F.anyKey
  (.seq (.block anyArgs)
  (.seq (.frame (.push [.ebp, .ecx, .edx, .esi, .edi]) (.call F.hiN F.hiC) (.pop .eax 5))
    (.block F.L.restore))))

end Fns

/-- `init` for a key of any length, choosing on entry: `long` (`init` for a
key of any length, cold) if `key_len` (argument 3) is more than `B` bytes, and
`short` (`init` for a key of at most a block) otherwise. -/
def initEntry (B : Nat) (short long : Prog isa) : Prog isa :=
  .seq (.block [.mov .eax (Fns.argM 3), .alu .cmp .eax (.imm (BitVec.ofNat 32 (B + 1)))])
    (Code.iteCold .ae long short)

end VG.Impl.Pbkdf2.Whole.X86
