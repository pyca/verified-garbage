module

public import VerifiedGarbage.Impl.Pbkdf2.Whole.Arm

/-!
# HMAC's `init` for a key of any length over any streaming hash function: 32-bit ARM implementation

As on x86 (`Impl/Pbkdf2/Md/AnyKey/X86.lean`): `initAny(inner = r0, outer = r1,
key = r2, key_len = r3, scratch = [sp])` does FIPS 198-1 §4's steps 1–3 for a
key of any length: a key longer than a block is hashed with the hash
function's streaming functions, as `pbkdf2` hashes a long password (`Fns.key`
itself, with the key in `r8` and `r9`, where `pbkdf2` keeps the password),
and HMAC's `init` (`init_scratch`, which takes a key of at most a block) is
called with the key or its digest.

`scratch` has `pbkdf2`'s working space, `W + S` words, laid out as its
(`Impl/Pbkdf2/Whole/Arm.lean`): the working space of the functions we call
(`8 W` bytes), our caller's registers and our return address, and for a long
key the working state (at `stWO`) and its digest (at `hkO`). `r11` is always
`scratch`, `r5` and `r6` the states. The only branch is on `key_len`, which
is public.

The digest stays in `scratch`, which the function that allocates it wipes
(`withStackScratchWiped`). `vg_hmac_<hash>_init` runs that only for a key
longer than a block (`initEntry`, which compares `key_len` on entry): a key
of at most a block goes to `init` in a frame of its own as before, smaller
and not wiped.
-/

@[expose] public section

namespace VG.Impl.Pbkdf2.Whole.Arm

open VG.Arm

namespace Fns

variable (F : Fns)

/-- Our caller's registers into `scratch`, which `r11` then holds; the key in
`r8` and `r9`, as `key` takes it, and the states in `r5` and `r6`. -/
def anyPrologue : List Instr :=
  ([.ldrSp .r12 0] : List Instr) ++ F.L.save ++
    ([.mov .r11 (.reg .r12), .mov .r8 (.reg .r2), .mov .r9 (.reg .r3), .mov .r5 (.reg .r0), .mov .r6 (.reg .r1)] :
      List Instr)

/-- HMAC's `init`'s arguments but the key (in `r2` and `r3`): the states and
`scratch`. -/
def anyArgs : List Instr := [.mov .r0 (.reg .r5), .mov .r1 (.reg .r6), .mov .r12 (.reg .r11)]

def hmacInitAny : Prog isa :=
  .seq (.block F.anyPrologue)
  (.seq F.key
  (.seq (.block anyArgs)
  (.seq (.frame (.push [.r12, .lr]) (.call F.hiN F.hiC) (.pop .r12 8))
    (.block F.L.restore))))

end Fns

/-- `init` for a key of any length, choosing on entry: `long` (`init` for a
key of any length, cold) if `key_len` (`r3`) is more than `B` bytes, and
`short` (`init` for a key of at most a block) otherwise. `Z` is whether
`key_len < B + 1`, as in `Fns.cmpPw`, through `r12`. -/
def initEntry (B : Nat) (short long : Prog isa) : Prog isa :=
  .seq (.block [.subs .r12 .r3 (.imm (BitVec.ofNat 32 (B + 1))), .mov .r12 (.imm 0), .adc .r12 .r12 (.imm 0),
      .cmp .r12 (.imm 0)])
    (Code.iteCold .ne long short)

end VG.Impl.Pbkdf2.Whole.Arm
