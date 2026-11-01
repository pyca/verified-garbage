module

public import VerifiedGarbage.Impl.Sm4.X86.Ecb
public import VerifiedGarbage.Impl.Sm4.Planes
public import VerifiedGarbage.Spec.Sm4.Contract

/-!
# SM4's round keys prepared once, and batches under them, on x86 (32-bit)

`vg_sm4_prepare_keys` and `vg_sm4_crypt_prepared`
(`Proof/Sm4/Prepared.lean`): ECB's two halves (`Ecb.lean`) as functions of
the working space, for the modes, which call them (`Modes.lean`). Both are
cdecl, their arguments at `[esp + 4]` on.

* `prepareKeys(schedule, decrypt, ws, ws_len)` saves the callee-saved
  registers in their slots (352–355) of `ws`, which moves to `edi`, builds
  the table of bitsliced round keys in the order `decrypt` selects (public)
  and restores the registers.
* `cryptPrepared(ws, ws_len)` saves the registers the same way and
  transforms the eight blocks of the tail buffer (`crypt8`) under the table.

The working space is ECB's 358 slots (`slots`). The table is what
`vg_sm4_crypt_prepared` reads of the preparation (`layout`): each plane of a
round key is a 32-bit word whose bit `8 i + b` is bit `j` of the key's byte
`i` (`planeOf32`), for every block `b`.
-/

@[expose] public section

namespace VG.Impl.Sm4.X86

open VG.X86 VG.Impl.Aes.X86

/-- `vg_sm4_prepare_keys`: the table of the direction the second argument
selects. -/
def prepareKeys : Prog isa :=
  .seq (.block (saveRegs 2 ++ [.mov .eax (.mem (argOp 1)), .alu .test .eax (.reg .eax)]))
    (.seq (.ite .e (keys .encrypt) (keys .decrypt)) (.block restoreRegs))

/-- `vg_sm4_crypt_prepared`: the eight blocks of the tail buffer. -/
def cryptPrepared : Prog isa :=
  .seq (.block (saveRegs 0)) (.seq crypt8 (.block restoreRegs))

/-! ## The layout -/

/-- The direction of the specification. -/
def ofSpecDir : Spec.Sm4.Direction → Dir
  | .encrypt => .encrypt
  | .decrypt => .decrypt

/-- The round key of the table's entry `e`, for the round keys `k` in the
order of the direction. -/
def keyEntry (k : Spec.Sm4.Schedule) : Dir → Nat → Spec.Sm4.Word
  | .encrypt, e => k.getD e 0
  | .decrypt, e => k.getD (31 - e) 0

/-- The word of slot `w` of the table: plane `w % 8` of its entry. -/
def preparedWord (k : Spec.Sm4.Schedule) (d : Dir) (w : Nat) : BitVec 32 :=
  Impl.Sm4.planeOf32 (keyEntry k d ((w - tableSlot) / 8)) ((w - tableSlot) % 8)

/-! ## The calls -/

/-- The working space's length in 64-bit words, `ws_len`. -/
def wsWords : Nat := 4 * slots / 8

/-- The value of `decrypt` for a direction. -/
def dirFlagOf : Dir → Nat
  | .encrypt => 0
  | .decrypt => 1

/-- The modes' data pointer and steps left, after the functions' slots
(`Impl/Modes/X86/Seq.lean`'s `dSlot` and `nSlot`). -/
def modeDSlot : Nat := slots + 4
def modeNSlot : Nat := slots + 5

/-- A call of `vg_sm4_prepare_keys` for the direction `d`, with the schedule
the mode's first argument and the working space at `edi`, of `slots` slots
(`wsWords` 64-bit words): the arguments pushed, the last first. `edi`, which
the function restores, is loaded again from the modes' fifth argument, the
working space: the analysis of constant time forgets which slot holds it
across the function's stores through a pointer into the table. -/
def prepareCall (d : Dir) : Prog isa :=
  .seq (.block [movI .eax (BitVec.ofNat 32 wsWords), movI .edx (BitVec.ofNat 32 (dirFlagOf d)),
      .mov .ecx (.mem (argOp 0))])
    (.seq (.frame (.push [.eax, .edi, .edx, .ecx])
      (.call "vg_sm4_prepare_keys" prepareKeys) (.pop .eax 4))
      (.block [.mov .edi (.mem (argOp 4))]))

/-- A call of `vg_sm4_crypt_prepared` on the working space at `edi`. The
modes' data pointer and steps left wait in `esi` and `ebp`, which the
function restores, and go back to their slots after it: the analysis of
constant time forgets what the scratch buffer holds across the function's
stores. -/
def cryptCall : Prog isa :=
  .seq (.block [movS .esi modeDSlot, movS .ebp modeNSlot, movI .eax (BitVec.ofNat 32 wsWords)])
    (.seq (.frame (.push [.eax, .edi]) (.call "vg_sm4_crypt_prepared" cryptPrepared) (.pop .eax 2))
      (.block [st modeDSlot .esi, st modeNSlot .ebp]))

end VG.Impl.Sm4.X86
