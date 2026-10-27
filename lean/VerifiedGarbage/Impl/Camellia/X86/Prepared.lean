module

public import VerifiedGarbage.Impl.Camellia.X86.Ecb
public import VerifiedGarbage.Impl.Camellia.Planes32
public import VerifiedGarbage.Spec.Camellia.Prepared

/-!
# Camellia's batches under prepared subkeys, on x86 (32-bit)

`vg_camellia_crypt_prepared` (`Spec/Camellia/Prepared.lean`): ECB's eight
blocks (`Ecb.lean`) as a function of the working space, for the modes,
which call it (`Modes.lean`).

`cryptPrepared(rounds, ws, ws_len)`, cdecl (the arguments at `[esp + 4]` …
`[esp + 12]`), saves the callee-saved registers in their slots (648–651),
moves `ws` to `edi`, and transforms the eight blocks of the tail buffer
(`crypt8`) under the table, with the code written out for 18 rounds or 24,
as ECB's, then restores the registers.

The working space is ECB's 672 slots (`slots`), of 4 bytes. The table is
what `vg_camellia_crypt_prepared` reads (`layout`): sixteen 32-bit planes
for each subkey, plane `8 w + j` its plane `j` of word `w`
(`keyPlane32`), in the order the rounds use them.

The modes build the table themselves, ECB's key setup inline in their
core's `prepare`: its loop stores through a pointer that the analysis of
constant time cannot place, after which it knows nothing of the working
space, and a call would return the callee-saved registers as secrets.
-/

@[expose] public section

namespace VG.Impl.Camellia.X86

open VG.X86 VG.Impl.Aes.X86

/-- `vg_camellia_crypt_prepared`: the eight blocks of the tail buffer. -/
def cryptPrepared : Prog isa :=
  .seq (.block (saveRegs 1 ++ [.mov .eax (.mem (argOp 0)), .alu .cmp .eax (.imm 18)]))
    (.seq (.ite .e (crypt8 3) (crypt8 4)) (.block restoreRegs))

/-! ## The layout -/

/-- The direction of the specification. -/
def ofSpecDir : Spec.Camellia.Direction → Dir
  | .encrypt => .encrypt
  | .decrypt => .decrypt

/-- The schedule's word in the table's entry `e`, for `g` groups of six
rounds and the words `w` in the order encryption uses them: the stored
order for encryption; for decryption `kw3, kw4`, the words between `kw2`
and `kw3` from the last back to the first, then `kw1, kw2` (as `keys`). -/
def keyEntry (w : List (BitVec 64)) (g : Nat) : Dir → Nat → BitVec 64
  | .encrypt, e => w.getD e 0
  | .decrypt, e => w.getD (if e < 2 then 8 * g + e else if e < 8 * g then 8 * g + 1 - e else e - 8 * g) 0

/-- The word of slot `k` (from the table's on) that the key setup writes for
`rounds` rounds: plane `(k - keySlot) % 16` of the table's entry. -/
def preparedWord (rounds : Nat) (w : List (BitVec 64)) (d : Dir) (k : Nat) : BitVec 32 :=
  keyPlane32 (keyEntry w (rounds / 6) d ((k - keySlot) / 16)) ((k - keySlot) % 16 / 8) ((k - keySlot) % 8)

/-- The table's slots, as a byte range. -/
def layout : Spec.Camellia.Prepared.Layout where
  table rounds := [(4 * keySlot, 64 * (8 * (rounds / 6) + 2))]
  encode rounds w d i := (preparedWord rounds w (ofSpecDir d) (i / 4)).extractLsb' (8 * (i % 4)) 8
  buf := 4 * tailSlot
  blocks := 8
  prepScratch := [(0, 4 * slots)]
  cryptScratch := [(0, 4 * keySlot), (4 * savedSlot, 4 * (slots - savedSlot))]
  size := 4 * slots

/-! ## The call -/

/-- The working space's length, in 64-bit words. -/
def wsWords : Nat := slots / 2

/-- A call of `vg_camellia_crypt_prepared` on the working space at `sb`, for
the number of rounds in the mode's second stack argument: the arguments
pushed in a frame. The function restores `edi`. -/
def cryptCall : Prog isa :=
  .seq (.block [.mov .eax (.mem (argOp 1)), movR .ecx sb, movI .edx (BitVec.ofNat 32 wsWords)])
    (.frame (.push [.edx, .ecx, .eax]) (.call (Spec.Camellia.Prepared.cryptApi layout).name cryptPrepared)
      (.pop .eax 3))

end VG.Impl.Camellia.X86
