module

public import VerifiedGarbage.Impl.Modes.PPC64LE.Seq
public import VerifiedGarbage.Impl.Modes.CbcChained
public import VerifiedGarbage.Impl.Modes.Ctr
public import VerifiedGarbage.Impl.Camellia.PPC64LE.Prepared

/-!
# Camellia's modes on PPC64LE

The modes' functions take two key arguments,
`f(schedule = r3, rounds = r4, iv = r5, data = r6, n = r7, scratch = r8)`,
where the generic modes (`Impl/Modes/PPC64LE/Seq.lean`) take one. So
`wrap` saves the caller's `r28` in the scratch buffer's slot after the
modes' (`extraSlot`), keeps the number of rounds in `r28`, which the modes
and the core keep, moves the other arguments to the generic modes'
registers, and restores `r28` after them.

`dirCore d`: Camellia's core for the modes, its subkeys in the order of the
direction `d`: encryption's for CBC encryption, OFB and CFB, decryption's
for CBC decryption. `prepare` inlines the body of `vg_camellia_prepare_keys`
(`Prepared.lean`), which sets the masks and builds the table of bitsliced
subkeys, once; `crypt` calls `vg_camellia_crypt_prepared`, which transforms
the eight blocks of the tail buffer in place, of which the modes use the
first (they take one step at a time).

Both functions use every callee-saved register, which they save in their
working space and restore. The body of `vg_camellia_prepare_keys` stores
through a pointer that the analysis of constant time cannot place, after
which it knows nothing of the working space: so while it runs, the values
the core must keep public (the modes' state in `r29`–`r31`, the schedule's
address in `r3`, the number of rounds and the scratch buffer's address)
wait in registers the body does not write (`r0`, `r5`, `r6`, `r9`–`r12`),
so that none of them passes through memory. Around the call,
`vg_camellia_crypt_prepared` keeps `r28`–`r31` in its working space, whose
slots the analysis follows, and writes neither `r6` nor `r10`, which keep
the scratch buffer's address and `r3`.

The core's slots are the functions' 414 (`slots`), the modes' six after
them, `wrap`'s one, and one more for alignment: 422 in all
(`[u64; 422]`).

`cbcEncryptChained`, `cbcDecryptChained`, `ofb`, `cfbEncrypt`,
`cfbDecrypt` and `ctr` are the modes over it.
-/

@[expose] public section

namespace VG.Impl.Camellia.PPC64LE

open VG.PPC64LE
open VG.Impl.Modes.PPC64LE (mov)

/-- The slot of the caller's `r28`, after the modes'. -/
def extraSlot : Nat := slots + 6

/-- The scratch buffer's slots. -/
def modeSlots : Nat := slots + 8

/-- The bit `vg_camellia_prepare_keys` takes for the direction. -/
def dirBit : Dir → Nat
  | .encrypt => 0
  | .decrypt => 1

/-- `vg_camellia_prepare_keys`'s body (schedule = r3, rounds = r4, decrypt =
r5, ws = r6), the modes' state, `r3` and the number of rounds kept in `r9`–`r12`
and `r0`, and `sb` in `r6`. -/
def prepareCore (d : Dir) : Prog isa :=
  .seq (.block [mov .r6 .r5, mov .r4 .r28, .li .r5 (dirBit d), mov .r9 .r29, mov .r10 .r30,
      mov .r11 .r31, mov .r12 .r3, mov .r0 .r28])
    (.seq prepareKeys
      (.block [mov .r5 .r6, mov .r3 .r12, mov .r28 .r0, mov .r29 .r9, mov .r30 .r10, mov .r31 .r11]))

/-- A call of `vg_camellia_crypt_prepared(r28, sb, slots)`, `r3` kept in `r10`
and `sb` in `r6`, which the function does not write. -/
def cryptCall : Prog isa :=
  .seq (.block [mov .r10 .r3, mov .r6 .r5, mov .r3 .r28, mov .r4 .r5, .li .r5 slots])
    (.seq (.call (Spec.Camellia.Prepared.cryptApi layout).name cryptPrepared) (.block [mov .r5 .r6, mov .r3 .r10]))

/-- Camellia's core for the modes, in the direction `d`. -/
def dirCore (d : Dir) : Modes.PPC64LE.Core where
  prepare := prepareCore d
  crypt := cryptCall
  slots := slots
  total := modeSlots
  buf := tailSlot
  G := 1
  bw := 4

/-- A mode with the two key arguments: the caller's `r28` saved in the
scratch buffer (at `r8`), the number of rounds to `r28`, the other arguments
to the generic modes' registers, and `r28` restored after (from the scratch
buffer, at `sb`). -/
def wrap (p : Prog isa) : Prog isa :=
  .seq (.block [.store .d .r28 .r8 (8 * extraSlot), mov .r28 .r4, mov .r4 .r5, mov .r5 .r6, mov .r6 .r7,
      mov .r7 .r8])
    (.seq p (.block [.load .d .r28 Modes.PPC64LE.sb (8 * extraSlot)]))

/-- `vg_camellia_cbc_encrypt_chained`, with its scratch buffer as the sixth argument. -/
def cbcEncryptChained : Prog isa := wrap ((dirCore .encrypt).seq (Modes.Mode.cbcEncChained 4))

/-- `vg_camellia_cbc_decrypt_chained`, with its scratch buffer as the sixth argument. -/
def cbcDecryptChained : Prog isa := wrap ((dirCore .decrypt).seq (Modes.Mode.cbcDecChained 4))

/-- `vg_camellia_ofb`, with its scratch buffer as the sixth argument. -/
def ofb : Prog isa := wrap ((dirCore .encrypt).seq (Modes.Mode.ofb 4))

/-- `vg_camellia_cfb128_encrypt`, with its scratch buffer as the sixth argument. -/
def cfbEncrypt : Prog isa := wrap ((dirCore .encrypt).seq (Modes.Mode.cfbEnc 4))

/-- `vg_camellia_cfb128_decrypt`, with its scratch buffer as the sixth argument. -/
def cfbDecrypt : Prog isa := wrap ((dirCore .encrypt).seq (Modes.Mode.cfbDec 4))

/-- `vg_camellia_ctr`, with its scratch buffer as the sixth argument. -/
def ctr : Prog isa := wrap ((dirCore .encrypt).seq Modes.Mode.ctr)

end VG.Impl.Camellia.PPC64LE
