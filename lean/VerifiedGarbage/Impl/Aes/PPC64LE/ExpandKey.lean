module

public import VerifiedGarbage.Impl.Aes.PPC64LE.Ctr32

/-!
# The AES key expansion on PPC64LE

`vg_aes_expand_key_scratch(key = r3, key_len = r4, schedule = r5, scratch = r6)`;
`vg_aes_expand_key` runs it with `scratch` in a frame of its own (`Proof/Aes/PPC64LE/Frame.lean`).

FIPS 197 §5.2 (`KEYEXPANSION`), one word at a time, with `SUBWORD` done by
the bitsliced S-box of `Sbox.lean` on the word in the low 32 bits of `q 0`
(as BearSSL's `aes_ct64` does in its `sub_word`; Thomas Pornin, MIT
licence), as the x86-64 code does (`Impl/Aes/X86_64/ExpandKey.lean`).

* `r8` is the scratch buffer; the nonvolatile registers are saved in its
  slots 40–57, and the round constant is kept in slot 61.
* The key is copied into the schedule 8 bytes at a time (16, 24 and 32 are
  multiples of 8), counting its length down in `r4`; `r7` keeps it.
* Word `i` (from `Nk` on) is computed with `r11` at `w[i − 1]`, `r10` at
  `w[i − Nk]`, `r12 = 4 (i mod Nk)` and `r4` the words left. Every branch is
  on these and `r7`, which depend only on `key_len`; the key's bytes only
  ever reach the S-box's registers and memory.
-/

@[expose] public section

namespace VG.Impl.Aes.PPC64LE

open VG.PPC64LE

/-- The slot of the round constant. -/
def rconSlot : Nat := 61

/-- Copy the key (`r4` bytes at `r3`, a multiple of 8) to `r5`. -/
def copyBody : List Instr :=
  [.load .d t0 .r3 0, .store .d t0 .r5 0, .addi .r3 .r3 8, .addi .r5 .r5 8, .subi .r4 .r4 8]

/-- After the copy (`r5` at `w[Nk]`, `r7 = 4 Nk`): `r10 := w[0]`,
`r11 := w[Nk − 1]`, `r12 := 0`, `r4 := 4 (Nr + 1) − Nk = 3 Nk + 28` words
left, and the round constant 1. -/
def wordSetup : List Instr :=
  [.sub .r10 .r5 .r7, .subi .r11 .r5 4, .li .r12 0, shrI .r4 .r7 2, .add t0 .r4 .r4,
   .add .r4 .r4 t0, .addi .r4 .r4 28, .li t0 1, stS rconSlot t0]

/-- The S-box on each byte of `q 0` (and of the other words). -/
def subAll : List Instr := toBs ++ sboxCode ++ fromBs

/-- After `subAll`: `q 0 := ROTWORD(q 0) ⊕ Rcon` (on the low 32 bits), and
the round constant times `x` (without a branch: `{1b}` is XORed in under a
mask made from bit 7). -/
def rotTail : List Instr :=
  [.rotr .w (q 0) (q 0) 8, ldS (q 1) rconSlot, xorR (q 0) (q 0) (q 1),
   shrI (q 2) (q 1) 7, .li (q 3) 0, .sub (q 3) (q 3) (q 2), .li t0 0x1b, andR (q 3) (q 3) t0,
   .add (q 1) (q 1) (q 1), xorR (q 1) (q 1) (q 3), .li t0 0xff, andR (q 1) (q 1) t0,
   stS rconSlot (q 1)]

/-- `q 0 := SUBWORD(ROTWORD(q 0)) ⊕ Rcon`. -/
def rotWordStep : List Instr := subAll ++ rotTail

/-- Word `i`: `temp := w[i − 1]`, transformed if `i mod Nk = 0`, or if
`Nk = 8` and `i mod Nk = 4`; `w[i] := w[i − Nk] ⊕ temp`; and on to `i + 1`. -/
def wordBody : Prog isa :=
  .seq (.block [.load .w (q 0) .r11 0])
    (.seq (.ite (.zero .d .r12) (.block rotWordStep)
        (.seq (.block [.subi t0 .r12 16])
          (.ite (.zero .d t0) (.seq (.block [.subi t0 .r7 32]) (.ite (.zero .d t0) (.block subAll) (.block [])))
            (.block []))))
      (.seq (.block [.load .w t0 .r10 0, xorR (q 0) (q 0) t0, .store .w (q 0) .r11 4,
          .addi .r11 .r11 4, .addi .r10 .r10 4, .addi .r12 .r12 4, .sub t0 .r12 .r7])
        (.seq (.ite (.zero .d t0) (.block [.li .r12 0]) (.block []))
          (.block [.subi .r4 .r4 1]))))

def expandKey : Prog isa :=
  .seq (.block ([movR sb .r6] ++ saveRegs ++ [movR .r7 .r4]))
    (.seq (.loop (.block copyBody) (.nonzero .d .r4))
      (.seq (.block wordSetup)
        (.seq (.loop wordBody (.nonzero .d .r4)) (.block restoreRegs))))

end VG.Impl.Aes.PPC64LE
