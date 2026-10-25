module

public import VerifiedGarbage.Impl.Aes.RISCV64.Ctr32

/-!
# The AES key expansion on RISC-V

`vg_aes_expand_key_scratch(key = a0, key_len = a1, schedule = a2, scratch = a3)`;
`vg_aes_expand_key` runs it with `scratch` in a frame of its own
(`Impl/StackScratch/RISCV64.lean`).

FIPS 197 §5.2 (`KEYEXPANSION`), one word at a time, with `SUBWORD` done by
the bitsliced S-box of `Sbox.lean` on the word in the low 32 bits of `q 0`
(as BearSSL's `aes_ct64` does in its `sub_word`; Thomas Pornin, MIT
licence), as on PPC64LE (`Impl/Aes/PPC64LE/ExpandKey.lean`).

* `a5` is the scratch buffer, rounded up to a multiple of 8 (which leaves 63
  of its 64 slots); the callee-saved registers are saved in its slots
  40–51, the masks of `toBs` and `fromBs` built in slots 52–57, and the
  round constant is kept in slot 58.
* The key is copied into the schedule 8 bytes at a time (16, 24 and 32 are
  multiples of 8), a byte at a time, counting its length down in `a1`;
  `a4` keeps it.
* Word `i` (from `Nk` on) is computed with `a2` at `w[i − 1]`, `a0` at
  `w[i − Nk]`, `a3 = 4 (i mod Nk)` and `a1` the words left. Every branch is
  on these and `a4`, which depend only on `key_len`; the key's bytes only
  ever reach the S-box's registers and memory. The schedule is accessed a
  byte at a time.
-/

@[expose] public section

namespace VG.Impl.Aes.RISCV64

open VG.RISCV64 VG.Impl.Words.RISCV64

/-- The slot of the round constant. -/
def rconSlot : Nat := 58

/-- Copy the key (`a1` bytes at `a0`, a multiple of 8) to `a2`. -/
def copyBody : List Instr :=
  copyBytes t0 .a0 .a2 0 0 8 ++ [.addi .a0 .a0 8, .addi .a2 .a2 8, .addi .a1 .a1 (-8)]

/-- After the copy (`a2` at `w[Nk]`, `a4 = 4 Nk`): `a0 := w[0]`,
`a2 := w[Nk − 1]`, `a3 := 0`, `a1 := 4 (Nr + 1) − Nk = 3 Nk + 28` words
left, and the round constant 1. -/
def wordSetup : List Instr :=
  [.sub .a0 .a2 .a4, .addi .a2 .a2 (-4), .li .a3 0, shrI .a1 .a4 2, .add t0 .a1 .a1,
   .add .a1 .a1 t0, .addi .a1 .a1 28, .li t0 1, stS rconSlot t0]

/-- The S-box on each byte of `q 0` (and of the other words). -/
def subAll : List Instr := toBs ++ sboxCode ++ fromBs

/-- After `subAll`: `q 0 := ROTWORD(q 0) ⊕ Rcon` (on the low 32 bits), and
the round constant times `x` (without a branch: `{1b}` is XORed in under a
mask made from bit 7). -/
def rotTail : List Instr :=
  [.shift .srl .w t0 (q 0) 8, .shift .sll .w (q 0) (q 0) 24, xorR (q 0) (q 0) t0,
   ldS (q 1) rconSlot, xorR (q 0) (q 0) (q 1),
   shrI (q 2) (q 1) 7, .li (q 3) 0, .sub (q 3) (q 3) (q 2), .logicImm .and (q 3) (q 3) 0x1b,
   .add (q 1) (q 1) (q 1), xorR (q 1) (q 1) (q 3), .logicImm .and (q 1) (q 1) 0xff,
   stS rconSlot (q 1)]

/-- `q 0 := SUBWORD(ROTWORD(q 0)) ⊕ Rcon`. -/
def rotWordStep : List Instr := subAll ++ rotTail

/-- Word `i`: `temp := w[i − 1]`, transformed if `i mod Nk = 0`, or if
`Nk = 8` and `i mod Nk = 4`; `w[i] := w[i − Nk] ⊕ temp`; and on to `i + 1`. -/
def wordBody : Prog isa :=
  .seq (.block (loadLE32 (q 0) t0 .a2 0))
    (.seq (.ite (.zero .a3) (.block rotWordStep)
        (.seq (.block [.addi t0 .a3 (-16)])
          (.ite (.zero t0) (.seq (.block [.addi t0 .a4 (-32)])
              (.ite (.zero t0) (.block subAll) (.block [])))
            (.block []))))
      (.seq (.block (loadLE32 t0 t1 .a0 0 ++ [xorR (q 0) (q 0) t0] ++ storeLE32 (q 0) t0 .a2 4 ++
          [.addi .a2 .a2 4, .addi .a0 .a0 4, .addi .a3 .a3 4, .sub t0 .a3 .a4]))
        (.seq (.ite (.zero t0) (.block [.li .a3 0]) (.block []))
          (.block [.addi .a1 .a1 (-1)]))))

def expandKey : Prog isa :=
  .seq (.block ([movR sb .a3] ++ roundSb ++ saveRegs ++ storeMasks bsSlot bsMasks ++
      [movR .a4 .a1]))
    (.seq (.loop (.block copyBody) (.nonzero .a1))
      (.seq (.block wordSetup)
        (.seq (.loop wordBody (.nonzero .a1)) (.block restoreRegs))))

end VG.Impl.Aes.RISCV64
