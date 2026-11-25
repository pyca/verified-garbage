module

public import VerifiedGarbage.Impl.Aes.RISCV64.Ctr32

/-!
# The AES key expansion on RISC-V

`vg_aes_expand_key_scratch(key = a0, key_len = a1, schedule = a2, scratch = a3)`
(`Proof/Aes/Contract.lean`): the key copied to the schedule, then a word at a
time (FIPS 197 §5.2).

SubWord needs no transpose: slice `j` of a word is the word shifted right by
`j`, whose bits 0, 8, 16 and 24 are bit `j` of its bytes, and the S-box does
not mix a slice's bits; the bits wanted of the result's slices are masked,
shifted back and added up. The scratch buffer (at `a5`, rounded) holds the
S-box's spills, the saved registers (slots 40–51), that mask (52) and the
round constant (58).
-/

@[expose] public section

namespace VG.Impl.Aes.RISCV64

open VG.RISCV64 VG.Impl.Words.RISCV64

def rconSlot : Nat := 58

/-- Bit 0 of the four bytes. -/
def ekMasks : List (Nat × BitVec 64) := [(1, 0x01010101)]

def subIn : List Instr := (List.range 7).map fun j => shrI (q (j + 1)) (q 0) (j + 1)

def subOut : List Instr :=
  [ldS t0 bsSlot, andR (q 0) (q 0) t0] ++
    (List.range 7).flatMap fun j =>
      [andR (q (j + 1)) (q (j + 1)) t0, shlI (q (j + 1)) (q (j + 1)) (j + 1), xorR (q 0) (q 0) (q (j + 1))]

/-- The S-box on the four bytes of the low half of `q 0`. -/
def subAll : List Instr := subIn ++ sboxCode ++ subOut

/-- `q 0` rotated by a byte, plus the round constant, which is doubled. -/
def rotTail : List Instr :=
  [.shift .srl .w t0 (q 0) 8, .shift .sll .w (q 0) (q 0) 24, xorR (q 0) (q 0) t0,
   ldS (q 1) rconSlot, xorR (q 0) (q 0) (q 1),
   shrI (q 2) (q 1) 7, .li (q 3) 0, .sub (q 3) (q 3) (q 2), .logicImm .and (q 3) (q 3) 0x1b,
   .add (q 1) (q 1) (q 1), xorR (q 1) (q 1) (q 3), .logicImm .and (q 1) (q 1) 0xff, stS rconSlot (q 1)]

/-- `SUBWORD(ROTWORD(temp)) ⊕ Rcon`. -/
def rotWordStep : List Instr := subAll ++ rotTail

/-- One word: the previous word is at `a2`, the one `Nk` back at `a0`; `a3` is
`4 (i mod Nk)`, `a4` is `4 Nk` and `a1` the words left. -/
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

/-- Eight bytes of the key copied. -/
def copyBody : List Instr :=
  copyBytes t0 .a0 .a2 0 0 8 ++ [.addi .a0 .a0 8, .addi .a2 .a2 8, .addi .a1 .a1 (-8)]

/-- The word loop's registers, and the round constant. -/
def wordSetup : List Instr :=
  [.sub .a0 .a2 .a4, .addi .a2 .a2 (-4), .li .a3 0, shrI t0 .a4 2, .add .a1 t0 t0, .add .a1 t0 .a1,
   .addi .a1 .a1 28, .li t0 1, stS rconSlot t0]

def expandKey : Prog isa :=
  .seq (.block ([movR sb .a3] ++ roundSb ++ saveRegs ++ storeMasks bsSlot ekMasks ++ [movR .a4 .a1]))
    (.seq (.loop (.block copyBody) (.nonzero .a1))
      (.seq (.block wordSetup)
        (.seq (.loop wordBody (.nonzero .a1)) (.block restoreRegs))))

end VG.Impl.Aes.RISCV64
