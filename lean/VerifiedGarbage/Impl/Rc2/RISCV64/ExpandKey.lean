module

public import VerifiedGarbage.Impl.Rc2.RISCV64.Lookup
public import VerifiedGarbage.Impl.Rc2.Table
public import VerifiedGarbage.Impl.Words.RISCV64.Word64

/-! # RC2 key expansion on RISC-V

`vg_rc2_expand_key(key = a0, key_len = a1, effective_bits = a2,
schedule = a3, scratch = a4)`, the algorithm of the PPC64LE implementation
(`Impl/Rc2/PPC64LE/ExpandKey.lean`). The expanded key's bytes `L` are built
in place in the schedule, a byte at a time. PITABLE is first written from
immediates into the first 256 bytes of the working space, which the
contracts align to 8 bytes (`Impl.Rc2.piQuads`), and each lookup scans it
whole (`piLookup`, `Lookup.lean`). Only the public lengths control the loops
and the branches; `a5` counts through `L`, `a6` holds addresses, `t4` holds
`T8` and `t3` is the scans' row pointer. Only temporaries and argument
registers are used, and no stack.
-/

@[expose] public section

namespace VG.Impl.Rc2.RISCV64

open VG.RISCV64
open VG.Impl.Words.RISCV64 (li64)

/-- PITABLE's 32 doublewords into the working space, through `t0` and `t1`. -/
def piInit : List Instr :=
  (List.range 32).flatMap fun k => li64 .t0 .t1 (Impl.Rc2.piQuad k) ++ [.store .d .t0 .a4 (8 * k)]

/-- `t1 := PITABLE[q]`, the byte at offset `q` (in `t0`) of the table in
the working space. -/
def piLookup : Prog isa := scan .a4 32 7 8

/-- `L[i] := key[i]`, the next `i`; `a7` is zero at the key's length. -/
def copyKey : List Instr :=
  [.add .a6 .a0 .a5, .load .b .t2 .a6 0, .add .a6 .a3 .a5, .store .b .t2 .a6 0, .addi .a5 .a5 1,
   .sub .a7 .a5 .a1]

/-- `q := L[i - 1] + L[i - T]` (mod 256). -/
def fillInput : List Instr :=
  [.add .a6 .a3 .a5, .addi .a6 .a6 (-1), .load .b .t0 .a6 0, .sub .a6 .a5 .a1, .add .a6 .a3 .a6,
   .load .b .t1 .a6 0, .add .t0 .t0 .t1] ++ mask .t0 8

/-- `L[i] := t1`. -/
def storeKey : List Instr := [.add .a6 .a3 .a5, .store .b .t1 .a6 0]

/-- After `L[i]`, the next `i`; `a7` is zero at 128. -/
def fillFinish : List Instr := storeKey ++ ([.addi .a5 .a5 1, .li .a7 128, .sub .a7 .a5 .a7] : List Instr)

def fillKey : Prog isa := .seq (.block fillInput) (.seq piLookup (.block fillFinish))

/-- `TM` into `t2`: 255, or `2 ^ c - 1` for `c = effective_bits mod 8`
when it is not 0, chosen by branches on the public `c` (in `a6`). -/
def maskCode : Prog isa :=
  .seq (.block [.shift .sll .d .a6 .a2 61, .shift .srl .d .a6 .a6 61, .li .t2 255])
    ((List.range 7).foldr (fun c rest =>
      .seq (.block [.addi .t0 .a6 (-((c + 1 : Nat) : Int))])
        (.seq (.ite (.zero .t0) (.block [.li .t2 ((2 ^ (c + 1) - 1 : Nat) : Int)]) (.block [])) rest))
      (.block []))

/-- `T8` into `t4`, and `i := 128 - T8`. -/
def reduceSetup : List Instr :=
  [.addi .t4 .a2 7, .shift .srl .d .t4 .t4 3, .li .a5 128, .sub .a5 .a5 .t4]

/-- `q := L[i] AND TM`. -/
def reduceInput : List Instr := [.add .a6 .a3 .a5, .load .b .t0 .a6 0, .logic .and .t0 .t0 .t2]

def reduceKey : Prog isa := .seq (.block reduceInput) (.seq piLookup (.block storeKey))

/-- The previous `i`, and `q := L[i + 1] XOR L[i + T8]`. -/
def descendInput : List Instr :=
  [.addi .a5 .a5 (-1), .add .a6 .a3 .a5, .load .b .t0 .a6 1, .add .a6 .a5 .t4, .add .a6 .a3 .a6,
   .load .b .t1 .a6 0, .logic .xor .t0 .t0 .t1]

def descendKey : Prog isa := .seq (.block descendInput) (.seq piLookup (.block storeKey))

def expandCopyFill : Prog isa :=
  .seq (.loop (.block copyKey) (.nonzero .a7))
    (.seq (.block [.li .a7 128, .sub .a7 .a5 .a7])
      (.ite (.zero .a7) (.block []) (.loop fillKey (.nonzero .a7))))

def expandReduce : Prog isa :=
  .seq (.block reduceSetup)
    (.seq maskCode (.seq reduceKey (.ite (.zero .a5) (.block []) (.loop descendKey (.nonzero .a5)))))

def expandKey : Prog isa :=
  .seq (.block (piInit ++ [.li .a5 0])) (.seq expandCopyFill expandReduce)

end VG.Impl.Rc2.RISCV64
