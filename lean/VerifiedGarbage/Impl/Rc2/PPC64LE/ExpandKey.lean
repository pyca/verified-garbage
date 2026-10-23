module

public import VerifiedGarbage.Impl.Rc2.PPC64LE.Lookup
public import VerifiedGarbage.Impl.Rc2.Table

/-! # RC2 key expansion on PPC64LE

`vg_rc2_expand_key(key = r3, key_len = r4, effective_bits = r5,
schedule = r6, scratch = r7)`. The expanded key's bytes `L` are built in
place in the schedule. PITABLE is first written from immediates into the
first 256 bytes of the working space (`Impl.Rc2.piQuads`), and each lookup
scans it whole (`piLookup`, `Lookup.lean`); our caller's `r14` and `r15`
are kept after it. Only the public lengths control the loops and the
branches; `r8` counts through `L`, `r9` holds addresses, `r14` holds `T8`
and `r15` is the scans' row pointer.
-/

@[expose] public section

namespace VG.Impl.Rc2.PPC64LE

open VG.PPC64LE

/-- `r15` and `r14`, to the working space after PITABLE. -/
def keySave : List Instr := [.store .d .r14 .r7 256, .store .d .r15 .r7 264]

def keyRestore : List Instr := [.load .d .r14 .r7 256, .load .d .r15 .r7 264]

/-- `d := v` for a 64-bit constant: the high word with `lis` and `ori`,
shifted up by `sldi`, then the low word with `oris` and `ori`. -/
def movImm64 (d : Reg) (v : BitVec 64) : List Instr :=
  [.lis d (v.extractLsb' 48 16), .ori d d (v.extractLsb' 32 16), .lsl d d 32,
   .oris d d (v.extractLsb' 16 16), .ori d d (v.extractLsb' 0 16)]

/-- PITABLE's 32 doublewords into the working space. -/
def piInit : List Instr :=
  (List.range 32).flatMap fun k => movImm64 .r12 (Impl.Rc2.piQuad k) ++ [.store .d .r12 .r7 (8 * k)]

/-- `r11 := PITABLE[q]`, the byte at offset `q` (in `r10`) of the table in
the working space. -/
def piLookup : Prog isa := scan .r7 .r15 32 [0, 1, 2] 8

/-- `L[i] := key[i]`, the next `i`; `r0` is zero at the key's length. -/
def copyKey : List Instr :=
  [.add .r9 .r3 .r8, .lbz .r12 .r9 0, .add .r9 .r6 .r8, .stb .r12 .r9 0, .addi .r8 .r8 1, .sub .r0 .r8 .r4]

/-- `q := L[i - 1] + L[i - T]` (mod 256). -/
def fillInput : List Instr :=
  [.add .r9 .r6 .r8, .subi .r9 .r9 1, .lbz .r10 .r9 0, .sub .r9 .r8 .r4, .add .r9 .r6 .r9, .lbz .r11 .r9 0,
   .add .r10 .r10 .r11] ++ mask .r10 8

/-- `L[i] := r11`. -/
def storeKey : List Instr := [.add .r9 .r6 .r8, .stb .r11 .r9 0]

/-- After `L[i]`, the next `i`; `r0` is zero at 128. -/
def fillFinish : List Instr := storeKey ++ ([.addi .r8 .r8 1, .li .r0 128, .sub .r0 .r8 .r0] : List Instr)

def fillKey : Prog isa := .seq (.block fillInput) (.seq piLookup (.block fillFinish))

/-- `TM` into `r12`: 255, or `2 ^ c - 1` for `c = effective_bits mod 8`
when it is not 0, chosen by branches on the public `c` (in `r9`). -/
def maskCode : Prog isa :=
  .seq (.block [.lsl .r9 .r5 61, .lsr .d .r9 .r9 61, .li .r12 255])
    ((List.range 7).foldr (fun c rest =>
      .seq (.block [.subi .r10 .r9 (c + 1)])
        (.seq (.ite (.zero .d .r10) (.block [.li .r12 (2 ^ (c + 1) - 1)]) (.block [])) rest)) (.block []))

/-- `T8` into `r14`, and `i := 128 - T8`. -/
def reduceSetup : List Instr := [.addi .r14 .r5 7, .lsr .d .r14 .r14 3, .li .r8 128, .sub .r8 .r8 .r14]

/-- `q := L[i] AND TM`. -/
def reduceInput : List Instr := [.add .r9 .r6 .r8, .lbz .r10 .r9 0, .logic .and .r10 .r10 .r12]

def reduceKey : Prog isa := .seq (.block reduceInput) (.seq piLookup (.block storeKey))

/-- The previous `i`, and `q := L[i + 1] XOR L[i + T8]`. -/
def descendInput : List Instr :=
  [.subi .r8 .r8 1, .add .r9 .r6 .r8, .lbz .r10 .r9 1, .add .r9 .r8 .r14, .add .r9 .r6 .r9, .lbz .r11 .r9 0,
   .logic .xor .r10 .r10 .r11]

def descendKey : Prog isa := .seq (.block descendInput) (.seq piLookup (.block storeKey))

def expandCopyFill : Prog isa :=
  .seq (.loop (.block copyKey) (.nonzero .d .r0))
    (.seq (.block [.li .r0 128, .sub .r0 .r8 .r0])
      (.ite (.zero .d .r0) (.block []) (.loop fillKey (.nonzero .d .r0))))

def expandReduce : Prog isa :=
  .seq (.block reduceSetup)
    (.seq maskCode (.seq reduceKey (.ite (.zero .d .r8) (.block []) (.loop descendKey (.nonzero .d .r8)))))

def expandKey : Prog isa :=
  .seq (.block (keySave ++ piInit ++ [.li .r8 0])) (.seq expandCopyFill (.seq expandReduce (.block keyRestore)))

end VG.Impl.Rc2.PPC64LE
