module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Layout

/-! Five-tooth comb: one square, one constant-time table scan and one product per row.
All five bit addresses and loop counts depend on the public policy width only. -/
@[expose] public section
namespace VG.Impl.Ffdh.AArch64.Cached.Comb
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64

/-- Public shift count in x10, at most seven. -/
def shift : Prog isa := .loop (.block [.lsr .x .x11 .x11 1,.subImm .x .x10 .x10 1]) (.nonzero .x .x10)

def load : List Instr := [.lsr .x .x8 .x9 3,.sub .x .x8 .x2 .x8,.subImm .x .x8 .x8 1,
   .add .x .x8 .x1 .x8,.ldrb .x11 .x8 0,movi .x10 7,.logic .and .x .x10 .x9 .x10]

def bit : Prog isa := .seq (.block [.sub .x .x8 .x9 .x5,.lsr .x .x8 .x8 63])
 (.ite (.nonzero .x .x8)
  (.seq (.block load)
   (.seq (.ite (.zero .x .x10) (.block []) shift)
    (.block [movi .x10 1,.logic .and .x .x11 .x11 .x10])))
  (.block [movi .x11 0]))

def tooth (j : Nat) : Prog isa := .seq bit (.block
 ((if j=0 then [] else [.lsl .x .x11 .x11 j]) ++
 [.logic .orr .x .x16 .x16 .x11,.add .x .x9 .x9 .x4]))

def gather : Prog isa := seqs ((List.range 5).map tooth)

def digit : Prog isa := .seq (.block [ldh .x1 sX,ldh .x2 sLen,ldh .x9 sI,
 .subImm .x .x9 .x9 1,ldh .x4 sRows,ldh .x5 sBits,movi .x16 0])
 (.seq gather (.block [sth .x16 sD]))

/-- Scan every entry in order, hoisting one secret mask outside its limb loop. -/
def selectWord : List Instr := [ld .x3 .x9,ld .x4 .x8,.logic .and .x .x3 .x3 .x6,
 .logic .orr .x .x4 .x4 .x3,st .x4 .x8,next .x9,next .x8]

def selectHead : List Instr := [ldh .x8 (sArr 5),ldh .x12 sW,
 .logic .eor .x .x3 .x10 .x11,movi .x7 0,.subs .x .x3 .x3 .x7,
 .subImm .x .x6 .x7 1,.cselc .x .x6 .x6 .x7 .eq]

def selectStep : Prog isa := .seq (.block selectHead)
 (.seq (countLoop .x12 selectWord)
 (.block [.addImm .x .x11 .x11 1,.subImm .x .x3 .x11 32]))

def select : Prog isa := .seq (const 5 0)
 (.seq (.block [ldh .x9 sTab,ldh .x10 sD,movi .x11 0]) (.loop selectStep (.nonzero .x .x3)))

def step (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
 .seq (mul 6 6 6) (.seq digit (.seq select (.seq (mul 6 6 5)
 (.block [ldh .x3 sI,.subImm .x .x3 .x3 1,sth .x3 sI]))))

def initCounter : List Instr := [ldh .x3 sRows,sth .x3 sI]

def initTable : List Instr := [ldh .x3 sCtx,ldh .x4 sW,
 .lsl .x .x4 .x4 4,.add .x .x3 .x3 .x4,.addImm .x .x3 .x3 24,sth .x3 sTab]

def code (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
 .seq (const 7 1) (.seq (mul 6 4 7)
 (.seq (.block initCounter) (.seq (.block initTable)
 (.seq (.loop (step mul) (.nonzero .x .x3)) (mul 6 6 7)))))

end VG.Impl.Ffdh.AArch64.Cached.Comb
