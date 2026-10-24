module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Comb
public import VerifiedGarbage.Impl.Ffdh.AArch64.Domain

/-! Cached generation keeps the reviewed scalar/status policy and public schedule.
A validated generator's powers already satisfy its subgroup relation. -/
@[expose] public section
namespace VG.Impl.Ffdh.AArch64.Cached.Generate
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64

/-- The cached API's context is its fourth stack argument. -/
def entry : List Instr := [.ldrSp .x8 8,.ldrSp .x9 24,
 st .x0 .x8 (8*sX),st .x2 .x8 (8*sY),st .x4 .x8 (8*sDom),st .x5 .x8 (8*sDL),
 st .x6 .x8 (8*sLen),st .x7 .x8 (8*sRand),st .x9 .x8 (8*sCtx),mov .x0 .x8,
 ld .x10 .x9 0,ld .x11 .x9 8,ld .x12 .x9 16,
 sth .x10 sBits,sth .x11 sBytes,sth .x12 sRows]

/-- Public byte mask, including the full-byte case. -/
def mask : Prog isa := .seq (.block [ldh .x3 sBits,.subImm .x .x3 .x3 1,
 movi .x4 7,.logic .and .x .x3 .x3 .x4,.sub .x .x3 .x4 .x3,movi .x12 255])
 (.seq (.ite (.zero .x .x3) (.block [])
 (.loop (.block [.lsr .x .x12 .x12 1,.subImm .x .x3 .x3 1]) (.nonzero .x .x3)))
 (.block [sth .x12 sMask]))

def sample : Prog isa := .seq mask (.seq (.block [ldh .x10 sLen,ldh .x11 sBytes,
 .sub .x .x11 .x10 .x11,ldh .x2 sX,ldh .x1 sRand,movi .x13 255,movi .x7 0,
 movi .x10 0,ldh .x14 sLen]) (countLoop .x14 VG.Impl.Ffdh.AArch64.Domain.GenerateKey.cutBody))

/-- q, or p-1, into array 5 without computing any secret-dependent width. -/
def bound : Prog isa := .seq (.block [ldh .x1 sDom,ldh .x2 sLen,ldh .x3 sDL,
 .lsl .x .x4 .x2 1,.sub .x .x3 .x3 .x4])
 (.ite (.zero .x .x3)
  (.seq (copy 5 0) (.block [ldh .x8 (sArr 5),ld .x3 .x8,.subImm .x .x3 .x3 1,st .x3 .x8]))
  (.seq (.block [.add .x .x1 .x1 .x4]) (load 5)))

/-- Strict comparison, with 1 in x9 exactly on a borrow. -/
def less (a b : Nat) : Prog isa := .seq (.block [ldh .x16 (sArr a),ldh .x17 (sArr b),
 ldh .x14 sW,movi .x7 0,.subs .x .x3 .x7 .x7])
 (.seq cmpLoop (.block [movi .x4 1,.csel .x .x9 .x7 .x4]))

def nonzero : Prog isa := .seq (.block [ldh .x8 (sArr 1),ldh .x12 sW,movi .x9 0])
 (.seq (countLoop .x12 [ld .x3 .x8,.logic .orr .x .x9 .x9 .x3,next .x8])
 (.block [movi .x3 0,movi .x4 1,.subs .x .x9 .x9 .x3,.cselc .x .x9 .x3 .x4 .eq,sth .x9 sTmp]))

def scalarRange : Prog isa := seqs [
 .block [ldh .x1 sX,ldh .x2 sLen],load 1,nonzero,bound,less 1 5,
 .block [ldh .x3 sTmp,.logic .and .x .x9 .x9 .x3]]

/-- p odd implies y < p-1 iff (y OR 1) < p. -/
def publicRange : Prog isa := seqs [less 7 6,.block [sth .x9 sTmp],copy 1 6,
 .block [ldh .x8 (sArr 1),ld .x3 .x8,movi .x4 1,.logic .orr .x .x3 .x3 .x4,st .x3 .x8],
 less 1 0,.block [ldh .x3 sTmp,.logic .and .x .x9 .x9 .x3,sth .x9 sTmp]]

def clear (slot : Nat) : Prog isa := .seq (.block [ldh .x1 slot,ldh .x2 sLen,movi .x3 0])
 (countLoop .x2 [.strb .x3 .x1 0,.addImm .x .x1 .x1 1])

def fail : Prog isa := .seq (clear sX) (.seq (clear sY) (.block [movi .x0 2]))

def maskX : Prog isa := .seq (.block [ldh .x1 sX,ldh .x2 sLen,ldh .x3 sTmp,
 movi .x7 0,.sub .x .x15 .x7 .x3])
 (countLoop .x2 [.ldrb .x3 .x1 0,.logic .and .x .x3 .x3 .x15,.strb .x3 .x1 0,.addImm .x .x1 .x1 1])

def finish : Prog isa := seqs [maskX,
 .block [ldh .x8 (sArr 6),ldh .x1 sY,ldh .x9 sLen,.add .x .x1 .x1 .x9],storeBE,
 .block [ldh .x9 sTmp,movi .x0 3,.lsl .x .x9 .x9 1,.sub .x .x0 .x0 .x9]]

def code (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
 .seq (.block entry) (.seq importPrefix (.seq sample (.seq scalarRange
 (.ite (.zero .x .x9) fail (.seq (Comb.code mul) (.seq publicRange finish))))))

end VG.Impl.Ffdh.AArch64.Cached.Generate
