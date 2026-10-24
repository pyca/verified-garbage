module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Policy

/-! Backend-independent public context: p/R² and all 32 five-tooth comb entries.
The layout is the existing reviewed generationPrecompute representation. -/
@[expose] public section
namespace VG.Impl.Ffdh.AArch64.Cached.Precompute
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64

def entry : List Instr := [st .x0 .x5 (8*sCtx),st .x2 .x5 (8*sDom),st .x3 .x5 (8*sDL),
 st .x4 .x5 (8*sLen),mov .x0 .x5]

def storePrefix : Prog isa := seqs [
 .block [ldh .x17 sCtx,.addImm .x .x17 .x17 24,ldh .x16 (sArr 0),ldh .x12 sW],copyWords,
 .block [ldh .x16 (sArr 4),ldh .x12 sW],copyWords]

def initial (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
 const 7 1,mul 6 4 7,.block [movi .x3 0],storeEntry 6,
 .block [ldh .x1 sDom,ldh .x2 sLen,.add .x .x1 .x1 .x2],load 1,
 mul 5 1 4,.block [movi .x3 1],storeEntry 5]

def squares (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
 .seq (copy 6 5) (.seq (.block [ldh .x3 sRows,sth .x3 sI])
 (.seq (.loop (.seq (mul 6 6 6) (.block [ldh .x3 sI,.subImm .x .x3 .x3 1,sth .x3 sI])) (.nonzero .x .x3)) (copy 5 6)))

def productLoad : Prog isa := .seq (.block [ldh .x3 sJ]) (loadEntry 1)

def productStore : Prog isa := .seq (.block [ldh .x3 sJ,ldh .x4 sD,.add .x .x3 .x3 .x4]) (storeEntry 6)

def productNext : List Instr := [ldh .x3 sJ,.addImm .x .x3 .x3 1,sth .x3 sJ,
 ldh .x4 sD,.sub .x .x3 .x3 .x4]

def product (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
 .seq productLoad (.seq (mul 6 5 1) (.seq productStore (.block productNext)))

def basisNext : List Instr := [ldh .x3 sD,.lsl .x .x3 .x3 1,sth .x3 sD,.subImm .x .x3 .x3 32]

def basis (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
 .seq (squares mul) (.seq (.block [ldh .x3 sD]) (.seq (storeEntry 5)
 (.seq (.block [movi .x3 1,sth .x3 sJ]) (.seq (.loop (product mul) (.nonzero .x .x3))
 (.block basisNext)))))

def table (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
 .seq (initial mul) (.seq (.block [movi .x3 2,sth .x3 sD]) (.loop (basis mul) (.nonzero .x .x3)))

def code (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
 .seq (.block entry) (.seq Policy.recognize (.seq Policy.metadata
 (.seq (seqs (VG.Impl.Rsa.AArch64.pcLoadW ++ VG.Impl.Rsa.AArch64.r2StepsPub mul))
 (.seq storePrefix (.seq (table mul) (.block [movi .x0 1]))))))

end VG.Impl.Ffdh.AArch64.Cached.Precompute
