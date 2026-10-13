module

public import VerifiedGarbage.Impl.Weierstrass.AArch64.NafPrep

/-! Sparse public width-five and width-seven NAF recoding. -/

@[expose] public section

namespace VG.Impl.Weierstrass.AArch64.FastNaf
open VG VG.AArch64 VG.Impl.Mont.AArch64

def shift (w : Nat) : List Instr :=
  [.extr .x .x5 .x6 .x5 w,.extr .x .x6 .x7 .x6 w,
   .extr .x .x7 .x8 .x7 w,.extr .x .x8 .x9 .x8 w,.lsr .x .x9 .x9 w]
def remain : List Instr :=
  [.logic .orr .x .x19 .x5 .x6,.logic .orr .x .x19 .x19 .x7,
   .logic .orr .x .x19 .x19 .x8,.logic .orr .x .x19 .x19 .x9]
def init (K : WinCfg) (src w : Nat) : List Instr :=
  [ld .x5 src,ld .x6 (src+8),ld .x7 (src+16),ld .x8 (src+24),
   .movz .x .x9 0 0,.movz .x .x10 (BitVec.ofNat 16 (2^w-1)) 0,
   .movz .x .x11 (BitVec.ofNat 16 (2^(w-1))) 0,.movz .x .x12 0 0,
   .movz .x .x13 1 0,.movz .x .x19 257 0,.addImm .x .x20 .x0 K.bits]

def clear (K : WinCfg) : List Instr :=
  (List.range 33).map fun i => st .x12 (K.bits+8*i)

def choose : List Instr :=
  [.logic .and .x .x2 .x5 .x10,.logic .and .x .x3 .x2 .x11,
   .lsl .x .x3 .x3 1,.sub .x .x2 .x2 .x3]

def odd (w : Nat) : List Instr :=
  choose ++ ([.strb .x2 .x20 0] : List Instr) ++ Naf.subtractShift.take 7 ++
    shift w ++ ([.addImm .x .x20 .x20 w] : List Instr)

def even : List Instr := shift 1 ++ ([.addImm .x .x20 .x20 1] : List Instr)

def step (w : Nat) : Prog isa :=
  .seq (.block [.logic .and .x .x1 .x5 .x13]) <|
  .seq (.ite (.nonzero .x .x1) (.block (odd w)) (.block even)) (.block remain)

def prep (K : WinCfg) (src w : Nat) : Prog isa :=
  .seq (.block (init K src w ++ clear K)) (.loop (step w) (.nonzero .x .x19))
end VG.Impl.Weierstrass.AArch64.FastNaf
