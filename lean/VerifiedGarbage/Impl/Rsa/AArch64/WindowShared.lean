module

public import VerifiedGarbage.Impl.Bignum.AArch64.WindowArithmetic
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowSelectVector
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowFive

/-! A five-square private window with one register-save boundary. Intermediate
squares stay below the limb radix; the last product is canonical. -/

@[expose] public section
namespace VG.Impl.Rsa.AArch64.WindowShared
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64

def vecs : List VReg := [.v0,.v1,.v2,.v3,.v4,.v5,.v6,.v27,.v28,.v29,.v30]
def save : List Instr := (BlockedRedc.saved.zip vecs).map fun (r,v) => .vop (.ins .d2 v 0 r)
def restore : List Instr := (BlockedRedc.saved.zip vecs).map fun (r,v) => .umov .x r v 0

def step : Prog isa := .seq (WindowArithmetic.square 6)
  (.block [ldh .x3 Crt.sBit, .subImm .x .x3 .x3 1, sth .x3 Crt.sBit])
def squares : Prog isa := .loop step (.nonzero .x .x3)
def core : Prog isa := .seq squares
  (.seq (WindowSelectVector.vector 32) (WindowArithmetic.product 6 6 5))
def work : Prog isa := .seq (.block [movi .x3 5, sth .x3 Crt.sBit]) core
def fast : Prog isa := .seq (.block save)
  (.seq work (.seq (.block restore) (.block WindowFive.resetWindow)))
def guard : List Instr :=
 [ldh .x12 sW, .lsr .x .x3 .x12 4, movi .x4 7, .logic .and .x .x4 .x12 .x4]
def code (fallback : Prog isa) : Prog isa :=
 .seq (.block guard)
  (.ite (.nonzero .x .x3) (.ite (.zero .x .x4) fast fallback) fallback)

end VG.Impl.Rsa.AArch64.WindowShared
