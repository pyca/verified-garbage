import VerifiedGarbage.Impl.Bignum.X86_64.AdxRotate8

/-! Propagate a raw-product carry through eight words at a time. -/
namespace VG.Impl.Bignum.X86_64.AdxCarry8
open VG.X86_64

def close : List Instr := [.mov32 .rbp (.imm 0), .adcx .rbp (.reg .rax)]

/-- `rbp` is the incoming word, `rcx` is zero, and `rbp` receives the carry. -/
def add : Prog isa :=
  .seq (.block [.alu32 .xor .rax (.reg .rax)])
    (.seq (.block (AdxRotate8.addChain (fun k => if k=0 then .reg .rbp else .reg .rcx)))
      (.block close))

def block8 : Prog isa :=
  .seq (.block AdxRotate8.loadCols) (.seq add (.block AdxRotate8.storeCols))

def advance : List Instr := [.alu .add .rsi (.imm 64), .alu .cmp .rsi (.reg .rdx)]

def step : Prog isa := .seq block8 (.block advance)

def propagate : Prog isa := .loop step .ne

end VG.Impl.Bignum.X86_64.AdxCarry8
