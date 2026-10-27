module

public import VerifiedGarbage.Impl.Scrypt.AArch64.Salsa

/-! Register-resident BlockMix. Salsa's sixteen scalar words remain live
between blocks. Each input XOR is written to its final output slot, which
also supplies Salsa's feed-forward input; no redundant reload of the state
or call of the standalone Salsa function is needed. -/

@[expose] public section
namespace VG.Impl.Scrypt.AArch64.Resident
open VG VG.AArch64
open VG.Impl.Scrypt.AArch64 (wreg rounds)

def mov (d n : Reg) : Instr := .addImm .x d n 0

def saved : List (Reg × Nat) :=
  [(.x19, 64), (.x20, 72), (.x21, 80), (.x23, 88), (.x24, 96), (.x22, 104)]

def prologue : List Instr := saved.map (fun (r,d) => .str .x r .x4 d) ++
 [mov .x23 .x1,mov .x19 .x0,mov .x20 .x2,mov .x22 .x4,
 .lsl .x .x9 .x1 6,.add .x .x21 .x2 .x9,
 .lsl .x .x9 .x1 7,.add .x .x24 .x0 .x9,.subImm .x .x24 .x24 64]

def loadWord (k : Nat) : Instr := .ldr .w (wreg k) .x24 (4*k)
def load : List Instr := (List.range 16).map loadWord

def xorWord (out : Reg) (k : Nat) : List Instr :=
 [.ldr .w .x1 .x19 (4*k),.logic .eor .w (wreg k) (wreg k) .x1,
 .str .w (wreg k) out (4*k)]

def finishWord (out : Reg) (k : Nat) : List Instr :=
 [.ldr .w .x1 out (4*k),.add .w (wreg k) (wreg k) .x1,.str .w (wreg k) out (4*k)]

def step (out : Reg) : Prog isa :=
 .seq (.block ((List.range 16).flatMap (xorWord out)))
 (.seq (rounds 4) (.block ((List.range 16).flatMap (finishWord out))))

def tail : List Instr := [mov .x24 .x21,.addImm .x .x19 .x19 64,
 .addImm .x .x20 .x20 64,.addImm .x .x21 .x21 64,.subImm .x .x23 .x23 1]

def body : Prog isa := .seq (step .x20)
 (.seq (.block [.addImm .x .x19 .x19 64]) (.seq (step .x21) (.block tail)))

def epilogue : List Instr := saved.map (fun (r,d) => .ldr .x r .x22 d)

def main : Prog isa := .seq (.block (prologue ++ load))
 (.seq (.loop body (.nonzero .x .x23)) (.block epilogue))

/-- Retain the existing sixteen-byte stack bound and return-address frame. -/
def code : Prog isa := .frame (.push .x30) main (.pop .x30)
end VG.Impl.Scrypt.AArch64.Resident
