module

public import VerifiedGarbage.Impl.Gcm.RISCV64

/-! # Scalar RISC-V GHASH with an already bitsliced key
The caller supplies the 36 read-only operand words at `a0`. The four product spills
occupy bytes 0–31 of a 112-byte frame. Bytes 32–111 hold the saved registers.
-/

@[expose] public section
namespace VG.Impl.Gcm.RISCV64.Prepared
open VG VG.RISCV64

def compactSaved : List (Reg × Nat) := saved.map fun (r,off) => (r,off-288)
def compactSave : List Instr := compactSaved.map fun (r,off) => .store .d r .t0 off
def compactRestore : List Instr := compactSaved.map fun (r,off) => .load .d r .t0 off

def cachedBody : Prog isa :=
  .seq (.block (.addSp .t0 0 :: compactSave ++ [.addi FP HP 0, .addSp HP 0] ++ maskCode ++ loadY))
    (.seq (.loop (.block (blockCodeWith HP 0)) (.nonzero N))
      (.block (storeY ++ (.addSp .t0 0 :: compactRestore) ++ Impl.StackScratch.RISCV64.wipe 14)))

def cachedHash : Prog isa := .ite (.zero N) (.block []) (.frame (.alloc 112) cachedBody (.free 112))

def loadPrepared : List Instr := [.addSp .t0 0, .load .d .a0 .t0 16, .addi .a0 .a0 960]
def preparedInvocation : Prog isa := .seq (.block loadPrepared) (.call "vg_ghash_prepared" cachedHash)

end VG.Impl.Gcm.RISCV64.Prepared
