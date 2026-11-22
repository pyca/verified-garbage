module

public import VerifiedGarbage.Impl.ICall
public import VerifiedGarbage.TCB.Arm.Isa

/-!
# Calling a function by the address in a register, on ARMv7

A function that is the same code for every implementation of a function `n`
it calls calls `n` by its address, which its caller leaves in a register `r`
that none of its code writes: `blx r`, an indirect call of `n` alone
(`Code.icalls`), whose printed code does not name `n`.
-/

@[expose] public section

namespace VG.Impl.Arm

open VG.Arm

/-- `blx r`: the call of `n`, whose code is `b`, by the address in `r`. -/
def callReg (n : String) (r : Reg) (b : Prog isa) : Prog isa := Code.icalls (.blx r) [(n, b)]

/-- `c` with each call of `n` made a call by the address in `r`, in the bodies
of the functions it calls too: code that is the same for every
implementation of `n` it calls. -/
def Code.viaRegAt (n : String) (r : Reg) : Prog isa → Prog isa
  | .block is => .block is
  | .seq a b => .seq (viaRegAt n r a) (viaRegAt n r b)
  | .ite cd a b => .ite cd (viaRegAt n r a) (viaRegAt n r b)
  | .loop b cd => .loop (viaRegAt n r b) cd
  | .call m b => if m = n then callReg n r (viaRegAt n r b) else .call m (viaRegAt n r b)
  | .frame i b j => .frame i (viaRegAt n r b) j
  | .icall i m b nx => .icall i m b nx

end VG.Impl.Arm
