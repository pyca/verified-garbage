module

public import VerifiedGarbage.Impl.Bignum.Arm.RowUmaal

/-! Optimize an ARMv7 caller's inlined Montgomery rows while leaving its
named callees unchanged. The generic caller already selects each callee's
matching backend; replacing its body again would change that binding. -/

@[expose] public section
namespace VG.Impl.Ffdh.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

def callerRows : Prog isa → Prog isa
  | .block is => if .block is = row then rowU else .block is
  | .seq x y => if .seq x y = row then rowU else .seq (callerRows x) (callerRows y)
  | .ite k t e => if .ite k t e = row then rowU else .ite k (callerRows t) (callerRows e)
  | .loop x k => if .loop x k = row then rowU else .loop (callerRows x) k
  | .call n x => .call n x
  | .frame i x j => if .frame i x j = row then rowU else .frame i (callerRows x) j

end VG.Impl.Ffdh.Arm
