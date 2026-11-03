module

public import VerifiedGarbage.Impl.Bignum.Arm.RowUmaal
public import VerifiedGarbage.Impl.Bignum.Arm.DownRowUmaal
public import VerifiedGarbage.Impl.Bignum.Arm.DownRow

/-! Optimize an ARMv7 caller's inlined Montgomery product and fused
reduction rows while leaving its named callees unchanged. The generic caller already selects each callee's
matching backend; replacing its body again would change that binding. -/

@[expose] public section
namespace VG.Impl.Ffdh.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

def callerRows : Prog isa → Prog isa
  | .block is => if .block is = row then rowU else
      if .block is = DownRow.code then DownRow.codeU else .block is
  | .seq x y => if .seq x y = row then rowU else
      if .seq x y = DownRow.code then DownRow.codeU else .seq (callerRows x) (callerRows y)
  | .ite k t e => if .ite k t e = row then rowU else
      if .ite k t e = DownRow.code then DownRow.codeU else .ite k (callerRows t) (callerRows e)
  | .loop x k => if .loop x k = row then rowU else
      if .loop x k = DownRow.code then DownRow.codeU else .loop (callerRows x) k
  | .call n x => .call n x
  | .frame i x j => if .frame i x j = row then rowU else
      if .frame i x j = DownRow.code then DownRow.codeU else .frame i (callerRows x) j
  | .icall i n x y => .icall i n x y

end VG.Impl.Ffdh.Arm
