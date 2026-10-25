module

public import VerifiedGarbage.Impl.Dsa.Arm.PublicValidation

/-! # DSA signing and verification bodies after public shape validation

The entry installs the arguments and checks public shapes before these
bodies. The final mask controls the signature bytes and the result;
secret-dependent validation never short-circuits the arithmetic schedule.
-/

@[expose] public section
namespace VG.Impl.Dsa.Arm.SignVerify
open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Impl.Dsa.Layout

def outputPointer (qLen : Nat) (second : Bool) : List Instr :=
  Core.pointer (.input .out) ++
    (if second then [.movw .r4 (BitVec.ofNat 16 qLen), .dp .add .r11 .r11 (.reg .r4)] else [])

def writeScalar (qLen input : Nat) (second : Bool) : Prog isa :=
  let n := (qLen + 7) / 8
  .seq (Core.load n qLen (baseS n) (.local input))
    (.seq (.block (outputPointer qLen second ++ [.ldr .r3 .r12 (Layout.field .mask)]))
      (storeComponent qLen (baseS n)))

def result : List Instr := [.ldr .r0 .r12 (Layout.field .mask), .dp .and .r0 .r0 (.imm 1)]

def signCompute (pLen qLen : Nat) : Prog isa := Core.sequence [
  Validate.signingKey pLen qLen,
  Validate.privateKey pLen qLen,
  Core.sign pLen qLen,
  .seq (Validate.zero qLen (.local r) true) (Validate.zero qLen (.local s) true)]

def signBody (pLen qLen : Nat) : Prog isa :=
  .seq (signCompute pLen qLen)
    (.seq (writeScalar qLen r false) (.seq (writeScalar qLen s true) (.block result)))

def verifyCompute (pLen qLen : Nat) : Prog isa := Core.sequence [
  PublicValidation.call pLen qLen,
  .seq (Validate.range qLen .q (.input .signature)) (Validate.range qLen .q .signatureS),
  Core.verify pLen qLen,
  Validate.equalValues qLen (.local u) (.input .signature)]

def verifyBody (pLen qLen : Nat) : Prog isa :=
  .seq (verifyCompute pLen qLen) (.block result)

end VG.Impl.Dsa.Arm.SignVerify
