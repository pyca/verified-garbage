module

public import VerifiedGarbage.Impl.Dsa.X86.Validate

/-! # DSA signing and verification bodies after public shape validation

The ABI wrapper installs arguments and checks public shapes before these
bodies. The final mask controls signature bytes and the Boolean result;
secret-dependent validation never short-circuits the arithmetic schedule.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86.SignVerify
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout

def outputPointer (qLen : Nat) (second : Bool) : List Instr :=
  Core.pointer (.input .out) ++
    (if second then [.alu .add .esi (.imm (BitVec.ofNat 32 qLen))] else [])

def writeScalar (qLen input : Nat) (second : Bool) : Prog isa :=
  let n := (qLen + 7) / 8
  .seq (Core.load n qLen (slot n 5) (.local input))
    (.seq (.block (outputPointer qLen second ++ [.mov .ecx (.mem (sc (Layout.field .mask)))]))
      (storeComponent qLen (slot n 5)))

def result : List Instr := [.mov .eax (.mem (sc (Layout.field .mask))), .alu .and .eax (.imm 1)]

def signCompute (pLen qLen : Nat) : Prog isa := Core.sequence [
  Validate.publicKey pLen qLen,
  Validate.privateKey pLen qLen,
  Core.sign pLen qLen,
  .seq (Validate.zero qLen (.local r) true) (Validate.zero qLen (.local s) true)]

def signBody (pLen qLen : Nat) : Prog isa :=
  .seq (signCompute pLen qLen)
    (.seq (writeScalar qLen r false) (.seq (writeScalar qLen s true) (.block result)))

def verifyCompute (pLen qLen : Nat) : Prog isa := Core.sequence [
  Validate.publicKey pLen qLen,
  .seq (Validate.range qLen .q (.input .signature)) (Validate.range qLen .q .signatureS),
  Core.verify pLen qLen,
  Validate.equalValues qLen (.local u) (.input .signature)]

def verifyBody (pLen qLen : Nat) : Prog isa :=
  .seq (verifyCompute pLen qLen) (.block result)

end VG.Impl.Dsa.X86.SignVerify
