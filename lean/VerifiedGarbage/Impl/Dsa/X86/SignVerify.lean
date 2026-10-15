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

def writeScalar (qLen input : Nat) (second : Bool) : List Instr :=
  let n := (qLen + 7) / 8
  Core.load n qLen (slot n 5) (.local input) ++ outputPointer qLen second ++
    ([.mov .ecx (.mem (sc (Layout.field .mask)))] : List Instr) ++ storeComponent qLen n (slot n 5)

def result : List Instr := [.mov .eax (.mem (sc (Layout.field .mask))), .alu .and .eax (.imm 1)]

def signCompute (pLen qLen digestLen : Nat) : Prog isa := Core.sequence [
  Validate.publicKey pLen qLen,
  Validate.privateKey pLen qLen,
  Core.sign pLen qLen digestLen,
  .block (Validate.zero qLen (.local r) true ++ Validate.zero qLen (.local s) true)]

def signBody (pLen qLen digestLen : Nat) : Prog isa :=
  .seq (signCompute pLen qLen digestLen) (.block (writeScalar qLen r false ++ writeScalar qLen s true ++ result))

def verifyCompute (pLen qLen digestLen : Nat) : Prog isa := Core.sequence [
  Validate.publicKey pLen qLen,
  .block (Validate.range qLen .q (.input .signature) ++ Validate.range qLen .q .signatureS),
  Core.verify pLen qLen digestLen,
  .block (Validate.equalValues qLen (.local u) (.input .signature))]

def verifyBody (pLen qLen digestLen : Nat) : Prog isa :=
  .seq (verifyCompute pLen qLen digestLen) (.block result)

end VG.Impl.Dsa.X86.SignVerify
