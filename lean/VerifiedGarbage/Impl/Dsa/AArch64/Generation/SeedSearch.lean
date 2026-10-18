module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Subgroup
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.GeneratorSearch
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Validate

/-! Native seed attempts and the complete finite parameter search. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)

def seedArguments (qLen : Nat) : List Instr :=
  [.ldrSp .x3 40, movi .x4 VG.Impl.Dsa.Generation.Layout.q, .add .x .x3 .x3 .x4,
   .strSp .x3 0, .ldrSp .x3 8, .strSp .x3 sLab, movi .x3 qLen, .strSp .x3 sLabLen]

def successStatus : List Instr := [.ldrSp .x3 152, .subImm .x .x3 .x3 1]

def onSuccess (next : Prog isa) : Prog isa :=
  .seq (.block successStatus) (.ite (.zero .x .x3) next (.block []))

def finishDomain (mul : Nat → Nat → Nat → Prog isa) (pLen qLen : Nat) : Prog isa :=
  .seq (pack pLen qLen) (validate mul pLen qLen)

def seedAttempt (G1 G256 : Hash) (mul : Nat → Nat → Nat → Prog isa)
    (roundCode : List (Prog isa)) (pLen qLen : Nat) : Prog isa :=
  .seq (.seq (.block (seedArguments qLen)) (subgroup G1 G256 mul roundCode qLen))
    (onSuccess (.seq (primeSearch G1 G256 mul roundCode pLen qLen)
      (onSuccess (.seq (generatorSearch mul pLen) (onSuccess (finishDomain mul pLen qLen))))))

def parameterSearch (G1 G256 : Hash) (mul : Nat → Nat → Nat → Prog isa)
    (roundCode : List (Prog isa)) (pLen qLen : Nat) : Prog isa :=
  tapeLoop seedTape qLen (seedAttempt G1 G256 mul roundCode pLen qLen)

end VG.Impl.Dsa.AArch64.Generation
