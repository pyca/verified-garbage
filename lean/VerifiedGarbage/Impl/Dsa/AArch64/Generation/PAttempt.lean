module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PConstruct
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.CandidateWidth
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Search
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PrimeCall

/-! A p-search iteration constructs, checks width, and tests the candidate natively. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)

def pAttemptArgs : List Instr :=
  [ldh .x3 1, .ldrSp .x4 40, movi .x5 VG.Impl.Dsa.Generation.Layout.shaped,
   .add .x .x4 .x4 .x5, .strSp .x4 0, .strSp .x3 16,
   .ldrSp .x4 24, .strSp .x4 sLab]

def stackStatus (status : Nat) : List Instr := [movi .x3 status, .strSp .x3 152]

def controlBase : List Instr :=
  [.ldrSp .x0 40, movi .x3 VG.Impl.Dsa.Generation.Layout.control, .add .x .x0 .x0 .x3]

def searchReturn : List Instr := controlBase ++ [.ldrSp .x3 152, sth .x3 2]

def pTest (prime : Nat → Prog isa) (pLen : Nat) : Prog isa :=
  .seq (.block candidateWidth) (.ite (.zero .x .x3) (.block (stackStatus 3)) (primeCall prime (8 * pLen)))

def pAttempt (G1 G256 : Hash) (prime : Nat → Prog isa) (pLen qLen : Nat) : Prog isa :=
  .seq (.block pAttemptArgs)
    (.seq (.seq (pConstruct (if qLen = 20 then G1 else G256) pLen qLen) (pTest prime pLen))
      (.block searchReturn))

def primeSearch (G1 G256 : Hash) (prime : Nat → Prog isa) (pLen qLen : Nat) : Prog isa :=
  .seq (.block controlBase)
    (pSearch (pAttempt G1 G256 prime pLen qLen) (32 * pLen) ((8 * pLen - 1) / (8 * qLen) + 1))

end VG.Impl.Dsa.AArch64.Generation
