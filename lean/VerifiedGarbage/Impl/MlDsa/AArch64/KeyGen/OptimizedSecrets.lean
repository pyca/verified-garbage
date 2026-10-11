module

public import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.Prims
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.BoundedFour

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call
open VG.Impl.MlKem.AArch64 (copy32)

/-- Two word-wise copies retain the measured unaligned 66-byte seed stride. -/
def secretSeedCopy (k : Nat) : List Instr :=
 lea .x10 .x28 (1408+66*k) ++ copy32 .x28 oSB .x10 0 ++
 copy32 .x28 (oSB+32) .x10 32

def secretSeedSlot (r k : Nat) : List Instr :=
 secretSeedCopy k ++
 setB (sc (1408+66*k+64)) (r+k) ++ setB (sc (1408+66*k+65)) 0

def boundedFourSymbol (c : Impl.Sha3.AArch64.Callee) (η : Nat) : String :=
 "vg_mldsa_rej_bounded_poly4_eta"++toString η++c.suffix

def secretGroup (c : Impl.Sha3.AArch64.Callee) (p : Params) (g : Nat) : Prog isa :=
 .seq (.block ((List.range 4).flatMap (secretSeedSlot (4*g)))) <|
 .seq (callAt (boundedFourSymbol c p.η)
   (VG.Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler c.pairedSha3 true p.η)
   [(.x0,.ptr (sc 1408)),(.x1,.ptr (sP p (4*g))),(.x2,.ptr (sc (oR4 p)))]) (.block and24)

/-- The unused fourth tail lane duplicates the first tail seed, so its failure
and rejection transcript add no information or failure case. -/
def secretTailSlot (r k : Nat) : List Instr :=
 secretSeedCopy k ++
 setB (sc (1408+66*k+64)) (r+if k=3 then 0 else k) ++ setB (sc (1408+66*k+65)) 0

def secretTailThree (c : Impl.Sha3.AArch64.Callee) (p : Params) : Prog isa :=
 let r:=4*((p.ℓ+p.k)/4)
 .seq (.block ((List.range 4).flatMap (secretTailSlot r))) <|
 .seq (callAt (boundedFourSymbol c p.η)
   (VG.Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler c.pairedSha3 true p.η)
   [(.x0,.ptr (sc 1408)),(.x1,.ptr (sP p r)),(.x2,.ptr (sc (oR4 p)))]) (.block and24)


/-- All three standard parameter sets end with either zero or three lanes. -/
def secretsWith (c : Impl.Sha3.AArch64.Callee) (p : Params) : Prog isa :=
 .seq (seqR (secretGroup c p) 0 ((p.ℓ+p.k)/4))
   (if (p.ℓ+p.k)%4=3 then secretTailThree c p else .block [])

end VG.Impl.MlDsa.AArch64.KeyGen.Optimized
