import VerifiedGarbage.Impl.Sha3.AArch64.Neon.Pair

/-! Register-resident paired SHAKE blocks. These are inline program fragments;
there is no custom calling convention or separately emitted resident helper. -/
namespace VG.Impl.MlDsa.AArch64.Optimized.Resident
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

/-- Both 64-bit lanes of v0..v24 undergo the same Keccak permutation. -/
def permute : Prog isa := .block VG.Impl.Sha3.AArch64.Sha3.Vector.rounds

/-- Serialize two consecutive rate words from each lane. -/
def squeezePair (a b : Reg) (i : Nat) : List Instr :=
  [.vop (.perm .trn1 .d2 .v26 (vreg (2*i)) (vreg (2*i+1))),
   .vop (.perm .trn2 .d2 .v27 (vreg (2*i)) (vreg (2*i+1))),
   .strq .v26 a (16*i), .strq .v27 b (16*i)]

/-- The final odd rate word, used for both SHAKE128 and SHAKE256. -/
def squeezeLast (a b : Reg) (i : Nat) : List Instr :=
  [.umov .x .x6 (vreg i) 0, .umov .x .x7 (vreg i) 1,
   .str .x .x6 a (8*i), .str .x .x7 b (8*i)]

/-- A public number of rate words; production callers use 17 or 21. -/
def squeeze (words : Nat) (a b : Reg) : List Instr :=
  (List.range (words/2)).flatMap (squeezePair a b) ++
    if words%2=1 then squeezeLast a b (words-1) else []

/-- Keep both states in registers for all blocks. The public loop counter is
x28; output pointers must be distinct from x6, x7, x16 and x28. -/
def streamWith (core : Prog isa) (words blocks : Nat) (a b : Reg) : Prog isa :=
  if blocks=0 then .block [] else
  .seq (.block [.movz .x .x28 (BitVec.ofNat 16 blocks) 0]) <|
    .loop (.seq core (.block (squeeze words a b ++
      ([.addImm .x a a (8*words), .addImm .x b b (8*words),
       .subImm .x .x28 .x28 1] : List Instr)))) (.nonzero .x .x28)

/-- The original schedule remains the default. -/
def stream (words blocks : Nat) (a b : Reg) : Prog isa := streamWith permute words blocks a b

/-- Load and store the packed states once around five SHAKE256 blocks. -/
def maskPairWith (core : Prog isa) (p a b : Reg) : Prog isa :=
  .seq (.block (VG.Impl.Sha3.AArch64.Neon.Pair.load p)) <|
  .seq (streamWith core 17 5 a b) (.block (VG.Impl.Sha3.AArch64.Neon.Pair.store p))
def maskPair (p a b : Reg) : Prog isa := maskPairWith permute p a b
end VG.Impl.MlDsa.AArch64.Optimized.Resident
