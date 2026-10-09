import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Resident

/-! Paired SHAKE128 blocks for the matrix sampler. The enclosing sampler
preserves the public ABI; the permutation remains inline. -/
namespace VG.Impl.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64

def squeeze (a b : Reg) : List Instr := Resident.squeeze 21 a b

def pair (p a b : Reg) : Prog isa :=
  .seq (.block (VG.Impl.Sha3.AArch64.Neon.Pair.load p))
    (.seq Resident.permute
      (.block (VG.Impl.Sha3.AArch64.Neon.Pair.store p ++ squeeze a b)))

/-- Five consecutive rate-168 blocks, with one state load and store. -/
def fiveWith (core : Prog isa) (p a b : Reg) : Prog isa :=
  .seq (.block (VG.Impl.Sha3.AArch64.Neon.Pair.load p))
    (.seq (Resident.streamWith core 21 5 a b)
      (.block (VG.Impl.Sha3.AArch64.Neon.Pair.store p)))

def five (p a b : Reg) : Prog isa := fiveWith Resident.permute p a b
end VG.Impl.MlDsa.AArch64.Optimized.ResidentRej
