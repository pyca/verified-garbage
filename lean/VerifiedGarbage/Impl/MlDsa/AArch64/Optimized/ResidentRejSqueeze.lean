module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Resident
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt4

/-! Paired SHAKE128 blocks for the matrix sampler. The enclosing sampler
preserves the public ABI. The five resident blocks keep the permutation
inline; the rare sixth block calls `vg_keccak_f1600_x2_sha3`. -/

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64

def squeeze (a b : Reg) : List Instr := Resident.squeeze 21 a b

/-- One permutation of the pair at `p`, by a call, and a rate block of each state
to `a` and `b`, serialized from the states loaded back into registers. -/
def pair (p a b : Reg) : Prog isa :=
  .seq (VG.Impl.Sha3.AArch64.Neon.X2.call true p .x19 Sample.Rej4.oX2)
    (.block (VG.Impl.Sha3.AArch64.Neon.Pair.load p ++ squeeze a b))

/-- Five consecutive rate-168 blocks, with one state load and store. -/
def fiveWith (core : Prog isa) (p a b : Reg) : Prog isa :=
  .seq (.block (VG.Impl.Sha3.AArch64.Neon.Pair.load p))
    (.seq (Resident.streamWith core 21 5 a b)
      (.block (VG.Impl.Sha3.AArch64.Neon.Pair.store p)))

def five (p a b : Reg) : Prog isa := fiveWith Resident.permute p a b
end VG.Impl.MlDsa.AArch64.Optimized.ResidentRej
