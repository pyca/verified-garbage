module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentRejFour
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt4

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64

/-- SHA3 uses the resident adaptive sampler; the portable path is unchanged. -/
def selected (sha3 : Bool) : Prog isa :=
  if sha3 then Four.code else Sample.Rej4.rejNTT4With false

end VG.Impl.MlDsa.AArch64.Optimized.ResidentRej
