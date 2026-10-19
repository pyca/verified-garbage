module

public import VerifiedGarbage.Impl.MlKem.AArch64.Optimized

/-! # Optimized composition with independently verified fixed hash helpers -/
@[expose] public section
namespace VG.Impl.MlKem.AArch64.Optimized
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM
open VG.Impl.MlKem.AArch64.Dot VG.Impl.MlKem.AArch64.Noise

def prfCbdUsing (hash : Prog isa) (N off : Nat) (w16 : Bool := false) : Prog isa :=
 .seq (.block [.movz .x .x9 (BitVec.ofNat 16 N) 0,.strb .x9 .x28 (RB+32)])
  (.seq hash (.seq (.block (ptrTo .x0 .x28 PB ++ ptrTo .x1 .x28 off)) (cbdCall w16)))

end VG.Impl.MlKem.AArch64.Optimized
