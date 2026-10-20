module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeFrameCTState
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimalityCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeFrameCTState

/-! The retained frame supplies the complete verified primality operation. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MillerRabin.AArch64
open VG.Impl.Dsa.AArch64.Generation

theorem primeFromFrame_ct (M : Mont) (K : Kernel) (candidate len draw checks : Nat)
    (hwidth : PrimeWidths len draw) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0])
      (.block (headerArguments (primeArguments candidate len draw checks))) hc).isSome = true) :
    RelCT isa (Two (PrimeFrameBefore candidate len draw checks))
      (primeFromFrame M.mm K.run candidate len draw checks) (fun _ _ => True) := by
  unfold primeFromFrame
  refine RelCT.seq (two_post (two_taint [.x0] ?_ ht) (fun _ _ h => primeFrame_arguments h)) ?_
  · intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hs.1.good.x0.trans ht.1.good.x0.symm
  · exact two_map PrimeFramePublic.bytes (fun _ _ h => h) (primeBytes_supported_ct M K hwidth)

end VG.Proof.Dsa.AArch64.Generation
