module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeFrameCTState
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimalityCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeFrameCTState
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ArgumentBlocksCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ArgumentBlocksCT

/-! # The native frame supplies every argument of the verified primality call -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Impl.Dsa.X86_64.Generation

theorem primeFromFrame_ct (M : Mont) (K : Kernel) (candidate len draw checks : Nat)
    (hwidth : PrimeWidths len draw) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .rsp])
      (.block (headerArguments (primeArguments candidate len draw checks))) hc).isSome = true) :
    RelCT isa (Two (PrimeFrameBefore candidate len draw checks))
      (primeFromFrame M.mm K.run candidate len draw checks) (fun _ _ => True) := by
  unfold primeFromFrame
  refine RelCT.seq (two_post
    (two_map (fun p : PrimeFramePublic => (⟨p.bytes.call.draw.prime.B, p.bytes.call.draw.prime.sp⟩ : ArgumentPointers))
      (fun _ _ h => by obtain ⟨mi, hg⟩ := h.1.good; exact ⟨hg.rdi, h.1.stack⟩)
      (primeArguments_ct candidate len draw checks ht))
    (fun _ _ h => primeFrame_arguments h)) ?_
  exact two_map PrimeFramePublic.bytes (fun _ _ h => h) (primeBytes_supported_ct M K hwidth)

end VG.Proof.Dsa.X86_64.Generation
