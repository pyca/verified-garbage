module

public import VerifiedGarbage.Proof.Dsa.X86.PowABI
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Dsa.X86.PowTiming
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Dsa.X86.PowBody
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.ModPowContract

/-! # Correctness and secrecy of callable IA-32 exponentiation -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Pow
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Impl.Dsa.X86.Pow

theorem scratch_fits {n size : Nat} (h : contextBytes n ≤ size) :
    ∀ r ∈ scratch n, r.1 + r.2 ≤ size := by
  intro r hr
  simp only [scratch, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp only [contextBytes, slot, stride] at * <;> omega

end VG.Proof.Dsa.X86.Pow
