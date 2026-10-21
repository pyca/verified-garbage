module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.MontInverse
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.X86.Inverse
import VerifiedGarbage.Proof.RsaKeyGen.X86.InverseSetup
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # The compact prepared kernel receives the reviewed full 64-bit inverse -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MontInverse
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.MontInverse

theorem code_ok {s : State} {base : Addr} {size modulus inverse : Nat} (scratch : Scr s base size)
    (modFit : modulus + 8 ≤ size) (invFit : inverse + 8 ≤ size)
    (apart : inverse + 8 ≤ modulus ∨ modulus + 8 ≤ inverse) (odd : w32 s.mem base modulus % 2 = 1) :
    WP isa (code modulus inverse) s fun t =>
      ((word t.mem base modulus).toNat * (word t.mem base inverse).toNat + 1) % 2 ^ 64 = 0 ∧
      Outside base inverse 8 s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  refine WP.seq (WP.mono (VG.Proof.Mont.X86.Dynamic.setupInverse_ok scratch (by omega) (by omega) odd)
    fun a ⟨inverseA, Oa, Ka⟩ => ?_)
  have low : (w32 a.mem base modulus * w32 a.mem base inverse + 1) % 2 ^ 32 = 0 := by
    rw [Oa.w32 (by omega) (by have := scratch.nowrap; omega)]
    exact inverseA
  refine WP.mono (InverseLift.setup_ok (scratch.of_keeps Ka (by decide)) modFit invFit low)
    fun t ⟨inverseT, Ot, Kt⟩ => ?_
  refine ⟨?_, (Oa.mono (by omega) (by omega)).trans (Ot.mono (by omega) (by omega)), ?_⟩
  · rw [word_eq_w32, word_eq_w32,
      Ot.w32 (d := modulus) (by omega) (by have := scratch.nowrap; omega),
      Ot.w32 (d := modulus + 4) (by omega) (by have := scratch.nowrap; omega),
      Ot.w32 (d := inverse) (by omega) (by have := scratch.nowrap; omega)]
    exact inverseT
  · exact (Ka.mono (by decide)).trans Kt

end VG.Proof.RsaKeyGen.X86.MontInverse
