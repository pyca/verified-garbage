module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentShift
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.RsaKeyGen.MrWindow
import VerifiedGarbage.Proof.RsaKeyGen.X86.SigMask
import VerifiedGarbage.Proof.RsaKeyGen.X86.HalfPassLoop
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # An alignment pass halves exactly when sigma exceeds its public index -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentShift
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.ExponentShift

theorem halfIf_ok {s : State} {base : Addr} {size n marker out j k : Nat} (scratch : Scr s base size)
    (positive : 0 < n) (fit : out + 4 * (n + 1) ≤ size) (markerFit : marker + 8 ≤ size)
    (top : w32 s.mem base (out + 4 * n) = 0) (index : k < 64) (choice : 1 ≤ j ∧ j ≤ 3)
    (value : word s.mem base marker = BitVec.twoPow 64 k) :
    WP isa (halfIf n marker out j) s fun t =>
      Outside base out (4 * n) s.mem t.mem ∧
      val32 t.mem base out n = (if j < VG.Proof.RsaKeyGen.sigOf k then val32 s.mem base out n / 2
        else val32 s.mem base out n) ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  refine WP.seq (WP.mono (SigMask.code_sig scratch markerFit index choice value) fun a ⟨mask, M, K⟩ => ?_)
  refine WP.mono (HalfPass.code_ok (scratch.of_keeps K (by decide)) positive fit (by omega) (Or.inl rfl)
    (by rw [M]; exact top) mask) fun t ⟨O, V, Kt⟩ => ?_
  rw [M] at O V
  exact ⟨O, by simpa only [decide_eq_true_eq] using V, (K.mono (by decide)).widen Kt⟩

end VG.Proof.RsaKeyGen.X86.ExponentShift
