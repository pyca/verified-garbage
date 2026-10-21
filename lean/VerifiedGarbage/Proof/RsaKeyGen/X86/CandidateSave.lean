module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateSave
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.X86.DivCopy
import VerifiedGarbage.Proof.RsaKeyGen.X86.LowWord
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Saving and restoring an odd candidate changes only the destination -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateSave
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.CandidateSave

theorem save_ok {s : State} {base : Addr} {size n src dst : Nat} (scratch : Scr s base size)
    (positive : 0 < n) (srcFit : src + 4 * n ≤ size) (dstFit : dst + 4 * n ≤ size)
    (sep : dst = src ∨ dst + 4 * n ≤ src ∨ src + 4 * n ≤ dst)
    (odd : val32 s.mem base src n % 2 = 1) :
    WP isa (save n src dst) s fun t =>
      val32 t.mem base dst n + 1 = val32 s.mem base src n ∧
      Outside base dst (4 * n) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.Div.copyWords_ok scratch positive srcFit dstFit sep)
    fun a ⟨Oa, value, Ka⟩ => ?_)
  have low : 0 < w32 a.mem base dst := LowWord.odd_low positive (by rw [value]; exact odd)
  refine WP.mono (LowWord.decrement_ok (scratch.of_keeps Ka (by decide)) positive dstFit low)
    fun t ⟨V, Ot, Kt⟩ => ?_
  rw [value] at V
  exact ⟨V, Oa.trans (Ot.mono (by omega) (by omega)), Ka.widen Kt⟩

theorem restore_ok {s : State} {base : Addr} {size n src dst : Nat} (scratch : Scr s base size)
    (positive : 0 < n) (srcFit : src + 4 * n ≤ size) (dstFit : dst + 4 * n ≤ size)
    (sep : dst = src ∨ dst + 4 * n ≤ src ∨ src + 4 * n ≤ dst)
    (even : val32 s.mem base src n % 2 = 0) :
    WP isa (restore n src dst) s fun t =>
      val32 t.mem base dst n = val32 s.mem base src n + 1 ∧
      Outside base dst (4 * n) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.Div.copyWords_ok scratch positive srcFit dstFit sep)
    fun a ⟨Oa, value, Ka⟩ => ?_)
  have low : w32 a.mem base dst + 1 < 2 ^ 32 := LowWord.even_low positive (by rw [value]; exact even)
  refine WP.mono (LowWord.increment_ok (scratch.of_keeps Ka (by decide)) positive dstFit low)
    fun t ⟨V, Ot, Kt⟩ => ?_
  rw [value] at V
  exact ⟨V, Oa.trans (Ot.mono (by omega) (by omega)), Ka.widen Kt⟩

end VG.Proof.RsaKeyGen.X86.CandidateSave
