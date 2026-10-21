module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateWord
public import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.Proof.RsaKeyGen.Bits32
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateBits
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # The two native writes construct exactly the specified RSA candidate -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateBits
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.CandidateBits

theorem code_ok {s : State} {base : Addr} {size w out : Nat}
    (scratch : Scr s base size) (positive : 0 < w) (fit : out + 8 * w ≤ size) :
    WP isa (.block (code w out)) s fun t =>
      val32 t.mem base out (2 * w) = Spec.RsaKeyGen.candidate (64 * w) (val32 s.mem base out (2 * w)) ∧
      Outside base out (8 * w) s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold code
  refine WP.block_append (WP.mono (forceWord_ok 1 scratch (by omega)) fun a ⟨low, Oa, Ka⟩ => ?_)
  refine WP.mono (forceWord_ok 0xc0000000 (scratch.of_keeps Ka (by decide)) (by omega))
    fun t ⟨top, Ot, Kt⟩ => ?_
  have lowSame : w32 t.mem base out = w32 a.mem base out := Ot.w32 (by omega) (by have := scratch.nowrap; omega)
  have topSame : w32 a.mem base (out + 8 * w - 4) = w32 s.mem base (out + 8 * w - 4) :=
    Oa.w32 (by omega) (by have := scratch.nowrap; omega)
  refine ⟨?_, (Oa.mono (by omega) (by omega)).trans (Ot.mono (by omega) (by omega)), Ka.trans Kt⟩
  rw [show 64 * w = 32 * (2 * w) by omega]
  apply VG.Proof.RsaKeyGen.val32_candidate (by omega)
  · rw [lowSame, low]
    rfl
  · rw [show out + 4 * (2 * w - 1) = out + 8 * w - 4 by omega, top, topSame]
    rfl
  · intro j first last
    exact (Ot.w32 (by omega) (by have := scratch.nowrap; omega)).trans
      (Oa.w32 (by omega) (by have := scratch.nowrap; omega))

end VG.Proof.RsaKeyGen.X86.CandidateBits
