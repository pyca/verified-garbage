module

public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw
public import VerifiedGarbage.Impl.Rsa.X86.RecoverRt
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.TCB.X86.Target

import VerifiedGarbage.Proof.Rsa.X86.RvOperationTiming
import VerifiedGarbage.Proof.Rsa.X86.RvSatisfiable
import VerifiedGarbage.Proof.Rsa.X86.RvABI
import VerifiedGarbage.Proof.Rsa.X86.RvResult
import VerifiedGarbage.Proof.Rsa.X86.RvReturn
import VerifiedGarbage.Proof.Rsa.X86.RvInstalled
import VerifiedGarbage.Proof.Rsa.X86.RvResources
import VerifiedGarbage.Proof.Bignum.X86.PublicReturn
import VerifiedGarbage.Proof.Bignum.X86.PublicSave
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Rsa.X86.RvBody
/-! # Complete i686 certificate for RSA prime recovery -/

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/RvCorrect.lean`, which only this module imported.
section

/-! # Functional correctness and cdecl preservation of i686 RSA prime recovery -/

section
variable [rsaBatchLaw : VG.Proof.Rsa.X86.BatchLaw]
include rsaBatchLaw
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum hiding off Outside
open VG.Proof.Bignum.X86 VG.Impl.Bignum.X86
open VG.Impl.Rsa.X86.Recover

theorem operation_ok {s : State} (a : ABI s) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.code s fun t => Written (caller s) s.mem t ∧ abiPreserved s t := by
  have low : 16 ≤ (caller s).Z := by have := a.used; omega
  have high : (caller s).Z ≤ 2 ^ 64 := by have := a.scratchBound; omega
  unfold VG.Impl.Rsa.X86.RecoverRt.code
  refine WP.seq (WP.mono (installed_ok a) fun u ⟨inputs, saved, k, o⟩ => ?_)
  refine WP.seq (WP.mono (body_ok inputs a.lengths_ok) fun v ⟨iv, written, frame, kv⟩ => ?_)
  have saveV := bodyFrame_saved inputs frame saved
  have whole : Frame (caller s).writes s.mem v.mem := by
    have start := outside_frame o (by omega)
    simp only [off, BitVec.add_zero] at start
    exact (start.mono (by simp [CallGeometry.writes])).trans (bodyFrame_full low frame)
  have ret : v.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32 :=
    whole.readW (Region.contains_self _ 4) a.retApartW (by decide)
  refine WP.mono (entryRestore_ok iv.ws.workspace low saveV) fun t restored => ?_
  refine ⟨?_, publicRestored_abi restored ((kv.1 _ (by decide)).trans (k.1 _ (by decide))) ret⟩
  unfold Written at written ⊢
  rw [calculated_entry a o] at written
  rw [restored.mem, restored.other .eax (by decide)]
  exact written

theorem correct (s : State) (h : (Spec.Rsa.recoverPrimesContract abi 96).pre s) :
    ∃ trace t, Exec isa VG.Impl.Rsa.X86.RecoverRt.code s trace t ∧ abiPreserved s t ∧
      (Spec.Rsa.recoverPrimesContract abi 96).post s t := by
  have a := abi_of h
  obtain ⟨trace, t, run, written, preserved⟩ := operation_ok a
  refine ⟨trace, t, run, preserved, ?_⟩
  sig_post [Spec.Rsa.recoverPrimesContract, Spec.Rsa.recoverPrimesSig, abi, argSlots, argVal, argBytes]
  rw [BitVec.setWidth_append_eq_right]
  unfold Written outputBuffers calculated inputBytes CallGeometry.buffer caller at written
  change Spec.Rsa.writtenAll t.mem
    [(VG.Proof.Dsa.X86.argumentPointer s 0, (arg s 1).toNat),
      (VG.Proof.Dsa.X86.argumentPointer s 2, (arg s 3).toNat)] (t.gpr .eax) _ at written
  rw [a.pLen, a.qLen] at written
  exact written

end VG.Proof.Rsa.X86.Recover
end

end

@[expose] public section
variable [rsaBatchLaw : VG.Proof.Rsa.X86.BatchLaw]
include rsaBatchLaw
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Impl.Rsa.X86.Recover

theorem verified : Verified target VG.Impl.Rsa.X86.RecoverRt.code (Spec.Rsa.recoverPrimesContract abi 96) :=
  ⟨correct, constantTime, satisfiable⟩

end VG.Proof.Rsa.X86.Recover
