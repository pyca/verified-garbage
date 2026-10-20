module

import VerifiedGarbage.Proof.Framework.X86_64.Avx512
public import VerifiedGarbage.TCB.X86_64.State
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Impl.Gcm.X86_64.Pclmul
import VerifiedGarbage.Proof.Aes.X86_64.VaesZ.Rounds
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec
import VerifiedGarbage.Proof.Gcm.X86_64.Rev
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Aes
import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Gh

/-!
# The blocks after the last group, through a mask

What the masked loads of the blocks after the last group share
(`RemGXor.lean`, `RemGHash.lean`): a masked load's result in a register
(`setZv`, `zlane_setZv`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod)
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Proof.Gcm.X86_64.StitchZ (restZ ldAcc ldAcc_ok)
open VG.Proof.Aes.X86_64.VaesZ (zmm_lane)
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq)
open VG.Spec.Gcm (Block blockAt)

/-- The lanes of a 512-bit value written to a register. -/
theorem zlane_setZv (s : State) (d : XReg) (v : BitVec 512) {l : Nat} (hl : l < 4) :
    (s.setZ d (v.extractLsb' 0 128) (v.extractLsb' 128 128) (v.extractLsb' 256 128) (v.extractLsb' 384 128)).zlane d l =
      v.extractLsb' (128 * l) 128 := by
  rw [State.zlane_setZ _ _ _ _ _ _ _ hl]
  simp only [ite_true]
  exact pick4_lanes (fun i => v.extractLsb' (128 * i) 128) hl

/-- A masked load's result, in a register. -/
abbrev setZv (s : State) (d : XReg) (v : BitVec 512) : State :=
  s.setZ d (v.extractLsb' 0 128) (v.extractLsb' 128 128) (v.extractLsb' 256 128) (v.extractLsb' 384 128)

end VG.Proof.Gcm.X86_64.StitchZH
