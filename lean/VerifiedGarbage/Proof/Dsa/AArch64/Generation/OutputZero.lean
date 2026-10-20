module

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OutputArgs
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ZeroBytes
public import VerifiedGarbage.Proof.RsaOaep.AArch64.DecOut
public import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Output
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! Every failed search clears the complete output and returns zero. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64

theorem outputZero_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} {len : Nat}
    (L : Lay s F S) (R : Rep s.mem F S V W) (hlen : W 7 = BitVec.ofNat 64 len)
    (hl : 0 < len ∧ len ≤ 1024) (hw : (⟨W 6, len⟩ : Region) ∈ s.wr)
    (_hb : (W 6).toNat + len ≤ 2 ^ 64) (_ha : Apart F S ⟨W 6, len⟩) :
    WP isa Impl.Dsa.AArch64.Generation.outputZero s fun t =>
      t.gpr .x0 = 0 ∧ Spec.Rsa.bytesAt t.mem (W 6) len = List.replicate len 0 ∧
      Frame [⟨F, frameBytes⟩, ⟨W 6, len⟩] s.mem t.mem ∧ Keep (.x0 :: mmRegs) s t := by
  unfold Impl.Dsa.AArch64.Generation.outputZero
  refine WP.seq (WP.mono (zeroArgs_ok L R) fun u ⟨Lu, Ru, fu, ku⟩ => ?_)
  refine WP.seq (WP.mono (zeroOut_bytes_ok (op := W 6) (k := len) Lu Ru (by simp [upd]) (by simpa [upd] using hlen)
    hl.1 (by omega) (fun i hi => by
      rw [ku.wr]
      exact ⟨⟨W 6, len⟩, hw, Offset.contains_base _ (by omega) (by omega)⟩))
    fun v ⟨zeros, fv, kv⟩ => ?_)
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = 0 ∧ t.mem = v.mem)
    (by brun) rfl rfl rfl) fun t ⟨⟨hr, hm⟩, kt⟩ => ?_
  refine ⟨hr, ?_, ?_, ((ku.trans kv).trans kt).mono (by decide)⟩
  · apply List.ext_getElem
    · simp only [VG.Proof.Bignum.bytesAt_length, List.length_replicate]
    · intro i hi hi'
      have hil : i < len := by simpa only [VG.Proof.Bignum.bytesAt_length] using hi
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate, hm]
      exact zeros i hil
  · have ff : Frame [⟨W 6, len⟩] u.mem t.mem := by
      intro a ha
      rw [hm]
      apply fv a
      intro i hi he
      apply ha ⟨W 6, len⟩ (by simp)
      rw [he]
      exact Offset.contains_base _ (by omega) (by omega)
    exact (fu.mono (by simp)).trans (ff.mono (by simp))

end VG.Proof.Dsa.AArch64.Generation
